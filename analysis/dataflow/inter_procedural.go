// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Package dataflow contains abstractions for reasoning about data flow within programs.
package dataflow

import (
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/awslabs/ar-go-tools/analysis/config"
	"github.com/awslabs/ar-go-tools/analysis/lang"
	"github.com/awslabs/ar-go-tools/analysis/summaries"
	"github.com/awslabs/ar-go-tools/internal/formatutil"
	"github.com/awslabs/ar-go-tools/internal/funcutil"
	"golang.org/x/tools/go/ssa"
)

// Visitor represents a visitor that runs an inter-procedural analysis from entrypoint.
type Visitor interface {
	Visit(s *State, entrypoint NodeWithTrace)
}

// NodePair represents a pair of graph nodes for Case 3 subspec generation
type NodePair struct {
	Source GraphNode
	Target GraphNode
}

// SpecificEdge represents a specific edge to be added to a callee's summary
type SpecificEdge struct {
	Source   GraphNode // Source node in the callee
	Target   GraphNode // Target node in the callee
	EdgeInfo EdgeInfo  // Edge information (conditions, paths, etc.)
}

// CalleeEdgeOption represents a potential specific edge for a callee function
type CalleeEdgeOption struct {
	Callee          *ssa.Function // The callee function
	Edge            SpecificEdge  // The specific edge to add
	ViolationsFixed []NodePair    // Which violations this edge fixes in the caller
	FixCount        int           // Number of violations this edge fixes
}

// SetCoverState tracks the state of the edge-based set-cover algorithm
type SetCoverState struct {
	Universe      []NodePair                       // All missing edges (violations) in the caller
	Uncovered     map[NodePair]bool                // Currently uncovered violations
	EdgeOptions   []*CalleeEdgeOption              // Available edge options for each callee
	SelectedEdges map[*ssa.Function][]SpecificEdge // Selected edges: callee -> specific edges to add

	// TEMPORARY: Legacy compatibility fields for compilation
	CalleeOptions   []*CalleeSubspecOption   // DEPRECATED: Use EdgeOptions instead
	SelectedCallees map[*ssa.Function]string // DEPRECATED: Use SelectedEdges instead
}

// Legacy type for backward compatibility (to be removed)
type CalleeSubspecOption struct {
	Callee          *ssa.Function
	SubspecType     string // "full", "empty", "identity" - DEPRECATED
	ViolationsFixed []NodePair
	FixCount        int
}

// RecursiveCheckResults tracks the results of recursively checking all callees
type RecursiveCheckResults struct {
	AllCalleesSound    bool   // True if all callees passed recursive checking
	CalleeCount        int    // Total number of callees checked
	FirstFailureReason string // Reason for first failure (if any)
}

// SoundnessCheckStats tracks statistics about soundness checking results
type SoundnessCheckStats struct {
	TotalSummaries   int            // Total number of summaries checked
	SoundCount       int            // Number of sound summaries
	UnsoundCount     int            // Number of unsound summaries
	StepDistribution map[string]int // Distribution of which step proved soundness (step name -> count)
}

// InterProceduralFlowGraph represents an inter-procedural data flow graph.
type InterProceduralFlowGraph struct {
	// ForwardEdges represents edges between nodes belonging to different sub-graphs (inter-procedural version of
	// (GraphNode).Out)
	ForwardEdges map[GraphNode]map[GraphNode]bool

	// BackwardEdges represents backward edges between nodes belonging to different sub-graphs (inter-procedural
	// version of (GraphNode).In)
	BackwardEdges map[GraphNode]map[GraphNode]bool

	// Summaries map the functions in the SSA to their summaries
	Summaries map[*ssa.Function]*SummaryGraph

	// AnalyzerState is a pointer to the analyzer state from which the dataflow graph is computed
	AnalyzerState *State

	// built indicates whether this graph has been built
	// this should only be set to true by BuildGraph() and be false by default
	built bool

	// Globals are edges between global nodes and the nodes that access the global
	Globals map[*GlobalNode]map[*AccessGlobalNode]bool
}

// NewInterProceduralFlowGraph returns a new non-built cross function flow graph.
func NewInterProceduralFlowGraph(summaries map[*ssa.Function]*SummaryGraph,
	state *State) InterProceduralFlowGraph {

	return InterProceduralFlowGraph{
		Summaries:     summaries,
		AnalyzerState: state,
		built:         false,
		ForwardEdges:  make(map[GraphNode]map[GraphNode]bool),
		BackwardEdges: make(map[GraphNode]map[GraphNode]bool),
	}
}

// IsBuilt returns true iff the cross function graph has been built, i.e. the summaries have been linked together.
func (g *InterProceduralFlowGraph) IsBuilt() bool {
	return g.built
}

// Print prints each of the function summaries in the graph.
func (g *InterProceduralFlowGraph) Print(w io.Writer) {
	fmt.Fprintf(w, "digraph program {\n")
	fmt.Fprintf(w, "\tcompound=true;\n") // visually group subgraphs together
	for _, summary := range g.Summaries {
		summary.Print(false, w)
	}
	const forwardColor = "\"#1cf4a3\""  // green
	const backwardColor = "\"#dc143c\"" // red
	const fmtColorEdge = "%s -> %s [color=%s];\n"
	for src, dsts := range g.ForwardEdges {
		for dst := range dsts {
			fmt.Fprintf(w, fmtColorEdge, escapeString(src.String()), escapeString(dst.String()), forwardColor)
		}
	}
	for dst, srcs := range g.BackwardEdges {
		for src := range srcs {
			fmt.Fprintf(w, fmtColorEdge, escapeString(dst.String()), escapeString(src.String()), backwardColor)
		}
	}

	for global, accesses := range g.Globals {
		for access := range accesses {
			// write is an edge from global <- access, read is an edge from global -> access
			if access.IsWrite {
				fmt.Fprintf(w, fmtColorEdge, escapeString(access.String()), escapeString(global.String()), forwardColor)
				fmt.Fprintf(w, fmtColorEdge, escapeString(global.String()), escapeString(access.String()), backwardColor)
			} else {
				fmt.Fprintf(w, fmtColorEdge, escapeString(global.String()), escapeString(access.String()), forwardColor)
				fmt.Fprintf(w, fmtColorEdge, escapeString(access.String()), escapeString(global.String()), backwardColor)
			}
		}
	}

	fmt.Fprintf(w, "}\n")
}

// InsertSummaries inserts all the summaries from g2 in g
func (g *InterProceduralFlowGraph) InsertSummaries(g2 InterProceduralFlowGraph) {
	for f, sum := range g2.Summaries {
		g.Summaries[f] = sum
	}
}

// BuildGraph builds the cross function flow graph by connecting summaries together
//
//gocyclo:ignore
func (g *InterProceduralFlowGraph) BuildGraph() []*SummaryGraph {
	c := g.AnalyzerState
	logger := c.Logger

	logger.Debugf("Building inter-procedural flow graph...")

	// Open a file to output summaries
	summariesFile := openSummaries(c)
	if summariesFile != nil {
		defer summariesFile.Close()
	}

	// Build the inter-procedural data flow graph:
	nameAliases := map[string]*ssa.Function{}
	// STEP 1: build a map from full function names to summaries
	for summarized := range g.Summaries {
		// sometimes a "thunk" function will be the same as a normal function,
		// just with a different name ending in $thunk and the same position
		nameAliases[summarized.String()] = summarized
	}

	// Collect external summaries to check after loading to avoid recursive memory pressure
	externalSummariesToCheck := make(map[*ssa.Function]*SummaryGraph)

	// STEP 2: Enforce dataflow contracts
	for _, summary := range g.Summaries {
		if summary == nil {
			continue
		}
		for _, callNodes := range summary.Callees {
			for _, node := range callNodes {
				if node.Callee() != nil && node.CalleeSummary == nil {
					externalContractSummary := g.AnalyzerState.LoadExternalContractSummary(node)
					if externalContractSummary != nil {
						logger.Debugf("Loaded %s from external contracts.\n",
							formatutil.SanitizeRepr(node.Callee()))

						// Link the summary and defer soundness checking
						g.Summaries[node.Callee()] = externalContractSummary
						node.CalleeSummary = externalContractSummary
						if x := externalContractSummary.Callsites[node.CallSite()]; x == nil {
							externalContractSummary.Callsites[node.CallSite()] = node
						}
						externalSummariesToCheck[node.Callee()] = externalContractSummary
					}
				}
			}
		}
	}

	// After loading external summaries everywhere, check them one by one
	var unsoundSummaries []*SummaryGraph
	for fn, extSum := range externalSummariesToCheck {
		isSound, reason, needsDeeperCheck := g.CheckSummarySoundness(fn, extSum)
		if !isSound {
			logger.Warnf("External summary for %s is not sound: %s",
				formatutil.SanitizeRepr(fn), reason)
			unsoundSummaries = append(unsoundSummaries, extSum)
		} else {
			logger.Debugf("External summary for %s is sound: %s",
				formatutil.SanitizeRepr(fn), reason)
			if len(needsDeeperCheck) > 0 {
				logger.Debugf("Summary for %s requires deeper analysis of %d callees",
					formatutil.SanitizeRepr(fn), len(needsDeeperCheck))
			}
		}
	}

	// Writes the summaries to file if the option is set
	if summariesFile != nil {
		// Read-only operation on summaries
		go func() {
			for _, summary := range g.Summaries {
				if summary == nil {
					continue
				}
				_, _ = summariesFile.WriteString(fmt.Sprintf("%s:\n", summary.Parent.String()))
				summary.Print(false, summariesFile)
				_, _ = summariesFile.WriteString("\n")
			}
		}()
	}

	// STEP 3: link all the summaries together
	for _, summary := range g.Summaries {
		if summary == nil {
			continue
		}
		// Interprocedural edges: callers to callees
		for _, callNodes := range summary.Callees {
			for _, node := range callNodes {
				if node.Callee() != nil && node.CalleeSummary == nil &&
					g.AnalyzerState.IsReachableFunction(node.Callee()) {
					node.CalleeSummary = g.resolveCalleeSummary(node, nameAliases)
				}
			}
		}

		// Interprocedural edges: closure creation to anonymous function
		for _, closureNode := range summary.CreatedClosures {
			if closureNode.instr != nil {
				closureSummary := g.findClosureSummary(closureNode.instr)
				// Add edge from created closure summary to creator
				if closureSummary != nil {
					closureSummary.ReferringMakeClosures[closureNode.instr] = closureNode
				}
				closureNode.ClosureSummary = closureSummary // nil is safe
			}
		}

		// Interprocedural edges: bound variable to capturing anonymous function
		for _, boundLabelNodeGroup := range summary.BoundLabelNodes {
			for _, boundLabelNode := range boundLabelNodeGroup {
				if boundLabelNode.targetInfo.MakeClosure != nil {
					closureSummary := g.findClosureSummary(boundLabelNode.targetInfo.MakeClosure)
					boundLabelNode.targetAnon = closureSummary // nil is safe
				}
			}
		}
	}
	// Change the built flag to true
	g.built = true
	return unsoundSummaries
}

// Sync synchronizes inter-procedural information in the graph. This is useful if updating a summary generates nodes
// that may require edges to nodes in other functions.
//
//gocyclo:ignore
func (g *InterProceduralFlowGraph) Sync() {
	if !g.built {
		g.AnalyzerState.Logger.Warnf("Attempting to sync an inter-procedural graph that has not been built.")
	}
	for _, summary := range g.Summaries {
		if summary == nil {
			continue
		}
		// Interprocedural edges: closure creation to anonymous function
		for _, closureNode := range summary.CreatedClosures {
			if closureNode.instr != nil {
				closureSummary := g.findClosureSummary(closureNode.instr)
				// Add edge from created closure summary to creator
				if closureSummary != nil {
					closureSummary.ReferringMakeClosures[closureNode.instr] = closureNode
				}
				closureNode.ClosureSummary = closureSummary // nil is safe
			}
		}

		// Interprocedural edges: bound variable to capturing anonymous function
		for _, boundLabelNodeGroup := range summary.BoundLabelNodes {
			for _, boundLabelNode := range boundLabelNodeGroup {
				if boundLabelNode.targetInfo.MakeClosure != nil {
					closureSummary := g.findClosureSummary(boundLabelNode.targetInfo.MakeClosure)
					boundLabelNode.targetAnon = closureSummary // nil is safe
				}
			}
		}
	}
}

// ScanningSpec specifies what nodes should be scanned. The caller can use both the ssa node and the graph node
// predicates to identify graph nodes that are the entry points of the analysis.
type ScanningSpec struct {
	// IsEntryPointSsa identifies graph nodes by the ssa node they represent.
	// It returns the code identifier from the config file if there was a match.
	IsEntryPointSsa func(node ssa.Node) (config.CodeIdentifier, bool)

	// IsEntryPointGraph identifies graph nodes directly as entry points.
	// It returns the code identifier from the config file if there was a match.
	IsEntryPointGraph func(node GraphNode) (config.CodeIdentifier, bool)

	// MarkCallArgsLikeCall specifies whether call arguments should be considered entry points when the call is
	// an entry point.
	MarkCallArgsLikeCall bool

	// ScanCallArgsOnly specifies whether only call arguments should be
	// considered entry points - not the call itself.
	ScanCallArgsOnly bool
}

// BuildAndRunVisitor runs the pass on the inter-procedural flow graph. First, it calls the BuildGraph function to
// build the inter-procedural dataflow graph. Then, it looks for every entry point designated by the isEntryPoint
// predicate to RunIntraProcedural the visitor on those points (using the [*InterProceduralFlowGraph.RunVisitorOnEntryPoints]
// function).
//
// Most of the logic of the analysis will be in the visitor's implementation by the client. This function is mostly
// a driver that sequences the analyses in the right order with small checks.
//
// This function does nothing if there are no summaries
// (i.e. `len(g.summaries) == 0`)
// or if `cfg.SkipInterprocedural` is set to true.
func (g *InterProceduralFlowGraph) BuildAndRunVisitor(c *State, visitor Visitor, spec ScanningSpec) {
	// Skip the pass if user configuration demands it
	if !c.Config.SummarizeOnDemand && len(g.Summaries) == 0 {
		c.Logger.Infof("Skipping inter-procedural pass: no summaries, and not summarizing on demand.")
		return
	}

	// Build the inter-procedural flow graph
	g.BuildGraph()

	// Open the coverage file if specified in configuration
	coverage := openCoverage(c)
	if coverage != nil {
		defer coverage.Close()
	}

	// Run the analysis
	g.RunVisitorOnEntryPoints(visitor, spec)
}

// RunVisitorOnEntryPoints runs the visitor on the entry points designated by either the isEntryPoint function
// or the isGraphEntryPoint function.
func (g *InterProceduralFlowGraph) RunVisitorOnEntryPoints(visitor Visitor, spec ScanningSpec) {

	g.AnalyzerState.Logger.Infof("Scanning for entry points ...\n")
	entryPoints := make(map[KeyType]NodeWithTrace)
	for _, summary := range g.Summaries {
		// Identify the entry points for that function: all the call sites that are entry points
		summary.ForAllNodes(scanEntryPoints(g, spec, entryPoints))
	}

	g.AnalyzerState.Logger.Infoboxf(" %d analysis entry points", len(entryPoints))
	if g.AnalyzerState.Logger.LogsDebug() {
		for _, entryPoint := range entryPoints {
			g.AnalyzerState.Logger.Debugf("Entry: %s", entryPoint.Node)
			g.AnalyzerState.Logger.Debugf("      in context %s", entryPoint.Trace)
		}
	}

	// Run the analysis for every entrypoint. We may be able to change this to RunIntraProcedural the analysis for all
	// entrypoints at once, but this would require a finer context-tracking mechanism than what the NodeWithCallStack
	// implements.
	// If the maximum number of alarms has been reached, stop early.
	i := 0
	for _, entry := range entryPoints {
		if !g.AnalyzerState.TestAlarmCount() {
			g.AnalyzerState.Logger.Warnf("%d entrypoints are skipped, max number of alarms reached.",
				len(entryPoints)-i)
			return
		}
		visitor.Visit(g.AnalyzerState, entry)
		i++
	}
}

//
//gocyclo:ignore
func scanEntryPoints(
	g *InterProceduralFlowGraph,
	spec ScanningSpec,
	entryPoints map[KeyType]NodeWithTrace) func(n GraphNode) {
	return func(n GraphNode) {
		if spec.IsEntryPointGraph != nil {
			if _, ok := spec.IsEntryPointGraph(n); ok {
				switch node := n.(type) {
				case *CallNodeArg:
					contexts := GetAllCallingContexts(g.AnalyzerState, node.ParentNode())
					nodes := addContexts(contexts, node)
					for _, nt := range nodes {
						entryPoints[nt.Key()] = nt
					}
					return
				}

				for _, callnode := range n.Graph().Callsites {
					contexts := GetAllCallingContexts(g.AnalyzerState, callnode)
					nodes := addContexts(contexts, n)
					for _, node := range nodes {
						entryPoints[node.Key()] = node
					}
				}
			}
		}
		// if the isEntryPointSsa function is not specified, skip the special casing
		if spec.IsEntryPointSsa == nil {
			return
		}

		// special cases for each SSA node type supported
		// TODO: try to factor out the special cases in the isEntryPointGraphNode functions
		switch node := n.(type) {
		case *SyntheticNode:
			addSyntheticNodeEntryPoints(spec, entryPoints, node)
		case *CallNodeArg:
			if spec.MarkCallArgsLikeCall {
				if _, ok := spec.IsEntryPointSsa(node.parent.CallSite().Value()); ok {
					entry := NodeWithTrace{Node: node, Trace: nil, ClosureTrace: nil}
					entryPoints[entry.Key()] = entry
				}
			}
		case *CallNode:
			if node.callSite == nil {
				return
			}

			if cid, ok := spec.IsEntryPointSsa(node.callSite.Value()); ok {
				if funcutil.Exists(cid.Target.Objects, func(obj config.TargetObject) bool {
					return obj.Kind == config.ArgumentKind
				}) {
					// Matching cid has an argument object which means the call itself is not an entrypoint
					return
				}

				contexts := GetAllCallingContexts(g.AnalyzerState, node)
				nodes := addContexts(contexts, node)
				for _, node := range nodes {
					entryPoints[node.Key()] = node
				}

				if spec.MarkCallArgsLikeCall {
					for _, arg := range node.args {
						entry := NodeWithTrace{arg, nil, nil}
						entryPoints[entry.Key()] = entry
					}
				}
			}
		}
	}
}

func addSyntheticNodeEntryPoints(
	spec ScanningSpec,
	entryPoints map[KeyType]NodeWithTrace,
	node *SyntheticNode) {
	if spec.IsEntryPointSsa == nil {
		return
	}
	asValue, isValue := node.Instr().(ssa.Node)
	if !isValue {
		return
	}
	if _, ok := spec.IsEntryPointSsa(asValue); ok {
		entry := NodeWithTrace{Node: node}
		entryPoints[entry.Key()] = entry
	}
}

// addContexts returns a new NodeWithTrace for each calling context of node.
// If contexts is empty or nil, then the node is returned without context.
func addContexts(contexts []*CallStack, node GraphNode) []NodeWithTrace {
	var res []NodeWithTrace
	if len(contexts) == 0 {
		// Default behaviour is to start without context (trace is nil)
		node := NodeWithTrace{Node: node, Trace: nil, ClosureTrace: nil}
		res = append(res, node)
	} else {
		for _, ctxt := range contexts {
			n := NodeWithTrace{
				Node:         node,
				Trace:        ctxt,
				ClosureTrace: nil,
			}
			res = append(res, n)
		}
	}

	return res
}

// resolveCalleeSummary fetches the summary of node's callee, using all possible summary resolution methods. It also
// sets the edge from callee to caller, if it could find a summary.
// Returns nil if no summary can be found.
func (g *InterProceduralFlowGraph) resolveCalleeSummary(node *CallNode,
	nameAliases map[string]*ssa.Function) *SummaryGraph {
	var calleeSummary *SummaryGraph
	logger := g.AnalyzerState.Logger

	// If it's not an interface contract, attempt to just find the summary in the dataflow graph's computed summaries
	if node.callee.Type != lang.InterfaceContract {
		calleeSummary = g.findSummary(node.Callee(), nameAliases)
	}

	if calleeSummary == nil {
		calleeSummary, err := NewPredefinedSummary(node.Callee(), GetUniqueFunctionID())
		if err != nil {
			// An error in our own predefined summaries: this should not happen, but panic if we missed something.
			panic(fmt.Errorf("could not create summary for %s: %s", formatutil.SanitizeRepr(node.Callee()), err))
		}
		if calleeSummary != nil {
			logger.Debugf("Loaded %s from summaries.\n", formatutil.SanitizeRepr(node.Callee()))
			g.Summaries[node.Callee()] = calleeSummary
		}
	}

	if calleeSummary != nil && !calleeSummary.Constructed {
		if shortSummary, isPredefined := summaries.SummaryOfFunc(node.Callee()); isPredefined {
			calleeSummary.PopulateGraphFromSummary(shortSummary, false)
			// Mark predefined summaries as sound
			calleeSummary.IsSound = true
			logger.Debugf("Constructed %s from summaries.\n", formatutil.SanitizeRepr(node.Callee()))
		}
	}

	// Add edge from callee to caller (adding a call site in the callee)
	if calleeSummary != nil {
		if x := calleeSummary.Callsites[node.CallSite()]; x == nil {
			calleeSummary.Callsites[node.CallSite()] = node
		}
	} else {
		g.summaryNotFound(node)
	}

	return calleeSummary
}

// ensureExternalSummaryCallees populates Callees/Callsites for an externally loaded or predefined summary
// by harvesting the real callsites from the callee's SSA (when available) and cloning only the call-related
// nodes into the external summary. It does not alter the summary's flows between non-call nodes.
func (g *InterProceduralFlowGraph) ensureExternalSummaryCallees(callee *ssa.Function, externalSummary *SummaryGraph) {
	// Preconditions and quick exits
	if externalSummary == nil {
		return
	}
	// Already has callees populated
	if len(externalSummary.Callees) > 0 {
		return
	}
	// No SSA implementation to harvest from
	if callee == nil || len(callee.Blocks) == 0 {
		return
	}

	// Ensure maps are initialized to avoid nil map writes during cloning/back-filling
	if externalSummary.Callees == nil {
		externalSummary.Callees = make(map[ssa.CallInstruction]map[*ssa.Function]*CallNode)
	}
	if externalSummary.Callsites == nil {
		externalSummary.Callsites = make(map[ssa.CallInstruction]*CallNode)
	}

	// Build a temporary real summary to harvest call nodes
	tmpSummary, err := g.PerformDataflowAnalysis(callee)
	if err != nil || tmpSummary == nil {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("ensureExternalSummaryCallees: skip harvesting for %s (err=%v)", callee.Name(), err)
		}
		return
	}

	// Clone only the callee/call nodes into the external summary
	nodeMapping := make(map[GraphNode]GraphNode)
	g.cloneCalleeNodes(tmpSummary, externalSummary, nodeMapping)

	// Back-fill callsites for convenience (used by unwinding and diagnostics)
	for instr, nodes := range externalSummary.Callees {
		for _, cn := range nodes {
			if x := externalSummary.Callsites[instr]; x == nil {
				externalSummary.Callsites[instr] = cn
			}
		}
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Populated external summary callees for %s: %d instr entries",
			callee.Name(), len(externalSummary.Callees))
	}
}

// findSummary returns the summary graph of f in summaries if present. Returns nil if not.
//
// This will also return a summary if:
//   - f$thunk is the input, and f has a summary, then f's summary is returned
//   - f is the input, and f$thunk has a summary, then f$thunk's summary is returned.
//
// This also holds for f and f$bound. The function checks that the position of the returned summary is the same as the
// position of the function.
func (g *InterProceduralFlowGraph) findSummary(f *ssa.Function, names map[string]*ssa.Function) *SummaryGraph {
	if summary, ok := g.Summaries[f]; ok {
		return summary
	}
	// Check if the function might correspond to a thunk
	actualThunk := g.findSummaryModuloSuffix(f, names, "$thunk")
	if actualThunk != nil {
		return actualThunk
	}
	// Check if the function might correspond to a bound function
	actualBound := g.findSummaryModuloSuffix(f, names, "$bound")
	if actualBound != nil {
		return actualBound
	}

	return nil
}

func (g *InterProceduralFlowGraph) findSummaryModuloSuffix(f *ssa.Function, names map[string]*ssa.Function,
	suffix string) *SummaryGraph {
	// Either the function has been summarized, and we are looking for function + suffix,
	// or the function + suffix has been summarized, and we are looking for the function.
	if alias, ok := names[f.String()+suffix]; ok {
		summary := g.Summaries[alias]
		if summary != nil && f.Pos() == summary.Parent.Pos() {
			return summary
		}
	}
	if alias, ok := names[f.String()]; ok {
		summary := g.Summaries[alias]
		if summary != nil && f.Pos() == summary.Parent.Pos() {
			return summary
		}
	}
	return nil
}

// findClosureSummary returns the summary graph of the function used in the MakeClosure instruction instr
func (g *InterProceduralFlowGraph) findClosureSummary(instr *ssa.MakeClosure) *SummaryGraph {
	switch funcValue := instr.Fn.(type) {
	case *ssa.Function:
		if summary, ok := g.Summaries[funcValue]; ok {
			return summary
		}
		return nil

	default:
		return nil
	}
}

// hasSSACalls reports whether the function contains any call/invoke/go/defer instructions.
func (g *InterProceduralFlowGraph) hasSSACalls(fn *ssa.Function) bool {
	if fn == nil || len(fn.Blocks) == 0 {
		return false
	}
	for _, b := range fn.Blocks {
		for _, instr := range b.Instrs {
			if _, ok := instr.(ssa.CallInstruction); ok {
				return true
			}
		}
	}
	return false
}

// enumerateSSAStaticCallees returns statically known callees from SSA (handles direct calls and invokes).
// It ignores dynamic/indirect calls that cannot be resolved statically.
func (g *InterProceduralFlowGraph) enumerateSSAStaticCallees(fn *ssa.Function) []*ssa.Function {
	if fn == nil || len(fn.Blocks) == 0 {
		return nil
	}
	seen := make(map[*ssa.Function]bool)
	var out []*ssa.Function
	for _, b := range fn.Blocks {
		for _, instr := range b.Instrs {
			if ci, ok := instr.(ssa.CallInstruction); ok {
				cc := ci.Common()
				if cal := cc.StaticCallee(); cal != nil && !seen[cal] {
					seen[cal] = true
					out = append(out, cal)
				}
			}
		}
	}
	return out
}

// enumerateSSAResolvedCallees returns callees by scanning SSA and resolving
// both static and dynamic (invoke/interface) calls using AnalyzerState.ResolveCallee.
// This provides a more complete fallback when summary.Callees is empty.
func (g *InterProceduralFlowGraph) enumerateSSAResolvedCallees(fn *ssa.Function) []*ssa.Function {
	if fn == nil || len(fn.Blocks) == 0 {
		return nil
	}
	seen := make(map[*ssa.Function]bool)
	var out []*ssa.Function
	for _, b := range fn.Blocks {
		for _, instr := range b.Instrs {
			ci, ok := instr.(ssa.CallInstruction)
			if !ok {
				continue
			}
			cc := ci.Common()
			if cal := cc.StaticCallee(); cal != nil {
				if !seen[cal] {
					seen[cal] = true
					out = append(out, cal)
				}
				continue
			}
			// Dynamic or interface call: try resolving via state
			if g.AnalyzerState != nil {
				if callees, err := g.AnalyzerState.ResolveCallee(ci, true); err == nil {
					for f := range callees {
						if f != nil && !seen[f] {
							seen[f] = true
							out = append(out, f)
						}
					}
				} else if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("enumerateSSAResolvedCallees: ResolveCallee failed at %s: %v", ci.String(), err)
				}
			}
		}
	}
	return out
}

func (g *InterProceduralFlowGraph) summaryNotFound(node *CallNode) {
	if node.callee.Callee.Name() != "init" &&
		g.AnalyzerState.IsReachableFunction(node.callee.Callee) {

		g.AnalyzerState.Logger.Debugf("Could not find summary of %s", node.callSite)
		if node.callee.Callee != nil {
			g.AnalyzerState.Logger.Debugf("|-- Key: %s", formatutil.SanitizeRepr(node.callee.Callee))
		}
		g.AnalyzerState.Logger.Debugf("|-- Location: %s", node.Position(g.AnalyzerState))

		if node.callSite.Common().IsInvoke() {
			g.AnalyzerState.Logger.Debugf("|-- invoke resolved to callee %s",
				formatutil.SanitizeRepr(node.callee.Callee))
		}
	}
}

// openCoverage opens the coverage file, if the config requires it.
// the caller is responsible for closing the file if non-nil
func openCoverage(c *State) *os.File {
	var err error
	var coverage *os.File

	if c.Config.ReportCoverage {
		coverage, err = os.CreateTemp(c.Config.ReportsDir, "coverage-*.out")
		if err != nil {
			coverage = nil
			c.Logger.Warnf("Could not create coverage file, continuing.\n")
			c.Logger.Warnf("Error was: %s", err)
		} else {
			c.Logger.Infof("Writing coverage information in %s.\n", coverage.Name())
			_, _ = coverage.WriteString("mode: set\n")
		}
	}
	return coverage
}

// openSummaries returns a non-nil opened file if the configuration is set properly
// the caller is responsible for closing the file if non-nil
func openSummaries(c *State) *os.File {
	var err error
	var summariesFile *os.File

	if c.Config.ReportSummaries {
		summariesFile, err = os.CreateTemp(c.Config.ReportsDir, "summaries-*.out")
		if err != nil {
			summariesFile = nil
			c.Logger.Warnf("Could not create summaries files, continuing.\n")
			c.Logger.Warnf("Error was: %s", err)
		} else {
			c.Logger.Infof("Writing summaries in %s.\n", summariesFile.Name())
		}
	}
	return summariesFile
}

// UnwindCallstackFromCallee returns the CallNode that should be returned upon. It satisfies the following conditions:
// - the CallNode is in the callsites set
// - the CallNode is in the stack
// If no CallNode satisfies these conditions, nil is returned.
func UnwindCallstackFromCallee(callsites map[ssa.CallInstruction]*CallNode, stack *CallStack) *CallNode {
	// no trace = nowhere to return to.
	if stack == nil {
		return nil
	}

	// the number of callsites in a call is expected to be small
	for _, x := range callsites {
		if x.CallSite() == stack.Label.CallSite() && x.Callee() == stack.Label.Callee() {
			return x
		}
	}
	// no return node has been found
	return nil
}

// UnwindCallStackToFunc looks for the callstack pointer where f was called. Returns nil if no such function can be
// found
func UnwindCallStackToFunc(stack *CallStack, f *ssa.Function) *CallStack {
	cur := stack
	for cur != nil {
		if cur.Label.Callee() == f {
			return cur
		}
		cur = cur.Parent
	}
	return nil
}

// debugSummaryFlows outputs detailed flow information for the three summaries used in soundness checking
func (g *InterProceduralFlowGraph) debugSummaryFlows(function *ssa.Function, Su, Sg, Sp *SummaryGraph) {
	g.AnalyzerState.Logger.Debugf("=== SUMMARY FLOWS DEBUG for %s ===", function.Name())

	// Debug Su (Summary Under Check)
	// g.AnalyzerState.Logger.Debugf("--- Su (Summary Under Check) ---")
	// g.logSummaryFlows(Su)

	// // Debug Sg (Most General)
	// g.AnalyzerState.Logger.Debugf("--- Sg (Most General) ---")
	// g.logSummaryFlows(Sg)

	// // Debug Sp (Most Preserved)
	// g.AnalyzerState.Logger.Debugf("--- Sp (Most Preserved) ---")
	// g.logSummaryFlows(Sp)

	// Show comparison results
	g.AnalyzerState.Logger.Debugf("--- Comparison Results ---")
	g.AnalyzerState.Logger.Debugf("Sp == Sg: %v", g.compareSummaries(Sp, Sg))
	g.AnalyzerState.Logger.Debugf("Sp ⊆ Su: %v", g.isSummarySubset(Sp, Su))
	g.AnalyzerState.Logger.Debugf("Su ⊆ Sg: %v", g.isSummarySubset(Su, Sg))
	g.AnalyzerState.Logger.Debugf("Su == Sg: %v", g.compareSummaries(Su, Sg))
	g.AnalyzerState.Logger.Debugf("Sp == Su: %v", g.compareSummaries(Sp, Su))

	g.AnalyzerState.Logger.Debugf("=== END SUMMARY FLOWS DEBUG ===")
}

// // logSummaryFlows logs detailed flow information for a single summary
// func (g *InterProceduralFlowGraph) logSummaryFlows(summary *SummaryGraph) {
// 	if summary == nil {
// 		g.AnalyzerState.Logger.Debugf("  Summary: nil")
// 		return
// 	}

// 	// Count nodes and edges
// 	nodeCount := 0
// 	edgeCount := 0
// 	nodeTypes := make(map[string]int)

// 	summary.ForAllNodes(func(node GraphNode) {
// 		nodeCount++
// 		nodeType := g.getNodeTypeName(node)
// 		nodeTypes[nodeType]++
// 		edgeCount += len(node.Out())
// 	})

// 	g.AnalyzerState.Logger.Debugf("  Total Nodes: %d, Total Edges: %d", nodeCount, edgeCount)
// 	g.AnalyzerState.Logger.Debugf("  Node Types: %v", nodeTypes)

// 	// Show detailed node and edge information
// 	g.AnalyzerState.Logger.Debugf("  Detailed Flows:")
// 	summary.ForAllNodes(func(node GraphNode) {
// 		if len(node.Out()) > 0 {
// 			g.AnalyzerState.Logger.Debugf("    %s:", node.String())
// 			for dest, edgeInfos := range node.Out() {
// 				for _, edgeInfo := range edgeInfos {
// 					condStr := "unconditional"
// 					if edgeInfo.Cond != nil && !edgeInfo.Cond.Satisfiable {
// 						condStr = "never"
// 					} else if edgeInfo.Cond != nil && len(edgeInfo.Cond.Conditions) > 0 {
// 						condStr = fmt.Sprintf("conditional(%d)", len(edgeInfo.Cond.Conditions))
// 					}
// 					pathStr := ""
// 					if len(edgeInfo.RelPath) > 0 {
// 						pathStr = fmt.Sprintf(" [paths: %d]", len(edgeInfo.RelPath))
// 					}
// 					g.AnalyzerState.Logger.Debugf("      → %s (%s)%s", dest.String(), condStr, pathStr)
// 				}
// 			}
// 		}
// 	})
// }

// // getNodeTypeName returns a simplified type name for logging
// func (g *InterProceduralFlowGraph) getNodeTypeName(node GraphNode) string {
// 	switch node.(type) {
// 	case *ParamNode:
// 		return "Param"
// 	case *CallNode:
// 		return "Call"
// 	case *CallNodeArg:
// 		return "CallArg"
// 	case *ReturnValNode:
// 		return "Return"
// 	case *SyntheticNode:
// 		return "Synthetic"
// 	case *BuiltinCallNode:
// 		return "Builtin"
// 	case *ClosureNode:
// 		return "Closure"
// 	case *BoundVarNode:
// 		return "BoundVar"
// 	case *AccessGlobalNode:
// 		return "Global"
// 	case *FreeVarNode:
// 		return "FreeVar"
// 	case *IfNode:
// 		return "If"
// 	case *BoundLabelNode:
// 		return "BoundLabel"
// 	default:
// 		return fmt.Sprintf("%T", node)
// 	}
// }

// ============================= LEGACY SOUNDNESS IMPLEMENTATION BEGIN =============================
// NOTE: This block is kept temporarily for reference / fallback. The new stepwise pipeline lives in
//
//	soundness_stepwise.go and is enabled via StepwiseSoundnessEnabled. After stabilization this
//	region can be safely removed.
//
// checkSummarySoundness checks if a summary is sound by comparing three types of summaries.
// This is the public interface that maintains backward compatibility.
func (g *InterProceduralFlowGraph) CheckSummarySoundness(
	function *ssa.Function,
	summaryUnderCheck *SummaryGraph) (bool, string, map[*ssa.Function]*SummaryGraph) {

	// Initialize recursion tracking
	visited := make(map[*ssa.Function]bool)
	cache := make(map[*ssa.Function]bool)

	return g.checkSummarySoundnessStepwise(function, summaryUnderCheck, 0, visited, cache)
}

// extractStepFromReason extracts the step name from a soundness check reason string.
// Returns the step name (e.g., "Step1", "Step2", etc.) or "Other" if not recognized.
func extractStepFromReason(reason string) string {
	// Check for step-specific patterns
	if strings.Contains(reason, "equals full-flow") {
		return "Step1"
	}
	if strings.Contains(reason, "type-infeasible") {
		return "Step2"
	}
	if strings.Contains(reason, "immutability") {
		return "Step3"
	}
	if strings.Contains(reason, "reaching") {
		return "Step4"
	}
	if strings.Contains(reason, "subspec") || strings.Contains(reason, "leaf intra subset") || strings.Contains(reason, "external subset") {
		return "Step5"
	}
	if strings.Contains(reason, "cached") {
		return "Cached"
	}
	if strings.Contains(reason, "cycle") {
		return "Cycle"
	}
	if strings.Contains(reason, "depth cap") {
		return "DepthLimit"
	}
	return "Other"
}

// CheckExternalSummaries is a wrapper around CheckSummarySoundness to check all external summaries.
// It returns both the unsound summaries and statistics about the checking process.
func (g *InterProceduralFlowGraph) CheckExternalSummaries() ([]*SummaryGraph, *SoundnessCheckStats, error) {
	var unsoundSummaries []*SummaryGraph
	if !g.IsBuilt() {
		unsoundSummaries = g.BuildGraph()
	}

	stats := &SoundnessCheckStats{
		StepDistribution: make(map[string]int),
	}

	var checkedFns = make(map[*ssa.Function]bool)

	// Check all summaries that are part of the call graph
	for function, summary := range g.Summaries {
		if summary.IsPreSummarized {
			stats.TotalSummaries++
			isSound, reason, _ := g.CheckSummarySoundness(function, summary)
			if !isSound {
				stats.UnsoundCount++
				// avoid duplicates
				isNew := true
				for _, unsound := range unsoundSummaries {
					if unsound == summary {
						isNew = false
						break
					}
				}
				if isNew {
					unsoundSummaries = append(unsoundSummaries, summary)
				}
				g.AnalyzerState.Logger.Warnf("Unsound external summary for %s: %s", function.String(), reason)
			} else {
				stats.SoundCount++
				step := extractStepFromReason(reason)
				stats.StepDistribution[step]++
			}
			checkedFns[function] = true
		}
	}

	return unsoundSummaries, stats, nil
}

// checkSummarySoundnessRecursive is the internal recursive implementation that checks soundness
// with cycle detection, depth limiting, and caching.
//
// Parameters:
// - function: The function whose summary is being checked
// - summaryUnderCheck: The summary to validate
// - recursionDepth: Current recursion depth (0 for root call)
// - visited: Set of functions currently being analyzed (cycle detection)
// - cache: Cache of previously computed soundness results
//
// Returns:
// - bool: true if sound, false if unsound
// - string: reason for the decision
// - map[*ssa.Function]*SummaryGraph: subspecs that need deeper analysis
func (g *InterProceduralFlowGraph) checkSummarySoundnessRecursive(
	function *ssa.Function,
	summaryUnderCheck *SummaryGraph,
	recursionDepth int,
	visited map[*ssa.Function]bool,
	cache map[*ssa.Function]bool) (bool, string, map[*ssa.Function]*SummaryGraph) {
	// LEGACY: original recursive multi-case algorithm (Case0/1/2/3)

	const maxRecursionDepth = 100

	// Debug logging for recursion
	if g.AnalyzerState.Logger.LogsDebug() {
		indent := strings.Repeat("  ", recursionDepth)
		g.AnalyzerState.Logger.Debugf("%sRecursive soundness check: %s (depth %d)",
			indent, function.Name(), recursionDepth)
	}

	// Check cache first
	if result, cached := cache[function]; cached {
		reason := "cached result"
		if result {
			reason = "Summary is sound: cached positive result"
		} else {
			reason = "Summary is unsound: cached negative result"
		}
		return result, reason, nil
	}

	// Check for cycles
	if visited[function] {
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sCycle detected for %s, assuming sound", indent, function.Name())
		}
		return true, "Summary is sound: cycle detected, assumed sound", nil
	}

	// Check recursion depth limit
	if recursionDepth >= maxRecursionDepth {
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sMax depth reached for %s, using most-general assumption",
				indent, function.Name())
		}
		// Use most-general summary assumption beyond max depth
		summaryUnderCheck.IsSound = true
		cache[function] = true
		return true, "Summary is sound: max recursion depth reached, assumed most-general", nil
	}

	// Mark as being visited
	visited[function] = true
	defer func() {
		delete(visited, function)
	}()

	// Case 0: Easiest case - if Su == Sg, trivially sound (LEGACY)
	Sg := createFullFlowSummary(summaryUnderCheck)
	if g.compareSummaries(summaryUnderCheck, Sg) {
		summaryUnderCheck.IsSound = true
		return true, "Summary is sound: already equivalent to full flow summary", nil
	}

	// Case 1: immutable analysis (LEGACY)
	if result := IsSpecSatisfyimmutable(summaryUnderCheck); result.IsSatisfied {
		// Targeted SSA verification - much faster than checking all parameters
		isValid, reason := CheckParametersimmutableInSSA(result, function)
		if isValid {
			// Case 1 succeeded
			summaryUnderCheck.IsSound = true
			cache[function] = true
			return true, "Summary is sound: immutable parameters confirmed", nil
		}
		// Case 1 failed, but continue to other cases - don't return false here
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sCase 1 (immutable) failed: %s, trying other cases", indent, reason)
		}
	}

	// Case 2: Intra-procedural reaching-definition analysis (LEGACY)
	// Apply this quick proof only for functions with NO SSA calls to keep over-approx guarantees robust.
	if !g.hasSSACalls(function) {
		Sr := g.createReachingDefinitionSummary(function)
		SrFlows := g.extractParamFlows(Sr)
		// Accept Case 2 only if Sr is informative (non-empty) and Sr ⊆ Su
		if len(SrFlows) > 0 && g.isSummarySubset(Sr, summaryUnderCheck) {
			// Case 2 succeeded: actual ⊆ Sr ⊆ Su
			summaryUnderCheck.IsSound = true
			cache[function] = true
			return true, "Summary is sound: covers reaching-definition flows (no calls)", nil
		}
		// Case 2 failed for a no-calls function, continue to Case 3
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sCase 2 failed (no-calls): Sr empty=%v, subset=%v; trying Case 3",
				indent, len(SrFlows) == 0, g.isSummarySubset(Sr, summaryUnderCheck))
		}
	} else if g.AnalyzerState.Logger.LogsDebug() {
		indent := strings.Repeat("  ", recursionDepth)
		g.AnalyzerState.Logger.Debugf("%sCase 2 bypassed: function has SSA calls; trying Case 3", indent)
	}

	// Case 3: Inter-procedural analysis by generating subspec (LEGACY)

	// ENHANCED DIAGNOSTIC LOGGING: Compare SSA vs Summary callees
	g.AnalyzerState.Logger.Debugf("=== CASE 3 ENTRY for %s ===", function.Name())

	// Ensure external/predefined summaries have their Callees populated if missing
	if len(summaryUnderCheck.Callees) == 0 {
		g.ensureExternalSummaryCallees(function, summaryUnderCheck)
	}

	// 1. Function Type & SSA Status
	g.AnalyzerState.Logger.Debugf("Function has %d blocks", len(function.Blocks))
	g.AnalyzerState.Logger.Debugf("Summary constructed: %v", summaryUnderCheck.Constructed)
	if function.Pkg != nil && function.Pkg.Pkg != nil {
		g.AnalyzerState.Logger.Debugf("Package: %s", function.Pkg.Pkg.Path())
	}

	// 2. Direct SSA Call Analysis (Most Important!)
	g.AnalyzerState.Logger.Debugf("=== SSA CALL INSTRUCTIONS ===")
	ssaCallCount := 0
	if len(function.Blocks) > 0 {
		for blockIdx, block := range function.Blocks {
			for instrIdx, instr := range block.Instrs {
				if call, ok := instr.(*ssa.Call); ok {
					ssaCallCount++
					calleeStr := "unknown"
					var calleeFunc *ssa.Function

					// Try to get the callee function
					if call.Call.Value != nil {
						calleeStr = call.Call.Value.String()
						if fn, ok := call.Call.Value.(*ssa.Function); ok {
							calleeFunc = fn
						}
					}

					// Enhanced logging for each SSA call
					g.AnalyzerState.Logger.Debugf("  SSA Call %d: %s (block %d, instr %d)",
						ssaCallCount, calleeStr, blockIdx, instrIdx)

					if calleeFunc != nil {
						g.AnalyzerState.Logger.Debugf("    Signature: %s", calleeFunc.Signature.String())
						if g.AnalyzerState.Program != nil && g.AnalyzerState.Program.Fset != nil {
							pos := g.AnalyzerState.Program.Fset.Position(calleeFunc.Pos())
							g.AnalyzerState.Logger.Debugf("    Location: %s", pos)
						}
						if calleeFunc.Pkg != nil && calleeFunc.Pkg.Pkg != nil {
							g.AnalyzerState.Logger.Debugf("    Package: %s", calleeFunc.Pkg.Pkg.Path())
						}
						// Check if it's external
						isExternal := len(calleeFunc.Blocks) == 0
						g.AnalyzerState.Logger.Debugf("    External: %v", isExternal)
					}
				}
			}
		}
	}
	g.AnalyzerState.Logger.Debugf("Total SSA calls found: %d", ssaCallCount)

	// 3. Summary Callees Comparison
	g.AnalyzerState.Logger.Debugf("=== SUMMARY CALLEES MAP ===")
	g.AnalyzerState.Logger.Debugf("Summary.Callees map size: %d", len(summaryUnderCheck.Callees))
	summaryCalleeCount := 0
	for instr, calleeMap := range summaryUnderCheck.Callees {
		g.AnalyzerState.Logger.Debugf("  Instruction: %s -> %d callees", instr.String(), len(calleeMap))
		for _, callNode := range calleeMap {
			callee := callNode.Callee()
			if callee != nil {
				summaryCalleeCount++
				g.AnalyzerState.Logger.Debugf("    Summary Callee %d: %s", summaryCalleeCount, callee.Name())
				// Add signature and location for summary callees too
				g.AnalyzerState.Logger.Debugf("      Signature: %s", callee.Signature.String())
				if g.AnalyzerState.Program != nil && g.AnalyzerState.Program.Fset != nil {
					pos := g.AnalyzerState.Program.Fset.Position(callee.Pos())
					g.AnalyzerState.Logger.Debugf("      Location: %s", pos)
				}
				if callee.Pkg != nil && callee.Pkg.Pkg != nil {
					g.AnalyzerState.Logger.Debugf("      Package: %s", callee.Pkg.Pkg.Path())
				}
				isExternal := len(callee.Blocks) == 0
				g.AnalyzerState.Logger.Debugf("      External: %v", isExternal)
			}
		}
	}

	// 4. Summary vs SSA Comparison
	g.AnalyzerState.Logger.Debugf("=== COMPARISON SUMMARY ===")
	g.AnalyzerState.Logger.Debugf("SSA calls found: %d", ssaCallCount)
	g.AnalyzerState.Logger.Debugf("Summary callees found: %d", summaryCalleeCount)
	if ssaCallCount != summaryCalleeCount {
		g.AnalyzerState.Logger.Debugf("WARNING: Mismatch between SSA calls (%d) and summary callees (%d)",
			ssaCallCount, summaryCalleeCount)
	}

	// Step 1: Create maximal summary assuming all callees have full graphs
	maximalSummary := g.createMostGeneralSummary(function)
	if maximalSummary == nil {
		return false, "Failed to create maximal summary for Case 3", nil
	}

	// Step 2: Extract flows using existing function (handles transitive closure)
	actualFlows := g.extractParamFlows(summaryUnderCheck)
	maximalFlows := g.extractParamFlows(maximalSummary)

	// Debug logging
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Case 3: Actual flows count: %d", len(actualFlows))
		g.AnalyzerState.Logger.Debugf("Case 3: Maximal flows count: %d", len(maximalFlows))
	}

	// Step 3: Find missing edges (target set)
	targetSet := g.findMissingEdgesForCase3(actualFlows, maximalFlows, summaryUnderCheck, maximalSummary)

	if len(targetSet) == 0 {
		summaryUnderCheck.IsSound = true
		return true, "Summary is sound: no missing edges in Case 3", nil
	}

	// Debug logging for target set
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Case 3: Found %d missing edges in target set", len(targetSet))
		for i, pair := range targetSet {
			if i < 5 { // Log first 5 edges to avoid spam
				g.AnalyzerState.Logger.Debugf("  Missing edge %d: %s -> %s", i, pair.Source.String(), pair.Target.String())
			}
		}
		if len(targetSet) > 5 {
			g.AnalyzerState.Logger.Debugf("  ... and %d more missing edges", len(targetSet)-5)
		}
	}

	// Step 4: Implement set-cover algorithm for subspec generation

	// Step 4a: Identify potential subspec options for each callee
	potentialOptions := g.identifyPotentialCalleeSubspecs(summaryUnderCheck, targetSet)

	// Step 4a.1: ALWAYS recursively check ALL callees, even if they can't help with current violations
	recursiveCheckResults := g.recursivelyCheckAllCallees(summaryUnderCheck, recursionDepth, visited, cache)

	if len(potentialOptions) == 0 {
		// CRITICAL FIX: Handle the case where a function has no callees (external functions)
		// For external functions with no callees, missing edges cannot be resolved by subspecs,
		// but this is expected and should not be considered an error.

		if recursiveCheckResults.CalleeCount == 0 {
			// This is a leaf function with no callees
			g.AnalyzerState.Logger.Debugf("reach the leaf, run intra-procedural")

			// Check if this is an external function (no Go source code implementation)
			isExternalFunction := len(function.Blocks) == 0 || (len(function.Blocks) > 0 && len(function.Blocks[0].Instrs) == 0)

			if isExternalFunction {
				// For external functions, the summary must be a valid and intentional subset of
				// the maximal summary. An empty summary is a subset, but is likely unsound.
				// We require Su == Sg, unless Su is identity or empty, which are valid special cases.
				g.AnalyzerState.Logger.Debugf("External leaf function %s: validating against maximal summary", function.Name())

				maximalSummary := g.createMostGeneralSummary(function)
				if maximalSummary == nil {
					// This is a failure condition. We cannot verify the summary.
					g.AnalyzerState.Logger.Debugf("Cannot create maximal summary for external function %s, assuming unsound", function.Name())
					summaryUnderCheck.IsSound = false
					cache[function] = false
					return false, "Summary is unsound: external function, cannot create maximal summary", nil
				}

				// Check for equivalence with the most general summary
				if g.compareSummaries(summaryUnderCheck, maximalSummary) {
					summaryUnderCheck.IsSound = true
					cache[function] = true
					return true, "Summary is sound: external function matches maximal flows (Sg)", nil
				}

				// Check for valid special cases: identity summary
				identitySummary := g.createIdentitySummary(function)
				if g.compareSummaries(summaryUnderCheck, identitySummary) {
					summaryUnderCheck.IsSound = true
					cache[function] = true
					return true, "Summary is sound: external function is identity", nil
				}

				// If it's not Sg and not identity, it's an invalid partial summary.
				summaryFlows := g.extractParamFlows(summaryUnderCheck)
				maximalFlows := g.extractParamFlows(maximalSummary)
				g.AnalyzerState.Logger.Debugf("Summary flows (%d): %v", len(summaryFlows), summaryFlows)
				g.AnalyzerState.Logger.Debugf("Maximal flows (%d): %v", len(maximalFlows), maximalFlows)

				summaryUnderCheck.IsSound = false
				cache[function] = false
				return false, "Summary is unsound: external function has a partial summary that is not a recognized pattern (full or identity)", nil

			} else {
				// For internal leaf functions, run intra-procedural analysis to get ground truth flows
				intraSummary, err := g.PerformDataflowAnalysis(function)
				if err != nil {
					// If intra-procedural analysis fails, we cannot verify the summary, so it is unsound.
					g.AnalyzerState.Logger.Warnf("Intra-procedural analysis failed for leaf function %s: %v", function.Name(), err)
					summaryUnderCheck.IsSound = false
					cache[function] = false
					return false, "Summary is unsound: leaf function, intra-procedural analysis failed", nil
				}

				// Compare summary under check against intra-procedural result
				// Sound if intra-procedural flows ⊆ summary flows (summary is superset of real flows)
				if g.isSummarySubset(intraSummary, summaryUnderCheck) {
					summaryUnderCheck.IsSound = true
					cache[function] = true
					return true, "Summary is sound: covers all actual parameter flows", nil
				}

				// Log the differences for debugging
				summaryFlows := g.extractParamFlows(summaryUnderCheck)
				intraFlows := g.extractParamFlows(intraSummary)
				g.AnalyzerState.Logger.Debugf("Summary flows (%d): %v", len(summaryFlows), summaryFlows)
				g.AnalyzerState.Logger.Debugf("Intra-procedural flows (%d): %v", len(intraFlows), intraFlows)

				summaryUnderCheck.IsSound = false
				cache[function] = false
				return false, "Summary is unsound: missing some actual parameter flows", nil
			}
		}

		// This function has callees, but none can help resolve the violations
		if recursiveCheckResults.AllCalleesSound {
			// All callees are sound, but they still can't help with our violations
			summaryUnderCheck.IsSound = false
			return false, fmt.Sprintf("Summary is unsound: %d missing edges cannot be resolved by any callee subspec (but %d callees recursively validated)",
				len(targetSet), recursiveCheckResults.CalleeCount), nil
		} else {
			// Some callees are unsound
			summaryUnderCheck.IsSound = false
			return false, fmt.Sprintf("Summary is unsound: %d missing edges cannot be resolved, and some callees are unsound: %s",
				len(targetSet), recursiveCheckResults.FirstFailureReason), nil
		}
	}

	// Debug logging for potential options
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Case 3: Found %d potential subspec options", len(potentialOptions))
		for i, option := range potentialOptions {
			if i < 10 { // Log first 10 options to avoid spam
				g.AnalyzerState.Logger.Debugf("  Option %d: %s (%s) fixes %d violations",
					i, option.Callee.Name(), option.SubspecType, option.FixCount)
			}
		}
		if len(potentialOptions) > 10 {
			g.AnalyzerState.Logger.Debugf("  ... and %d more options", len(potentialOptions)-10)
		}
	}

	// Step 4b: Run greedy set-cover algorithm
	setCoverResult := g.greedySetCoverAlgorithm(potentialOptions, targetSet)

	// Step 4c: Check if set-cover was successful
	if len(setCoverResult.Uncovered) > 0 {
		// Some violations could not be covered
		summaryUnderCheck.IsSound = false
		return false, fmt.Sprintf("Summary is unsound: %d violations remain uncovered after set-cover",
			len(setCoverResult.Uncovered)), nil
	}

	// Step 4d: Generate final subspecs for selected callees with recursive checking
	calleesDiveDeeperMap, err := g.generateSelectedSubspecsWithRecursiveCheck(
		summaryUnderCheck, setCoverResult, recursionDepth, visited, cache)

	if err != nil {
		// Recursive checking failed - propagate failure up
		summaryUnderCheck.IsSound = false
		cache[function] = false
		return false, fmt.Sprintf("Summary is unsound: recursive subspec checking failed: %v", err), nil
	}

	// Debug final results
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Case 3: Set-cover completed successfully with recursive validation")
		g.AnalyzerState.Logger.Debugf("  Selected %d callees for subspec generation", len(calleesDiveDeeperMap))
		for callee, subspecType := range setCoverResult.SelectedCallees {
			g.AnalyzerState.Logger.Debugf("  - %s: %s subspec (recursively validated)", callee.Name(), subspecType)
		}
	}

	// Cache the successful result
	summaryUnderCheck.IsSound = true
	cache[function] = true
	return true, fmt.Sprintf("Summary is sound with recursive subspec validation: covered %d violations using %d callees",
		len(targetSet), len(calleesDiveDeeperMap)), calleesDiveDeeperMap
}

// createMostGeneralSummary creates a summary where every callee function has maximum possible dataflows.
// This represents Sg (most-general summary) in the summary soundness check.
//
//gocyclo:ignore
func (g *InterProceduralFlowGraph) createMostGeneralSummary(function *ssa.Function) *SummaryGraph {
	// Debug logging at function entry
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] === createMostGeneralSummary ENTRY for %s ===", function.Name())
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Function blocks: %d", len(function.Blocks))
		if len(function.Blocks) > 0 {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] First block instructions: %d", len(function.Blocks[0].Instrs))
		}
	}

	// Validate input parameters
	if g == nil {
		panic("InterProceduralFlowGraph is nil")
	}
	if g.AnalyzerState == nil {
		panic("AnalyzerState is nil")
	}
	if function == nil {
		panic("function parameter is nil")
	}

	// External/body-less function: build maximal param/return connectivity
	if len(function.Blocks) == 0 || (len(function.Blocks) > 0 && len(function.Blocks[0].Instrs) == 0) {
		id := GetUniqueFunctionID()
		summary := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
		g.createExternalFunctionNodes(summary, function)
		summary.BuildFullFlowGraph()
		summary.Constructed = true
		summary.IsSound = true
		return summary
	}

	// INTERNAL: Sg = re-run intra-procedural on a clone with all callees set to full
	// IMPORTANT: use a fresh SSA-based summary; do NOT reuse a pre-constructed external/contract summary.
	base, err := g.PerformFreshDataflowAnalysis(function)
	if err != nil || base == nil {
		// fallback: full connectivity on caller
		id := GetUniqueFunctionID()
		fallback := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
		fallback.BuildFullFlowGraph()
		fallback.Constructed = true
		fallback.IsSound = true
		return fallback
	}

	maximal := g.cloneSummary(base)
	if maximal == nil {
		id := GetUniqueFunctionID()
		maximal = NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
	}

	// Set each callee summary to full
	for _, calleeMap := range maximal.Callees {
		for _, callNode := range calleeMap {
			if callNode.Callee() == nil {
				continue
			}
			if callNode.CalleeSummary == nil {
				id := GetUniqueFunctionID()
				callNode.CalleeSummary = NewSummaryGraph(g.AnalyzerState, callNode.Callee(), id, IsNodeOfInterest, nil)
			}
			callNode.CalleeSummary.BuildFullFlowGraph()
			callNode.CalleeSummary.Constructed = true
			callNode.CalleeSummary.IsSound = true
		}
	}

	// Ensure a default tracker to avoid nil deref in intra analysis
	if maximal.shouldTrack == nil {
		maximal.shouldTrack = IsNodeOfInterest
	}
	if _, err := RunIntraProcedural(g.AnalyzerState, maximal); err != nil {
		maximal.BuildFullFlowGraph()
	}

	// Augment caller-level interference to reflect callee-full semantics:
	// For each callsite, find caller parameters that flow into any call argument.
	// Add param→param edges between all such parameters and param→return edges to all returns.
	g.augmentCallerParamInterferenceForFullCallees(maximal)

	// If there are no callees, the intra-procedural analysis is all we have,
	// but we still need to ensure it represents the "most general" case,
	// which means full flow between params and returns.
	if len(maximal.Callees) == 0 {
		maximal.BuildFullFlowGraph()
	}

	// If there are no callees, the intra-procedural analysis is all we have,
	// but we still need to ensure it represents the "most general" case,
	// which means full flow between params and returns.
	if len(maximal.Callees) == 0 {
		maximal.BuildFullFlowGraph()
	}

	maximal.Constructed = true
	maximal.IsSound = true
	return maximal
}

// PerformFreshDataflowAnalysis performs intra-procedural dataflow analysis on a fresh summary,
// ignoring any pre-existing constructed summaries in g.Summaries. It does NOT register the
// produced summary in g.Summaries to avoid side effects during soundness checks.
func (g *InterProceduralFlowGraph) PerformFreshDataflowAnalysis(function *ssa.Function) (*SummaryGraph, error) {
	if function == nil {
		return nil, fmt.Errorf("cannot analyze nil function")
	}

	id := GetUniqueFunctionID()
	// Force a fresh summary with proper tracker
	summary := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)

	// Run the intra-procedural analysis
	elapsed, err := RunIntraProcedural(g.AnalyzerState, summary)
	if err != nil {
		return nil, fmt.Errorf("fresh dataflow analysis failed for %v: %w", function, err)
	}

	g.AnalyzerState.Logger.Debugf("PerformFreshDataflowAnalysis: Finished analyzing %v (%.2f s)",
		function, elapsed.Seconds())

	// Mark the summary as constructed and sound (since it's computed by the program)
	summary.Constructed = true
	summary.IsSound = true
	summary.SyncGlobals()

	return summary, nil
}

// augmentCallerParamInterferenceForFullCallees adds caller-level param→param and param→return edges
// among parameters that participate as sources of any call argument. This lifts callee full-connectivity
// to the caller summary to ensure Sg over-approximates potential interference through callees.
func (g *InterProceduralFlowGraph) augmentCallerParamInterferenceForFullCallees(summary *SummaryGraph) {
	if summary == nil || summary.Parent == nil {
		return
	}

	// 1) Collect all CallNodeArg as targets
	callArgTargets := make(map[GraphNode]bool)
	for _, calleeMap := range summary.Callees {
		for _, callNode := range calleeMap {
			for _, arg := range callNode.args {
				if arg != nil {
					callArgTargets[arg] = true
				}
			}
		}
	}
	if len(callArgTargets) == 0 {
		return
	}

	// 2) From each ParamNode, DFS to see if it can reach any CallNodeArg
	reachesAnyCallArg := func(start GraphNode) bool {
		visited := make(map[GraphNode]bool)
		var dfs func(GraphNode) bool
		dfs = func(n GraphNode) bool {
			if visited[n] {
				return false
			}
			visited[n] = true
			if callArgTargets[n] {
				return true
			}
			for m := range n.Out() {
				if dfs(m) {
					return true
				}
			}
			return false
		}
		return dfs(start)
	}

	involved := make(map[*ParamNode]bool)
	for _, p := range summary.Params {
		if p == nil {
			continue
		}
		if reachesAnyCallArg(p) {
			involved[p] = true
		}
	}
	if len(involved) == 0 {
		return
	}

	// 3) Add param→param and param→return edges for involved params
	fullEI := EdgeInfo{RelPath: map[string]map[string]bool{"*": {"": true}}, Index: 0, Cond: nil}

	params := make([]*ParamNode, 0, len(involved))
	for p := range involved {
		params = append(params, p)
	}

	// param→param full connectivity among involved
	for i := 0; i < len(params); i++ {
		for j := 0; j < len(params); j++ {
			if i == j {
				continue
			}
			src := params[i]
			dst := params[j]
			if _, ok := src.Out()[dst]; !ok {
				if src.Out()[dst] == nil {
					src.Out()[dst] = make([]EdgeInfo, 0, 1)
				}
				src.Out()[dst] = append(src.Out()[dst], fullEI)
				dst.In()[src] = fullEI
			}
		}
	}

	// param→return edges to all return nodes
	for _, retNodes := range summary.Returns {
		for _, ret := range retNodes {
			if ret == nil {
				continue
			}
			for src := range involved {
				if _, ok := src.Out()[ret]; !ok {
					if src.Out()[ret] == nil {
						src.Out()[ret] = make([]EdgeInfo, 0, 1)
					}
					src.Out()[ret] = append(src.Out()[ret], fullEI)
					ret.In()[src] = fullEI
				}
			}
		}
	}
}

// createExternalFunctionNodes creates parameter and return nodes for external functions
// based on their function signatures. This is essential before calling BuildFullFlowGraph()
// on external functions, otherwise there are no nodes to connect.
func (g *InterProceduralFlowGraph) createExternalFunctionNodes(summary *SummaryGraph, function *ssa.Function) {
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] === createExternalFunctionNodes ENTRY for %s ===", function.Name())
	}

	if summary == nil || function == nil {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] createExternalFunctionNodes: summary=%v, function=%v - returning early", summary == nil, function == nil)
		}
		return
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Function signature - Params: %d, Results: %d",
			len(function.Params), function.Signature.Results().Len())
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Summary before node creation - Params: %d, Returns: %d",
			len(summary.Params), len(summary.Returns))
	}

	paramCount := 0
	// Create parameter nodes based on function signature
	for i, param := range function.Params {
		if summary.shouldTrack == nil || summary.shouldTrack(g.AnalyzerState, param) {
			paramNode := &ParamNode{
				id:      summary.newNodeID(),
				parent:  summary,
				ssaNode: param,
				out:     make(map[GraphNode][]EdgeInfo),
				in:      make(map[GraphNode]EdgeInfo),
				argPos:  i,
			}
			summary.Params[param] = paramNode
			paramCount++

			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Created parameter node %d: %s (%s) with ID %d",
					i, param.Name(), param.Type(), paramNode.id)
			}
		} else {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Skipped parameter node %d: %s (not tracked)",
					i, param.Name())
			}
		}
	}

	returnCount := 0
	// Create return value nodes based on function signature
	sig := function.Signature
	if sig.Results() != nil && sig.Results().Len() > 0 {
		// Create a synthetic return instruction to hold the return nodes
		// We use nil as the key since external functions don't have actual return instructions
		var syntheticReturnInstr ssa.Instruction = nil
		returnNodes := make([]*ReturnValNode, sig.Results().Len())

		for i := 0; i < sig.Results().Len(); i++ {
			returnNode := &ReturnValNode{
				id:     summary.newNodeID(),
				parent: summary,
				index:  i,
				in:     make(map[GraphNode]EdgeInfo),
				out:    make(map[GraphNode][]EdgeInfo),
			}
			returnNodes[i] = returnNode
			returnCount++

			if g.AnalyzerState.Logger.LogsDebug() {
				resultVar := sig.Results().At(i)
				g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Created return node %d: %s with ID %d",
					i, resultVar.Type(), returnNode.id)
			}
		}

		summary.Returns[syntheticReturnInstr] = returnNodes

		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Added %d return nodes to summary.Returns[nil]", len(returnNodes))
		}
	} else {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] No return values to create for function %s", function.Name())
		}
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] === createExternalFunctionNodes EXIT: created %d params, %d returns ===",
			paramCount, returnCount)
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Summary after node creation - Params: %d, Returns: %d",
			len(summary.Params), len(summary.Returns))
	}
}

// createReachingDefinitionSummary creates a summary using lightweight intra-procedural reaching-definition analysis,
// making direct use of SSA structure. This represents Sr (reaching-definition summary) in the summary soundness check.
func (g *InterProceduralFlowGraph) createReachingDefinitionSummary(function *ssa.Function) *SummaryGraph {
	// Create a fresh empty summary
	id := GetUniqueFunctionID()
	summary := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)

	// Perform lightweight reaching definition analysis using SSA structure directly
	reachingDefs := PerformLightweightReachingDefinition(g.AnalyzerState, function)

	// Build summary based on reaching definition results
	BuildSummaryFromReachingDefs(g.AnalyzerState, summary, reachingDefs)

	// Mark the summary as constructed and sound
	summary.Constructed = true
	summary.IsSound = true
	summary.SyncGlobals()

	return summary
}

// createMostPreservedSummary creates a summary assuming no dataflows between callees.
// This represents Sp (most-preserved summary) in the summary soundness check.
func (g *InterProceduralFlowGraph) createMostPreservedSummary(function *ssa.Function) *SummaryGraph {
	// Get or create a fresh summary for the function
	summary := g.Summaries[function]
	if summary == nil {
		id := GetUniqueFunctionID()
		summary = NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
		// Clone the summary to avoid modifying the original
		// summary = g.cloneSummary(summary)
	} else {
		// Clone the summary to avoid modifying the original
		summary = g.cloneSummary(summary)
	}

	// For each callee, create empty summaries with no dataflows
	for _, calleeMap := range summary.Callees {
		for _, callNode := range calleeMap {
			// For most-preserved, assume every callee has no internal dataflows
			if callNode.Callee() != nil {
				// If the callee doesn't have a summary, create one
				if callNode.CalleeSummary == nil {
					id := GetUniqueFunctionID()
					calleeSummary := NewSummaryGraph(g.AnalyzerState, callNode.Callee(), id, IsNodeOfInterest, nil)
					callNode.CalleeSummary = calleeSummary
					g.Summaries[callNode.Callee()] = calleeSummary
					// In theory the summary is already empty, here we just call the BuildEmptyGraph to actually enforce it
					callNode.CalleeSummary.BuildEmptyGraph()
				} else if !callNode.CalleeSummary.IsSound {
					// If it has a summary, create a fresh empty clone of it
					emptyCalleeSummary := g.cloneSummary(callNode.CalleeSummary)
					// Use BuildEmptyGraph to clear all edges from the callee summary to represent no dataflows
					emptyCalleeSummary.BuildEmptyGraph()
					callNode.CalleeSummary = emptyCalleeSummary
				}
			}
		}
	}

	// Validate summary state before running intra-procedural analysis
	if summary.shouldTrack == nil {
		g.AnalyzerState.Logger.Debugf("Setting shouldTrack to IsNodeOfInterest for function %v", function)
		summary.shouldTrack = IsNodeOfInterest
	}
	// Perform intra-procedural analysis on our carefully crafted summary
	_, err := RunIntraProcedural(g.AnalyzerState, summary)
	if err != nil {
		// Log error but continue with the summary we've built so far
		g.AnalyzerState.Logger.Warnf("Failed to analyze function %v with minimal callee flows: %v", function, err)
		summary.BuildEmptyGraph() // Fallback to no connectivity
		return summary
	}

	// Mark the summary as constructed and sound
	summary.Constructed = true
	summary.IsSound = true
	summary.SyncGlobals()

	// Use the analyzed summary as our most-preserved summary
	return summary
}

// createIdentitySummary creates a summary with identity flows (param -> return).
func (g *InterProceduralFlowGraph) createIdentitySummary(function *ssa.Function) *SummaryGraph {
	id := GetUniqueFunctionID()
	summary := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
	g.createExternalFunctionNodes(summary, function)
	summary.BuildIdentityGraph()
	summary.Constructed = true
	summary.IsSound = true
	return summary
}

// createEmptySummary creates a summary with no flows.
func (g *InterProceduralFlowGraph) createEmptySummary(function *ssa.Function) *SummaryGraph {
	id := GetUniqueFunctionID()
	summary := NewSummaryGraph(g.AnalyzerState, function, id, IsNodeOfInterest, nil)
	g.createExternalFunctionNodes(summary, function)
	summary.BuildEmptyGraph()
	summary.Constructed = true
	summary.IsSound = true
	return summary
}

// extractParamFlows extracts parameter-to-parameter and parameter-to-return flows from a summary,
// using transitive closure to find all reachable parameters and returns, ignoring self-loops.
func (g *InterProceduralFlowGraph) extractParamFlows(summary *SummaryGraph) map[string]bool {
	flows := make(map[string]bool)

	if summary == nil {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] extractParamFlows: summary is nil, returning empty flows")
		}
		return flows
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] === extractParamFlows DEBUG for %s ===", summary.Parent.Name())
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Summary has %d params, %d return groups",
			len(summary.Params), len(summary.Returns))

		// Enhanced logging for external function debugging
		isExternal := len(summary.Parent.Blocks) == 0 || (len(summary.Parent.Blocks) > 0 && len(summary.Parent.Blocks[0].Instrs) == 0)
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Function type: %s", func() string {
			if isExternal {
				return "EXTERNAL"
			}
			return "INTERNAL"
		}())
	}

	// Collect all target nodes (parameters and return values) into a set for efficient lookup
	targetNodes := make(map[GraphNode]bool)
	paramCount := 0
	for _, paramNode := range summary.Params {
		targetNodes[paramNode] = true
		paramCount++
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Target param node: %s", paramNode.String())
		}
	}

	returnCount := 0
	for instrKey, retNodes := range summary.Returns {
		if g.AnalyzerState.Logger.LogsDebug() {
			instrStr := "nil"
			if instrKey != nil {
				instrStr = instrKey.String()
			}
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Return group for instruction %s: %d nodes", instrStr, len(retNodes))
		}
		for i, ret := range retNodes {
			if ret != nil { // Return nodes can be nil for constant values
				targetNodes[ret] = true
				returnCount++
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Target return node %d: %s", i, ret.String())
				}
			} else {
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Return node %d is nil (skipped)", i)
				}
			}
		}
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Total target nodes: %d params + %d returns = %d",
			paramCount, returnCount, len(targetNodes))
	}

	// For each parameter, find all reachable target nodes using DFS
	flowCount := 0
	for _, paramNode := range summary.Params {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Analyzing flows from param: %s", paramNode.String())
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Param has %d outgoing edges", len(paramNode.Out()))
		}

		visited := make(map[GraphNode]bool)
		reachableTargets := g.findReachableTargets(paramNode, targetNodes, visited)

		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Found %d reachable targets from %s",
				len(reachableTargets), paramNode.String())
		}

		// Record flows to reachable target nodes (excluding self-loops)
		for _, target := range reachableTargets {
			if target != paramNode { // Skip self-loops
				flowKey := fmt.Sprintf("%s -> %s", paramNode.String(), target.String())
				flows[flowKey] = true
				flowCount++
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Added flow: %s", flowKey)
				}
			} else {
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Skipped self-loop: %s -> %s",
						paramNode.String(), target.String())
				}
			}
		}
	}

	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] === extractParamFlows RESULT: %d flows ===", len(flows))
		if len(flows) > 0 {
			for flowKey := range flows {
				g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] Final flow: %s", flowKey)
			}
		} else {
			g.AnalyzerState.Logger.Debugf("[DBG MXFLOW] No flows found!")
		}
	}

	return flows
}

// findReachableTargets performs DFS traversal to find all reachable target nodes
// from the given start node, avoiding cycles using the visited set.
// targetNodes specifies which nodes we consider as valid targets (params and returns).
func (g *InterProceduralFlowGraph) findReachableTargets(startNode GraphNode, targetNodes map[GraphNode]bool, visited map[GraphNode]bool) []GraphNode {
	var targets []GraphNode

	// Mark current node as visited to prevent cycles
	visited[startNode] = true

	// If the current node is a target node, add it to results
	if targetNodes[startNode] {
		targets = append(targets, startNode)
	}

	// Explore all outgoing edges
	edgeCount := 0
	for destNode := range startNode.Out() {
		edgeCount++

		// Skip already visited nodes to prevent cycles
		if visited[destNode] {
			continue
		}

		// Recursively explore this destination node
		subTargets := g.findReachableTargets(destNode, targetNodes, visited)
		targets = append(targets, subTargets...)
	}

	return targets
}

// compareSummaries compares two summaries and returns true if they are equivalent.
// Only compares parameter-to-parameter and parameter-to-return relationships, ignoring self-loops.
func (g *InterProceduralFlowGraph) compareSummaries(summary1, summary2 *SummaryGraph) bool {
	if summary1 == nil || summary2 == nil {
		return summary1 == summary2
	}

	// Extract relevant flows from both summaries
	flows1 := g.extractParamFlows(summary1)
	flows2 := g.extractParamFlows(summary2)

	// Compare the flow sets
	if len(flows1) != len(flows2) {
		return false
	}

	for flow1 := range flows1 {
		if _, exists := flows2[flow1]; !exists {
			return false
		}
	}

	return true
}

// isSummarySubset checks if summary1 is a subset of summary2 (summary1 ⊆ summary2).
// Only considers parameter-to-parameter and parameter-to-return relationships, ignoring self-loops.
func (g *InterProceduralFlowGraph) isSummarySubset(summary1, summary2 *SummaryGraph) bool {
	if summary1 == nil {
		return true // Empty set is a subset of any set
	}
	if summary2 == nil {
		return false // Non-empty set cannot be a subset of an empty set
	}

	// Extract relevant flows from both summaries
	flows1 := g.extractParamFlows(summary1)
	flows2 := g.extractParamFlows(summary2)

	// Check if all flows in summary1 exist in summary2
	for flow1 := range flows1 {
		if _, exists := flows2[flow1]; !exists {
			return false
		}
	}

	return true
}

// compareEdgeInfo compares two EdgeInfo structures and returns true if they are equivalent.
func (g *InterProceduralFlowGraph) compareEdgeInfo(ei1, ei2 EdgeInfo) bool {
	// Check if indices match
	if ei1.Index != ei2.Index {
		return false
	}

	// Compare conditions (either both nil or both equal)
	if (ei1.Cond == nil) != (ei2.Cond == nil) {
		return false
	}
	if ei1.Cond != nil && ei2.Cond != nil {
		if ei1.Cond.Satisfiable != ei2.Cond.Satisfiable {
			return false
		}
		if len(ei1.Cond.Conditions) != len(ei2.Cond.Conditions) {
			return false
		}
		// For simplicity, we're not comparing the actual condition contents
	}

	// Compare RelPath maps
	if len(ei1.RelPath) != len(ei2.RelPath) {
		return false
	}

	// Check if all paths in ei1 exist in ei2
	for inPath1, outPathMap := range ei1.RelPath {
		clonedOutPathMap := make(map[string]bool)
		for outPath, val := range outPathMap {
			clonedOutPathMap[outPath] = val
		}
		outPaths2, exists := ei2.RelPath[inPath1]
		if !exists {
			return false
		}

		if len(outPaths2) != len(clonedOutPathMap) {
			return false
		}

		for outPath1 := range clonedOutPathMap {
			if _, exists := outPaths2[outPath1]; !exists {
				return false
			}
		}
	}

	return true
}

// createEmptySummaryClone creates a new SummaryGraph with the same metadata as the original.
func (g *InterProceduralFlowGraph) createEmptySummaryClone(original *SummaryGraph) *SummaryGraph {
	return &SummaryGraph{
		ID:                    original.ID,
		Constructed:           original.Constructed,
		IsInterfaceContract:   original.IsInterfaceContract,
		IsPreSummarized:       original.IsPreSummarized,
		IsSound:               original.IsSound, // Copy the sound flag to preserve it during cloning
		Parent:                original.Parent,
		Params:                make(map[ssa.Node]*ParamNode),
		FreeVars:              make(map[ssa.Node]*FreeVarNode),
		Callees:               make(map[ssa.CallInstruction]map[*ssa.Function]*CallNode),
		Callsites:             make(map[ssa.CallInstruction]*CallNode),
		BuiltinCalls:          make(map[ssa.CallInstruction]*BuiltinCallNode),
		Returns:               make(map[ssa.Instruction][]*ReturnValNode),
		CreatedClosures:       make(map[ssa.Instruction]*ClosureNode),
		ReferringMakeClosures: make(map[ssa.Instruction]*ClosureNode),
		AccessGlobalNodes:     make(map[ssa.Instruction]map[ssa.Value]*AccessGlobalNode),
		SyntheticNodes:        make(map[ssa.Instruction]*SyntheticNode),
		BoundLabelNodes:       make(map[ssa.Instruction]map[BindingInfo]*BoundLabelNode),
		Ifs:                   make(map[ssa.Instruction]*IfNode),
		errors:                make(map[error]bool),
		lastNodeID:            original.lastNodeID,
		shouldTrack:           original.shouldTrack,
		postBlockCallBack:     original.postBlockCallBack,
	}
}

// cloneParameterNodes clones all parameter nodes from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneParameterNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone parameters
	for k, v := range original.Params {
		paramNode := &ParamNode{
			id:      v.id,
			parent:  clone,
			ssaNode: v.ssaNode,
			out:     make(map[GraphNode][]EdgeInfo),
			in:      make(map[GraphNode]EdgeInfo),
			argPos:  v.argPos,
		}
		clone.Params[k] = paramNode
		nodeMapping[v] = paramNode
	}

	// Clone free variables
	for k, v := range original.FreeVars {
		freeVarNode := &FreeVarNode{
			id:      v.id,
			parent:  clone,
			ssaNode: v.ssaNode,
			out:     make(map[GraphNode][]EdgeInfo),
			in:      make(map[GraphNode]EdgeInfo),
			fvPos:   v.fvPos,
		}
		clone.FreeVars[k] = freeVarNode
		nodeMapping[v] = freeVarNode
	}
}

// cloneCalleeNodes clones all callee and call nodes from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneCalleeNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone callees and call nodes
	for instr, calleeMap := range original.Callees {
		clone.Callees[instr] = make(map[*ssa.Function]*CallNode)
		for fn, callNode := range calleeMap {
			newCallNode := &CallNode{
				id:            callNode.id,
				parent:        clone,
				callee:        callNode.callee,
				CalleeSummary: callNode.CalleeSummary, // Reference to the original callee summary
				args:          make([]*CallNodeArg, len(callNode.args)),
				callSite:      callNode.callSite,
				out:           make(map[GraphNode][]EdgeInfo),
				in:            make(map[GraphNode]EdgeInfo),
			}

			// Clone args
			for i, arg := range callNode.args {
				callNodeArg := &CallNodeArg{
					id:        arg.id,
					parent:    newCallNode,
					ssaValue:  arg.ssaValue,
					argPos:    arg.argPos,
					out:       make(map[GraphNode][]EdgeInfo),
					in:        make(map[GraphNode]EdgeInfo),
					paramName: arg.paramName,
				}
				newCallNode.args[i] = callNodeArg
				nodeMapping[arg] = callNodeArg
			}

			clone.Callees[instr][fn] = newCallNode
			clone.Callsites[instr] = newCallNode
			nodeMapping[callNode] = newCallNode
		}
	}
}

// cloneBuiltinCallNodes clones all builtin call nodes from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneBuiltinCallNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone builtin calls
	for instr, builtinCall := range original.BuiltinCalls {
		builtinCallNode := &BuiltinCallNode{
			id:       builtinCall.id,
			parent:   clone,
			callSite: builtinCall.callSite,
			name:     builtinCall.name,
			out:      make(map[GraphNode][]EdgeInfo),
			in:       make(map[GraphNode]EdgeInfo),
			marks:    builtinCall.marks, // This might need deeper cloning if mutable
		}
		clone.BuiltinCalls[instr] = builtinCallNode
		nodeMapping[builtinCall] = builtinCallNode
	}
}

// cloneReturnNodes clones all return value nodes from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneReturnNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone return values
	for instr, returnValNodes := range original.Returns {
		clonedReturnNodes := make([]*ReturnValNode, len(returnValNodes))
		for i, returnNode := range returnValNodes {
			if returnNode != nil {
				// ReturnValNode now has both 'in' and 'out' fields
				returnValNode := &ReturnValNode{
					id:     returnNode.id,
					parent: clone,
					index:  returnNode.index,
					in:     make(map[GraphNode]EdgeInfo),
					out:    make(map[GraphNode][]EdgeInfo),
				}
				clonedReturnNodes[i] = returnValNode
				nodeMapping[returnNode] = returnValNode
			}
		}
		clone.Returns[instr] = clonedReturnNodes
	}
}

// cloneClosureNodes clones all closure nodes from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneClosureNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone closure nodes
	for instr, closureNode := range original.CreatedClosures {
		clonedClosureNode := &ClosureNode{
			id:             closureNode.id,
			parent:         clone,
			ClosureSummary: closureNode.ClosureSummary, // Reference to the original closure summary
			instr:          closureNode.instr,
			boundVars:      make([]*BoundVarNode, len(closureNode.boundVars)),
			out:            make(map[GraphNode][]EdgeInfo),
			in:             make(map[GraphNode]EdgeInfo),
		}

		// Clone bound variables
		for i, boundVar := range closureNode.boundVars {
			boundVarNode := &BoundVarNode{
				id:       boundVar.id,
				parent:   clonedClosureNode,
				ssaValue: boundVar.ssaValue,
				bPos:     boundVar.bPos,
				out:      make(map[GraphNode][]EdgeInfo),
				in:       make(map[GraphNode]EdgeInfo),
			}
			clonedClosureNode.boundVars[i] = boundVarNode
			nodeMapping[boundVar] = boundVarNode
		}

		clone.CreatedClosures[instr] = clonedClosureNode
		nodeMapping[closureNode] = clonedClosureNode
	}

	// Clone referring make closures
	for instr, makeClosure := range original.ReferringMakeClosures {
		// These should be references to closure nodes we've already created
		if clonedNode, exists := nodeMapping[makeClosure]; exists {
			clone.ReferringMakeClosures[instr] = clonedNode.(*ClosureNode)
		}
	}
}

// cloneMiscNodes clones various other node types (synthetic, bound label, if, access global)
// from the original graph to the clone.
func (g *InterProceduralFlowGraph) cloneMiscNodes(
	original *SummaryGraph,
	clone *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	// Clone synthetic nodes
	for instr, syntheticNode := range original.SyntheticNodes {
		synNode := &SyntheticNode{
			id:     syntheticNode.id,
			parent: clone,
			instr:  syntheticNode.instr,
			label:  syntheticNode.label,
			out:    make(map[GraphNode][]EdgeInfo),
			in:     make(map[GraphNode]EdgeInfo),
		}
		clone.SyntheticNodes[instr] = synNode
		nodeMapping[syntheticNode] = synNode
	}

	// Clone bound label nodes
	for instr, boundLabelMap := range original.BoundLabelNodes {
		clone.BoundLabelNodes[instr] = make(map[BindingInfo]*BoundLabelNode)
		for bindingInfo, boundLabelNode := range boundLabelMap {
			blNode := &BoundLabelNode{
				id:         boundLabelNode.id,
				parent:     clone,
				instr:      boundLabelNode.instr,
				label:      boundLabelNode.label, // Might need deep copy if label is mutable
				targetInfo: boundLabelNode.targetInfo,
				targetAnon: boundLabelNode.targetAnon, // Reference to the original target
				out:        make(map[GraphNode][]EdgeInfo),
				in:         make(map[GraphNode]EdgeInfo),
			}
			clone.BoundLabelNodes[instr][bindingInfo] = blNode
			nodeMapping[boundLabelNode] = blNode
		}
	}

	// Clone if nodes
	for instr, ifNode := range original.Ifs {
		ifn := &IfNode{
			id:      ifNode.id,
			parent:  clone,
			ssaNode: ifNode.ssaNode,
			out:     make(map[GraphNode][]EdgeInfo),
			in:      make(map[GraphNode]EdgeInfo),
		}
		clone.Ifs[instr] = ifn
		nodeMapping[ifNode] = ifn
	}

	// Clone access global nodes
	for instr, globalMap := range original.AccessGlobalNodes {
		clone.AccessGlobalNodes[instr] = make(map[ssa.Value]*AccessGlobalNode)
		for value, accessGlobalNode := range globalMap {
			agNode := &AccessGlobalNode{
				id:      accessGlobalNode.id,
				IsWrite: accessGlobalNode.IsWrite,
				graph:   clone,
				instr:   accessGlobalNode.instr,
				Global:  accessGlobalNode.Global, // Reference to the original global
				out:     make(map[GraphNode][]EdgeInfo),
				in:      make(map[GraphNode]EdgeInfo),
			}
			clone.AccessGlobalNodes[instr][value] = agNode
			nodeMapping[accessGlobalNode] = agNode
		}
	}

	// Clone errors
	for err := range original.errors {
		clone.errors[err] = true
	}
}

// cloneEdgeInfo creates a deep copy of an EdgeInfo structure.
func (g *InterProceduralFlowGraph) cloneEdgeInfo(ei EdgeInfo) EdgeInfo {
	clonedEdgeInfo := EdgeInfo{
		Index: ei.Index,
		Cond:  ei.Cond, // Might need deep copy if condition is mutable
	}

	// Clone RelPath map
	clonedRelPath := make(map[string]map[string]bool)
	for inPath, outPathMap := range ei.RelPath {
		clonedOutPathMap := make(map[string]bool)
		for outPath, val := range outPathMap {
			clonedOutPathMap[outPath] = val
		}
		clonedRelPath[inPath] = clonedOutPathMap
	}
	clonedEdgeInfo.RelPath = clonedRelPath

	return clonedEdgeInfo
}

// restoreEdges recreates all the edges between nodes in the cloned graph.
func (g *InterProceduralFlowGraph) restoreEdges(
	original *SummaryGraph,
	nodeMapping map[GraphNode]GraphNode) {

	original.ForAllNodes(func(origNode GraphNode) {
		// Get the corresponding cloned node
		clonedNode, exists := nodeMapping[origNode]
		if !exists {
			return
		}

		// Copy outgoing edges
		for destOrigNode, edgeInfos := range origNode.Out() {
			destClonedNode, destExists := nodeMapping[destOrigNode]
			if !destExists {
				continue
			}

			// Clone edge infos
			clonedEdgeInfos := make([]EdgeInfo, len(edgeInfos))
			for i, ei := range edgeInfos {
				clonedEdgeInfos[i] = g.cloneEdgeInfo(ei)
			}

			// Add edge to cloned node
			outMap := clonedNode.Out()
			outMap[destClonedNode] = clonedEdgeInfos

			// Add corresponding in-edge
			// We use the first edge info as representative for the in-edge
			if len(clonedEdgeInfos) > 0 {
				addInEdge(destClonedNode, clonedNode, clonedEdgeInfos[0])
			}
		}
	})
}

// cloneSummary creates a complete deep copy of a SummaryGraph to avoid modifying the original.
// This function delegates to helper functions to keep its complexity manageable.
func (g *InterProceduralFlowGraph) cloneSummary(original *SummaryGraph) *SummaryGraph {
	if original == nil {
		return nil
	}

	// Create the base summary structure
	clone := g.createEmptySummaryClone(original)

	// Create a node mapping to help restore edges later
	nodeMapping := make(map[GraphNode]GraphNode)

	// Clone all the different types of nodes
	g.cloneParameterNodes(original, clone, nodeMapping)
	g.cloneCalleeNodes(original, clone, nodeMapping)
	g.cloneBuiltinCallNodes(original, clone, nodeMapping)
	g.cloneReturnNodes(original, clone, nodeMapping)
	g.cloneClosureNodes(original, clone, nodeMapping)
	g.cloneMiscNodes(original, clone, nodeMapping)

	// Restore all the edges between nodes
	g.restoreEdges(original, nodeMapping)

	return clone
}

// isNodeRelatedToCallee checks if a node is related to a specific callee function.
func (g *InterProceduralFlowGraph) isNodeRelatedToCallee(node GraphNode, callee *ssa.Function) bool {
	switch n := node.(type) {
	case *CallNode:
		return n.Callee() == callee
	case *CallNodeArg:
		return n.ParentNode().Callee() == callee
	default:
		return false
	}
}

// findCorrespondingNode finds a node in the target graph that corresponds to the source node.
func (g *InterProceduralFlowGraph) findCorrespondingNode(sourceNode GraphNode, targetGraph *SummaryGraph) (GraphNode, bool) {
	var result GraphNode
	found := false

	targetGraph.ForAllNodes(func(node GraphNode) {
		if node.String() == sourceNode.String() {
			result = node
			found = true
		}
	})

	return result, found
}

// findEdgeDifferences identifies edges that exist in sourceNode but not in targetNode.
// It returns a list of edges (destination nodes and edge infos) that should be added to the result graph.
func (g *InterProceduralFlowGraph) findEdgeDifferences(
	sourceNode, targetNode GraphNode,
	sourceGraph, targetGraph *SummaryGraph) map[GraphNode][]EdgeInfo {

	differences := make(map[GraphNode][]EdgeInfo)

	// For each outgoing edge from the source node
	for destSourceNode, edgeInfos1 := range sourceNode.Out() {
		// Find corresponding destination node in target graph
		destTargetNode, destFound := g.findCorrespondingNode(destSourceNode, targetGraph)

		if !destFound {
			// The edge exists in source but not in target
			differences[destSourceNode] = edgeInfos1
			continue
		}

		// Check if the edge infos are different
		targetEdgeInfos := targetNode.Out()[destTargetNode]

		// For each EdgeInfo in the source, check if it exists in the target
		for _, ei1 := range edgeInfos1 {
			edgeExists := false

			for _, ei2 := range targetEdgeInfos {
				if g.compareEdgeInfo(ei1, ei2) {
					edgeExists = true
					break
				}
			}

			if !edgeExists {
				// This specific edge info doesn't exist in the target
				if _, ok := differences[destSourceNode]; !ok {
					differences[destSourceNode] = []EdgeInfo{ei1}
				} else {
					differences[destSourceNode] = append(differences[destSourceNode], ei1)
				}
			}
		}
	}

	return differences
}

// createIntersectionSummary creates a summary representing (Su∖Sp)∩Gi for a given callee.
// This computes the difference between Su and Sp, then intersects it with the callee's summary.
func (g *InterProceduralFlowGraph) createIntersectionSummary(Su, Sp *SummaryGraph, callee *ssa.Function) *SummaryGraph {
	// Get or create the callee's summary
	calleeSummary := g.Summaries[callee]
	if calleeSummary == nil {
		id := GetUniqueFunctionID()
		calleeSummary = NewSummaryGraph(g.AnalyzerState, callee, id, nil, nil)
	}

	// Clone the callee summary to avoid modifying the original
	result := g.cloneSummary(calleeSummary)

	// Process each node in Su that is related to this callee
	Su.ForAllNodes(func(suNode GraphNode) {
		// Skip nodes not related to the callee
		if !g.isNodeRelatedToCallee(suNode, callee) {
			return
		}

		// Find corresponding node in Sp
		spNode, nodeInSp := g.findCorrespondingNode(suNode, Sp)

		// If the node doesn't exist in Sp, it's fully in Su∖Sp
		// (In a complete implementation, we would add this node and all its edges)
		if !nodeInSp {
			return
		}

		// Find edges that exist in Su but not in Sp
		edgeDifferences := g.findEdgeDifferences(suNode, spNode, Su, Sp)

		// In a complete implementation, we would add these edge differences to the result summary
		// For now, we're just identifying the differences but not actually modifying the result
		if len(edgeDifferences) > 0 {
			g.AnalyzerState.Logger.Debugf(
				"Found %d edge differences for node %s in function %s",
				len(edgeDifferences), suNode.String(), callee.String())
		}
	})

	return result
}

// parseFlowStringToNodes parses a flow string like "param1 -> param2" and returns the corresponding GraphNodes
func (g *InterProceduralFlowGraph) parseFlowStringToNodes(flowString string, summary *SummaryGraph) (GraphNode, GraphNode, bool) {
	parts := strings.Split(flowString, " -> ")
	if len(parts) != 2 {
		return nil, nil, false
	}

	sourceStr := strings.TrimSpace(parts[0])
	targetStr := strings.TrimSpace(parts[1])

	var sourceNode, targetNode GraphNode

	// Find source node
	summary.ForAllNodes(func(node GraphNode) {
		if sourceNode == nil && node.String() == sourceStr {
			sourceNode = node
		}
		if targetNode == nil && node.String() == targetStr {
			targetNode = node
		}
	})

	if sourceNode == nil || targetNode == nil {
		return nil, nil, false
	}

	return sourceNode, targetNode, true
}

// findMissingEdgesForCase3 identifies missing edges between actualSummary and maximalSummary for Case 3 analysis
func (g *InterProceduralFlowGraph) findMissingEdgesForCase3(
	actualFlows, maximalFlows map[string]bool,
	actualSummary, maximalSummary *SummaryGraph) []NodePair {

	var targetSet []NodePair

	// Find flows that exist in maximal but not in actual
	for maximalFlow := range maximalFlows {
		if !actualFlows[maximalFlow] {
			// This is a missing flow, convert to NodePair
			sourceNode, targetNode, ok := g.parseFlowStringToNodes(maximalFlow, maximalSummary)
			if ok {
				targetSet = append(targetSet, NodePair{
					Source: sourceNode,
					Target: targetNode,
				})
			}
		}
	}

	return targetSet
}

// identifyPotentialCalleeSubspecs creates potential subspec options for each callee function
func (g *InterProceduralFlowGraph) identifyPotentialCalleeSubspecs(
	summaryUnderCheck *SummaryGraph,
	targetSet []NodePair) []*CalleeSubspecOption {

	var options []*CalleeSubspecOption
	calleesProcessed := make(map[*ssa.Function]bool)

	// Build a worklist of callees: prefer those recorded in the summary; if empty, fall back to SSA static callees
	var worklist []*ssa.Function
	if len(summaryUnderCheck.Callees) == 0 {
		// Ensure external summaries have their callees harvested when possible
		g.ensureExternalSummaryCallees(summaryUnderCheck.Parent, summaryUnderCheck)
	}
	if len(worklist) == 0 {
		// Use recorded summary callees
		for _, calleeMap := range summaryUnderCheck.Callees {
			for _, callNode := range calleeMap {
				if cal := callNode.Callee(); cal != nil {
					worklist = append(worklist, cal)
				}
			}
		}
	}

	// For each callee in the worklist, try different subspec options
	for _, callee := range worklist {
		if callee == nil || calleesProcessed[callee] {
			continue
		}
		calleesProcessed[callee] = true

		// Try three subspec options: full, empty, identity
		subspecOptions := []string{"full", "empty", "identity"}
		for _, subspecType := range subspecOptions {
			option := &CalleeSubspecOption{
				Callee:          callee,
				SubspecType:     subspecType,
				ViolationsFixed: []NodePair{},
				FixCount:        0,
			}

			// Simulate this subspec and see which violations it fixes
			fixedViolations := g.simulateCalleeSubspec(summaryUnderCheck, callee, subspecType, targetSet)
			option.ViolationsFixed = fixedViolations
			option.FixCount = len(fixedViolations)

			// Only add options that actually fix some violations
			if option.FixCount > 0 {
				options = append(options, option)
			}
		}
	}

	return options
}

// simulateCalleeSubspec simulates applying a subspec to a callee and returns which violations it fixes
func (g *InterProceduralFlowGraph) simulateCalleeSubspec(
	summaryUnderCheck *SummaryGraph,
	callee *ssa.Function,
	subspecType string,
	targetSet []NodePair) []NodePair {

	// CRITICAL FIX: The original logic was inverted. For missing edges, we need to:
	// 1. Create a new maximal summary with the subspec applied to the callee
	// 2. Compare actual flows vs new maximal flows
	// 3. Count how many missing edges are eliminated (not how many flows are added)

	// Create a new maximal summary with the subspec applied to this callee
	testMaximalSummary := g.createMaximalSummaryWithSubspec(summaryUnderCheck.Parent, callee, subspecType)

	// Extract flows from both summaries
	actualFlows := g.extractParamFlows(summaryUnderCheck)
	testMaximalFlows := g.extractParamFlows(testMaximalSummary)

	// Find which violations from targetSet are eliminated by this subspec
	var fixedViolations []NodePair
	for _, violation := range targetSet {
		violationKey := fmt.Sprintf("%s -> %s", violation.Source.String(), violation.Target.String())

		// A violation is "fixed" if:
		// - It was missing in actual vs original maximal (violation.Source -> violation.Target was in maximal but not actual)
		// - After applying subspec, it's no longer missing (either appears in actual or disappears from maximal)

		actualHasFlow := actualFlows[violationKey]
		testMaximalHasFlow := testMaximalFlows[violationKey]

		// The violation is fixed if the discrepancy is eliminated:
		// Either the flow appears in actual, or it disappears from maximal
		if actualHasFlow || !testMaximalHasFlow {
			fixedViolations = append(fixedViolations, violation)
		}
	}

	return fixedViolations
}

// createMaximalSummaryWithSubspec creates a maximal summary for a function with a specific subspec applied to one callee
func (g *InterProceduralFlowGraph) createMaximalSummaryWithSubspec(function *ssa.Function, targetCallee *ssa.Function, subspecType string) *SummaryGraph {
	// Create a maximal summary for the function
	maximalSummary := g.createMostGeneralSummary(function)

	// Clone it to avoid modifying the original
	testSummary := g.cloneSummary(maximalSummary)
	if testSummary == nil {
		// If cloning fails, return the original
		return maximalSummary
	}

	// Apply the specific subspec to the target callee
	g.applySubspecToCallee(testSummary, targetCallee, subspecType)

	// Re-run intra-procedural analysis to propagate the changes
	if testSummary.Parent != nil && len(testSummary.Parent.Blocks) > 0 {
		if testSummary.shouldTrack == nil {
			testSummary.shouldTrack = IsNodeOfInterest
		}
		// Only run intra-procedural analysis for internal functions
		_, err := RunIntraProcedural(g.AnalyzerState, testSummary)
		if err != nil {
			// If analysis fails, fall back to the original maximal summary
			return maximalSummary
		}
	}

	return testSummary
}

// applySubspecToCallee applies a specific subspec type to a callee function in the summary
func (g *InterProceduralFlowGraph) applySubspecToCallee(
	summary *SummaryGraph,
	callee *ssa.Function,
	subspecType string) {

	// Find all call nodes for this callee and modify their summaries
	for _, calleeMap := range summary.Callees {
		for _, callNode := range calleeMap {
			if callNode.Callee() == callee {
				// Create or modify the callee's summary based on subspec type
				switch subspecType {
				case "full":
					g.applyFullSubspec(callNode)
				case "empty":
					g.applyEmptySubspec(callNode)
				case "identity":
					g.applyIdentitySubspec(callNode)
				}
			}
		}
	}
}

// applyFullSubspec applies a full connectivity subspec to a callee
func (g *InterProceduralFlowGraph) applyFullSubspec(callNode *CallNode) {
	if callNode.CalleeSummary == nil {
		id := GetUniqueFunctionID()
		callNode.CalleeSummary = NewSummaryGraph(g.AnalyzerState, callNode.Callee(), id, IsNodeOfInterest, nil)
	}
	callNode.CalleeSummary.BuildFullFlowGraph()
}

// applyEmptySubspec applies an empty connectivity subspec to a callee
func (g *InterProceduralFlowGraph) applyEmptySubspec(callNode *CallNode) {
	if callNode.CalleeSummary == nil {
		id := GetUniqueFunctionID()
		callNode.CalleeSummary = NewSummaryGraph(g.AnalyzerState, callNode.Callee(), id, IsNodeOfInterest, nil)
	}
	callNode.CalleeSummary.BuildEmptyGraph()
}

// applyIdentitySubspec applies an identity connectivity subspec to a callee
func (g *InterProceduralFlowGraph) applyIdentitySubspec(callNode *CallNode) {
	if callNode.CalleeSummary == nil {
		id := GetUniqueFunctionID()
		callNode.CalleeSummary = NewSummaryGraph(g.AnalyzerState, callNode.Callee(), id, IsNodeOfInterest, nil)
	}
	callNode.CalleeSummary.BuildIdentityGraph()
}

// greedySetCoverAlgorithm performs greedy set-cover to select the best combination of subspecs
func (g *InterProceduralFlowGraph) greedySetCoverAlgorithm(
	options []*CalleeSubspecOption,
	targetSet []NodePair) *SetCoverState {

	// Initialize state - TEMPORARY: convert old options to new structure
	edgeOptions := make([]*CalleeEdgeOption, 0)
	for _, option := range options {
		// For now, convert each old-style option to multiple edge options
		// TODO: Replace with proper edge-based enumeration
		edgeOption := &CalleeEdgeOption{
			Callee: option.Callee,
			Edge: SpecificEdge{
				Source:   nil,        // TODO: implement proper edge identification
				Target:   nil,        // TODO: implement proper edge identification
				EdgeInfo: EdgeInfo{}, // TODO: implement proper edge info
			},
			ViolationsFixed: option.ViolationsFixed,
			FixCount:        option.FixCount,
		}
		edgeOptions = append(edgeOptions, edgeOption)
	}

	state := &SetCoverState{
		Universe:      targetSet,
		Uncovered:     make(map[NodePair]bool),
		EdgeOptions:   edgeOptions,
		SelectedEdges: make(map[*ssa.Function][]SpecificEdge),

		// TEMPORARY: Initialize legacy compatibility fields
		CalleeOptions:   options,
		SelectedCallees: make(map[*ssa.Function]string),
	}

	// Initialize uncovered set
	for _, violation := range targetSet {
		state.Uncovered[violation] = true
	}

	// Debug logging
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("Set-cover: Starting with %d violations, %d options",
			len(targetSet), len(options))
	}

	iteration := 0
	// Greedy loop: keep selecting options until all violations are covered
	for len(state.Uncovered) > 0 {
		iteration++

		// Find the option that covers the most uncovered violations
		bestOption := g.findBestOption(state)
		if bestOption == nil {
			// No option can cover any remaining violations
			break
		}

		// Select this option
		state.SelectedCallees[bestOption.Callee] = bestOption.SubspecType

		// Remove the violations this option covers
		coveredCount := 0
		for _, violation := range bestOption.ViolationsFixed {
			if state.Uncovered[violation] {
				delete(state.Uncovered, violation)
				coveredCount++
			}
		}

		// Debug logging
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("Set-cover iteration %d: selected %s (%s), covered %d violations, %d remaining",
				iteration, bestOption.Callee.Name(), bestOption.SubspecType,
				coveredCount, len(state.Uncovered))
		}

		// Prevent infinite loops
		if iteration > 100 {
			g.AnalyzerState.Logger.Warnf("Set-cover algorithm terminated after 100 iterations")
			break
		}
	}

	return state
}

// findBestOption finds the option that covers the most uncovered violations
func (g *InterProceduralFlowGraph) findBestOption(state *SetCoverState) *CalleeSubspecOption {
	var bestOption *CalleeSubspecOption
	maxCoveredCount := 0

	for _, option := range state.CalleeOptions {
		// Skip if we've already selected a subspec for this callee
		if _, alreadySelected := state.SelectedCallees[option.Callee]; alreadySelected {
			continue
		}

		// Count how many uncovered violations this option would fix
		coveredCount := 0
		for _, violation := range option.ViolationsFixed {
			if state.Uncovered[violation] {
				coveredCount++
			}
		}

		// Select this option if it covers more violations
		if coveredCount > maxCoveredCount {
			maxCoveredCount = coveredCount
			bestOption = option
		}
	}

	return bestOption
}

// generateSelectedSubspecs creates the final subspecs based on set-cover results
func (g *InterProceduralFlowGraph) generateSelectedSubspecs(
	summaryUnderCheck *SummaryGraph,
	setCoverResult *SetCoverState) map[*ssa.Function]*SummaryGraph {

	result := make(map[*ssa.Function]*SummaryGraph)

	// For each selected callee, create its subspec
	for callee, subspecType := range setCoverResult.SelectedCallees {
		// Create a fresh summary for the callee
		id := GetUniqueFunctionID()
		subspecSummary := NewSummaryGraph(g.AnalyzerState, callee, id, IsNodeOfInterest, nil)

		// Apply the selected subspec type
		switch subspecType {
		case "full":
			subspecSummary.BuildFullFlowGraph()
		case "empty":
			subspecSummary.BuildEmptyGraph()
		case "identity":
			subspecSummary.BuildIdentityGraph()
		}

		// Mark as constructed and sound
		subspecSummary.Constructed = true
		subspecSummary.IsSound = true

		result[callee] = subspecSummary
	}

	return result
}

// generateSelectedSubspecsWithRecursiveCheck creates subspecs and recursively validates them
func (g *InterProceduralFlowGraph) generateSelectedSubspecsWithRecursiveCheck(
	summaryUnderCheck *SummaryGraph,
	setCoverResult *SetCoverState,
	recursionDepth int,
	visited map[*ssa.Function]bool,
	cache map[*ssa.Function]bool) (map[*ssa.Function]*SummaryGraph, error) {

	result := make(map[*ssa.Function]*SummaryGraph)

	// For each selected callee, create its subspec and recursively check it
	for callee, subspecType := range setCoverResult.SelectedCallees {

		// Debug logging for recursive subspecs generation
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sGenerating %s subspec for %s",
				indent, subspecType, callee.Name())
		}

		// Create a fresh summary for the callee
		id := GetUniqueFunctionID()
		subspecSummary := NewSummaryGraph(g.AnalyzerState, callee, id, IsNodeOfInterest, nil)

		// Apply the selected subspec type
		switch subspecType {
		case "full":
			subspecSummary.BuildFullFlowGraph()
		case "empty":
			subspecSummary.BuildEmptyGraph()
		case "identity":
			subspecSummary.BuildIdentityGraph()
		}

		// Mark as constructed
		subspecSummary.Constructed = true

		// Recursively check if this subspec is sound
		isSound, reason, nestedSubspecs := g.checkSummarySoundnessRecursive(
			callee, subspecSummary, recursionDepth+1, visited, cache)

		if !isSound {
			// Recursive checking failed - propagate the failure up
			if g.AnalyzerState.Logger.LogsDebug() {
				indent := strings.Repeat("  ", recursionDepth)
				g.AnalyzerState.Logger.Debugf("%sRecursive check failed for %s: %s",
					indent, callee.Name(), reason)
			}
			return nil, fmt.Errorf("subspec for %s is unsound: %s", callee.Name(), reason)
		}

		// Mark as sound and add to result
		subspecSummary.IsSound = true
		result[callee] = subspecSummary

		// If the recursive check generated nested subspecs, we could handle them here
		// For now, we just log their existence
		if len(nestedSubspecs) > 0 && g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			g.AnalyzerState.Logger.Debugf("%sSubspec for %s generated %d nested subspecs",
				indent, callee.Name(), len(nestedSubspecs))
		}
	}

	return result, nil
}

// recursivelyCheckAllCallees recursively checks all callees of a function, regardless of whether they help with violations
func (g *InterProceduralFlowGraph) recursivelyCheckAllCallees(
	summaryUnderCheck *SummaryGraph,
	recursionDepth int,
	visited map[*ssa.Function]bool,
	cache map[*ssa.Function]bool) *RecursiveCheckResults {

	results := &RecursiveCheckResults{
		AllCalleesSound:    true,
		CalleeCount:        0,
		FirstFailureReason: "",
	}

	calleesProcessed := make(map[*ssa.Function]bool)

	// Build a worklist of callees: prefer those recorded in the summary; if empty, fall back to SSA static callees
	var worklist []*ssa.Function
	if len(summaryUnderCheck.Callees) == 0 {
		// Ensure external summaries have their callees harvested when possible
		g.ensureExternalSummaryCallees(summaryUnderCheck.Parent, summaryUnderCheck)
		if len(summaryUnderCheck.Callees) == 0 {
			// Prefer resolved enumeration that handles interface invokes via ResolveCallee
			worklist = g.enumerateSSAResolvedCallees(summaryUnderCheck.Parent)
			if len(worklist) == 0 {
				worklist = g.enumerateSSAStaticCallees(summaryUnderCheck.Parent)
			}
		}
	}
	if len(worklist) == 0 {
		for _, calleeMap := range summaryUnderCheck.Callees {
			for _, callNode := range calleeMap {
				if cal := callNode.Callee(); cal != nil {
					worklist = append(worklist, cal)
				}
			}
		}
	}

	// Iterate through all callees in the worklist
	for _, callee := range worklist {
		if callee == nil || calleesProcessed[callee] {
			continue
		}
		calleesProcessed[callee] = true
		results.CalleeCount++

		// Use the actual callee's summary for recursive checking
		var subspecSummary *SummaryGraph

		// Try to get the existing summary for this callee
		if existingSummary, exists := g.Summaries[callee]; exists && existingSummary.Constructed {
			// Use the existing constructed summary
			subspecSummary = existingSummary
		} else {
			// If no existing summary, build one based on the callee's implementation
			if len(callee.Blocks) == 0 {
				// External function: use most-general summary
				subspecSummary = g.createMostGeneralSummary(callee)
			} else {
				// Internal function: perform actual dataflow analysis
				var err error
				subspecSummary, err = g.PerformDataflowAnalysis(callee)
				if err != nil {
					// If analysis fails, mark unsound and continue
					results.AllCalleesSound = false
					if results.FirstFailureReason == "" {
						results.FirstFailureReason = fmt.Sprintf("%s: failed to analyze: %v", callee.Name(), err)
					}
					continue
				}
			}
		}

		// Recursively check this callee with its actual summary
		isSound, reason, _ := g.checkSummarySoundnessRecursive(
			callee, subspecSummary, recursionDepth+1, visited, cache)

		if !isSound {
			results.AllCalleesSound = false
			if results.FirstFailureReason == "" {
				results.FirstFailureReason = fmt.Sprintf("%s: %s", callee.Name(), reason)
			}
			// Continue checking other callees to get full count
		}

		// Debug logging for individual callee results
		if g.AnalyzerState.Logger.LogsDebug() {
			indent := strings.Repeat("  ", recursionDepth)
			status := "sound"
			if !isSound {
				status = "unsound"
			}
			g.AnalyzerState.Logger.Debugf("%sRecursive check for callee %s: %s",
				indent, callee.Name(), status)
		}
	}

	return results
}

// PerformDataflowAnalysis performs intra-procedural dataflow analysis on the given function,
// assuming all callees have already been summarized.
// It returns a summary graph representing which variables can flow to which other variables.
func (g *InterProceduralFlowGraph) PerformDataflowAnalysis(function *ssa.Function) (*SummaryGraph, error) {
	if function == nil {
		return nil, fmt.Errorf("cannot analyze nil function")
	}

	// Check if we already have a summary for this function
	if summary, ok := g.Summaries[function]; ok && summary.Constructed {
		return summary, nil
	}

	// Get or create a new summary
	//TODO: It should be guaranteed to be sound, cnosidering add a field to summary to mark it's sound or not
	// Panic if it's unsound here
	var summary *SummaryGraph
	if existingSummary, ok := g.Summaries[function]; ok {
		summary = existingSummary
	} else {
		id := GetUniqueFunctionID()
		summary = NewSummaryGraph(g.AnalyzerState, function, id, nil, nil)
		g.Summaries[function] = summary
	}

	// Perform the intra-procedural analysis
	elapsed, err := RunIntraProcedural(g.AnalyzerState, summary)
	if err != nil {
		return nil, fmt.Errorf("dataflow analysis failed for %v: %w", function, err)
	}

	g.AnalyzerState.Logger.Debugf("PerformDataflowAnalysis: Finished analyzing %v (%.2f s)",
		function, elapsed.Seconds())

	// Mark the summary as constructed and sound (since it's computed by the program)
	summary.Constructed = true
	summary.IsSound = true

	// Synchronize global information
	summary.SyncGlobals()

	return summary, nil
}

// BuildSummary builds a summary for function and returns it.
// If the summary was already built, i.e. there in a summary corresponding to the function in the flow graph, then
// the summary is constructed by running the intra-procedural dataflow analysis.
// If the summary was not already in the flow graph of the state, it creates a new summary, adds it to the flow graph
// and then runs the intra-procedural dataflow analysis.
//
// BuildSummary expects to be called only on reachable functions, because the analyses usually instantiate the summaries
// only for those functions.
func BuildSummary(s *State, function *ssa.Function) *SummaryGraph {
	summary := s.FlowGraph.Summaries[function]
	if summary != nil && summary.Constructed {
		return summary
	}
	// nil summaries should only happen for functions that should have an internally defined summary, i.e. standard library.
	if summary == nil {
		id := GetUniqueFunctionID()
		predef, err := NewPredefinedSummary(function, id)
		if err != nil {
			// An error in the predefined summaries: this should not happen
			panic(fmt.Errorf("could not create summary for %v: %v", function, err))
		}
		if predef != nil {
			s.FlowGraph.Summaries[function] = predef
			summary = predef
		}
	}
	// Summary is still nil, we should panic now.
	if summary == nil {
		panic(fmt.Errorf("summary for function %v is nil", function))
	}

	logger := s.Logger

	logger.Debugf("BuildSummary: Constructing summary for %v...\n", function)
	elapsed, err := RunIntraProcedural(s, summary)

	if err != nil {
		panic(fmt.Errorf("single function analysis failed for %v: %v", function, err))
	}

	logger.Debugf("BuildSummary: Finished constructing summary for %v (%.2f s)", function, elapsed.Seconds())

	// Mark the summary as sound since it was computed by the program
	summary.IsSound = true

	return summary
}
