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

package dataflow

import (
	"context"
	"fmt"
	"go/types"
	"strings"
	"time"

	"github.com/awslabs/ar-go-tools/analysis/defers"
	"github.com/awslabs/ar-go-tools/analysis/lang"
	"github.com/awslabs/ar-go-tools/analysis/summaries"
	"github.com/awslabs/ar-go-tools/internal/formatutil"
	"github.com/awslabs/ar-go-tools/internal/funcutil"
	"github.com/awslabs/ar-go-tools/internal/pointer"
	"golang.org/x/tools/go/ssa"
)

// This file implements the single function analysis. This analysis pass inspects a single function and constructs
// a dataflow summary of the function.
// - this file `single_function.go` contains the logic that determines when to run the monotone framework analysis,
// call the monotone framework analysis, and builds the dataflow graph from the result of the monotone framework
// analysis.
// - `single_function_monotone_analysis.go` contains all the functions relative to the monotone analysis part of this
// single function analysis.
// - `single_function_instruction_ops.go` file contains all the functions that define how instructions in the function
// are handled.

// IntraProceduralResult holds the results of the intra-procedural analysis.
type IntraProceduralResult struct {
	Summary *SummaryGraph // Summary is the procedure summary built by the analysis
	Time    time.Duration // Time it took to compute the summary
}

// IntraProceduralAnalysis is the main entry point of the intra procedural analysis.
func IntraProceduralAnalysis(state *State,
	function *ssa.Function,
	buildSummary bool,
	id uint32,
	shouldTrack func(*State, ssa.Node) bool,
	postBlockCallback func(*IntraAnalysisState)) (IntraProceduralResult, error) {
	var err error
	var sm *SummaryGraph
	existingSummary := state.FlowGraph.Summaries[function]

	if existingSummary == nil {
		sm = NewSummaryGraph(state, function, id, shouldTrack, postBlockCallback)
	} else {
		sm = existingSummary
		existingSummary.postBlockCallBack = postBlockCallback
		existingSummary.shouldTrack = shouldTrack
	}

	// The function should have at least one instruction!
	if len(function.Blocks) == 0 || len(function.Blocks[0].Instrs) == 0 {
		return IntraProceduralResult{Summary: sm}, nil
	}

	elapsed := time.Duration(0)
	// Run the analysis. Once the analysis terminates, mark the summary as constructed.
	if buildSummary {
		elapsed, err = RunIntraProcedural(state, sm)
		if err != nil {
			return IntraProceduralResult{Summary: sm, Time: elapsed}, err
		}
	}

	return IntraProceduralResult{Summary: sm, Time: elapsed}, nil
}

// BuildEmptyGraph removes all flow edges between nodes in the graph
// This creates a graph with no dataflows at all
func (g *SummaryGraph) BuildEmptyGraph() {
	// Iterate through all nodes in the graph and clear their edges
	g.ForAllNodes(func(n GraphNode) {
		// Clear all outgoing edges
		for dst := range n.Out() {
			delete(n.Out(), dst)
		}

		// Clear incoming edges based on node type
		switch node := n.(type) {
		case *ParamNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *CallNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *CallNodeArg:
			node.in = make(map[GraphNode]EdgeInfo)
		case *FreeVarNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *ReturnValNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *ClosureNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *SyntheticNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *AccessGlobalNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *BoundVarNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *BoundLabelNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *IfNode:
			node.in = make(map[GraphNode]EdgeInfo)
		case *BuiltinCallNode:
			node.in = make(map[GraphNode]EdgeInfo)
		}
	})
}

// BuildFullFlowGraph builds a full flow graph where every input parameter flows to every other input parameter
// and every input parameter flows to every output parameter
func (g *SummaryGraph) BuildFullFlowGraph() {
	// Clear all existing edges first
	g.BuildEmptyGraph()

	// Collect all input nodes (parameters and free variables)
	var inputNodes []GraphNode
	for _, paramNode := range g.Params {
		inputNodes = append(inputNodes, paramNode)
	}
	for _, freeVarNode := range g.FreeVars {
		inputNodes = append(inputNodes, freeVarNode)
	}

	// Collect all output nodes (return values)
	var outputNodes []GraphNode
	for _, retTuple := range g.Returns {
		for _, retNode := range retTuple {
			if retNode != nil {
				outputNodes = append(outputNodes, retNode)
			}
		}
	}

	// Create edge info for full flow (all access paths flow)
	allFlowEdgeInfo := EdgeInfo{
		RelPath: map[string]map[string]bool{"*": {"": true}},
		Index:   0,
		Cond:    nil, // No condition - unconditional flow
	}

	// Create input-to-input flows: every input parameter flows to every other input parameter
	for _, srcNode := range inputNodes {
		for _, dstNode := range inputNodes {
			// Skip self-edges
			if srcNode == dstNode {
				continue
			}

			// Add outgoing edge from source to destination
			if srcNode.Out()[dstNode] == nil {
				srcNode.Out()[dstNode] = make([]EdgeInfo, 0, 1)
			}
			srcNode.Out()[dstNode] = append(srcNode.Out()[dstNode], allFlowEdgeInfo)

			// Add incoming edge to destination from source
			dstNode.In()[srcNode] = allFlowEdgeInfo
		}
	}

	// Create input-to-output flows: every input parameter flows to every output parameter
	for _, srcNode := range inputNodes {
		for _, dstNode := range outputNodes {
			// Add outgoing edge from input to output
			if srcNode.Out()[dstNode] == nil {
				srcNode.Out()[dstNode] = make([]EdgeInfo, 0, 1)
			}
			srcNode.Out()[dstNode] = append(srcNode.Out()[dstNode], allFlowEdgeInfo)

			// Add incoming edge to output from input
			dstNode.In()[srcNode] = allFlowEdgeInfo
		}
	}
}

// BuildIdentityGraph builds an identity flow graph where each parameter flows directly to the corresponding return value
// but no parameter flows to other parameters. This is used for reaching-definition analysis where function calls
// are treated as identity functions (ignoring their internal effects).
func (g *SummaryGraph) BuildIdentityGraph() {
	// Clear all existing edges first
	g.BuildEmptyGraph()

	// Collect all input nodes (parameters and free variables)
	var inputNodes []GraphNode
	for _, paramNode := range g.Params {
		inputNodes = append(inputNodes, paramNode)
	}
	for _, freeVarNode := range g.FreeVars {
		inputNodes = append(inputNodes, freeVarNode)
	}

	// Collect all output nodes (return values) - flatten into a single slice
	var outputNodes []GraphNode
	for _, retTuple := range g.Returns {
		for _, retNode := range retTuple {
			if retNode != nil {
				outputNodes = append(outputNodes, retNode)
			}
		}
	}

	// Create edge info for identity flow
	identityFlowEdgeInfo := EdgeInfo{
		RelPath: map[string]map[string]bool{"": {"": true}},
		Index:   0,
		Cond:    nil, // No condition - unconditional flow
	}

	// Create identity flows: each input parameter flows directly to corresponding return values
	// For simplicity, we'll make each input flow to all returns (simulating identity function behavior)
	for _, srcNode := range inputNodes {
		for _, dstNode := range outputNodes {
			// Add outgoing edge from input to output
			if srcNode.Out()[dstNode] == nil {
				srcNode.Out()[dstNode] = make([]EdgeInfo, 0, 1)
			}
			srcNode.Out()[dstNode] = append(srcNode.Out()[dstNode], identityFlowEdgeInfo)

			// Add incoming edge to output from input
			dstNode.In()[srcNode] = identityFlowEdgeInfo
		}
	}

	// Note: We do NOT create parameter-to-parameter flows in identity graph
	// This represents the case where function calls don't cause parameters to interfere with each other
}

// analysisResult holds the result of the intra-procedural analysis when run in a goroutine
type analysisResult struct {
	duration time.Duration
	err      error
}

// RunIntraProcedural is the core of the intra-procedural analysis. It updates the summary graph *in place* using the
// information contained in the state. It is possible to create a graph first only using NewSummaryGraph and then
// run RunIntraProcedural to update the edges in the graph.
//
// RunIntraProcedural does not add any nod except bound label nodes to the summary graph, it only updates information
// related to the edges.
//
// If the analysis takes longer than 10 seconds, it will be cancelled and replaced with a full graph constructed by
// BuildFullFlowGraph.
func RunIntraProcedural(a *State, sm *SummaryGraph) (time.Duration, error) {
	if sm == nil {
		return 0, fmt.Errorf("summary graph is nil")
	}

	// Create context with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	// Use buffered channel to prevent blocking
	done := make(chan analysisResult, 1)

	// Start analysis goroutine
	go func() {
		// defer func() {
		// 	if r := recover(); r != nil {
		// 		// Handle panic in goroutine
		// 		funcName := "unknown"
		// 		if sm != nil && sm.Parent != nil {
		// 			funcName = formatutil.Sanitize(sm.Parent.String())
		// 		}
		// 		a.Logger.Errorf("Panic in intra-procedural analysis for function %s: %v", funcName, r)
		// 		select {
		// 		case done <- analysisResult{duration: 0, err: fmt.Errorf("analysis panicked: %v", r)}:
		// 		default:
		// 			// Channel might be closed, ignore
		// 		}
		// 	}
		// }()
		start := time.Now()
		err := runOriginalAnalysisWithContext(ctx, a, sm)
		elapsed := time.Since(start)

		// Try to send result, but don't block if timeout already happened
		select {
		case done <- analysisResult{duration: elapsed, err: err}:
		default:
			// Analysis was cancelled, ignore result
		}
	}()

	// Wait for either completion or timeout
	select {
	case result := <-done:
		// Analysis completed within timeout
		return result.duration, result.err
	case <-ctx.Done():
		// Timeout occurred
		if a.Logger != nil {
			funcName := "unknown"
			if sm != nil && sm.Parent != nil {
				funcName = formatutil.Sanitize(sm.Parent.String())
			}
			a.Logger.Warnf("Function %s is cancelled due to time out", funcName)
		}

		// Build full graph as replacement
		start := time.Now()
		sm.BuildFullFlowGraph()
		sm.Constructed = true
		elapsed := time.Since(start)

		return elapsed, nil
	}
}

// // runOriginalAnalysis contains the original RunIntraProcedural logic
// it is temporarily removed by the timing feature
// func runOriginalAnalysis(a *State, sm *SummaryGraph) error {
// 	flowInfo := NewFlowInfo(a.Config, sm.Parent)
// 	// This is the only place an IntraAnalysisState is initialized
// 	state := &IntraAnalysisState{
// 		flowInfo:            flowInfo,
// 		parentAnalyzerState: a,
// 		changeFlag:          true,
// 		blocksSeen:          make([]bool, flowInfo.NumBlocks),
// 		errors:              map[ssa.Node]error{},
// 		summary:             sm,
// 		deferStacks:         defers.AnalyzeFunction(sm.Parent, a.Logger),
// 		paths:               make([]*ConditionInfo, flowInfo.NumBlocks*flowInfo.NumBlocks),
// 		instrPrev:           make([]map[IndexT]bool, flowInfo.NumInstructions),
// 		paramAliases:        make([]map[*ssa.Parameter]bool, flowInfo.NumValues),
// 		freeVarAliases:      make([]map[*ssa.FreeVar]bool, flowInfo.NumValues),
// 		shouldTrack:         sm.shouldTrack,
// 		postBlockCallback:   sm.postBlockCallBack,
// 	}

// 	reportUnsoundFeatures(a, sm.Parent)

// 	// Output warning if defer stack is unbounded
// 	if !state.deferStacks.DeferStackBounded {
// 		a.Logger.Warnf("Defer stack unbounded in %s: %s",
// 			formatutil.Sanitize(sm.Parent.String()), formatutil.Yellow("analysis unsound!"))
// 	}
// 	// First, we initialize the state of the monotone framework analysis (see the initialize function for more details)
// 	state.initialize()
// 	// Once the state is initialized, we call the forward iterative monotone framework analysis. The algorithm is
// 	// defined generally in the lang package, but all the details, including transfer functions, are in the
// 	// single_function_monotone_analysis.go file
// 	lang.RunForwardIterative(state, sm.Parent)
// 	// Once the analysis has RunIntraProcedural, we have a state that maps each instruction to an abstract Value at
// 	// that instruction.  This abstract valuation maps values to the values that flow into them. This can directly be
// 	// translated into a dataflow graph, with special attention for closures.
// 	// Next, we build the edges of the summary. The functions for edge building are in this file
// 	lang.IterateInstructions(sm.Parent, state.makeEdgesAtInstruction)
// 	// Synchronize the edges of global variables
// 	sm.SyncGlobals()
// 	// Update the locsets / marks of the nodes. The locsets are elements that can be used to check results against
// 	// other analyses. Currently, the locsets are the set of instructions that the data represented by a given node
// 	// flows to.
// 	state.moveLocSetsToSummary()
// 	// Mark the summary as constructed
// 	sm.Constructed = true
// 	// If we have errors, return one. This is sufficient to warn the user that the results are incorrect.
// 	// TODO: manage error messages for better debugging
// 	for _, err := range state.errors {
// 		return fmt.Errorf("error in intraprocedural analysis: %w", err)
// 	}
// 	return nil
// }

// runOriginalAnalysisWithContext contains the context-aware RunIntraProcedural logic with cancellation support
func runOriginalAnalysisWithContext(ctx context.Context, a *State, sm *SummaryGraph) error {
	// Check for cancellation at the start
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	// // Validate inputs before starting analysis
	// if sm == nil {
	// 	return fmt.Errorf("summary graph is nil")
	// }
	// if sm.Parent == nil {
	// 	return fmt.Errorf("function is nil")
	// }
	// if len(sm.Parent.Blocks) == 0 {
	// 	return fmt.Errorf("function has no blocks")
	// }

	flowInfo := NewFlowInfo(a.Config, sm.Parent)
	// This is the only place an IntraAnalysisState is initialized
	state := &IntraAnalysisState{
		flowInfo:            flowInfo,
		parentAnalyzerState: a,
		changeFlag:          true,
		blocksSeen:          make([]bool, flowInfo.NumBlocks),
		errors:              map[ssa.Node]error{},
		summary:             sm,
		deferStacks:         defers.AnalyzeFunction(sm.Parent, a.Logger),
		paths:               make([]*ConditionInfo, flowInfo.NumBlocks*flowInfo.NumBlocks),
		instrPrev:           make([]map[IndexT]bool, flowInfo.NumInstructions),
		paramAliases:        make([]map[*ssa.Parameter]bool, flowInfo.NumValues),
		freeVarAliases:      make([]map[*ssa.FreeVar]bool, flowInfo.NumValues),
		shouldTrack:         sm.shouldTrack,
		postBlockCallback:   sm.postBlockCallBack,
	}

	// Check for cancellation after initialization
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	reportUnsoundFeatures(a, sm.Parent)

	// Output warning if defer stack is unbounded
	if !state.deferStacks.DeferStackBounded {
		funcName := "unknown"
		if sm != nil && sm.Parent != nil {
			funcName = formatutil.Sanitize(sm.Parent.String())
		}
		a.Logger.Warnf("Defer stack unbounded in %s: %s", funcName, formatutil.Yellow("analysis unsound!"))
	}

	// Check for cancellation before heavy computation
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	// First, we initialize the state of the monotone framework analysis (see the initialize function for more details)
	state.initialize()

	// Check for cancellation before the most intensive part
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	// Once the state is initialized, we call the forward iterative monotone framework analysis. The algorithm is
	// defined generally in the lang package, but all the details, including transfer functions, are in the
	// single_function_monotone_analysis.go file
	// This is the most time-consuming part of the analysis
	lang.RunForwardIterative(state, sm.Parent)

	// Check for cancellation after forward iterative analysis
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	// Once the analysis has RunIntraProcedural, we have a state that maps each instruction to an abstract Value at
	// that instruction.  This abstract valuation maps values to the values that flow into them. This can directly be
	// translated into a dataflow graph, with special attention for closures.
	// Next, we build the edges of the summary. The functions for edge building are in this file
	lang.IterateInstructions(sm.Parent, state.makeEdgesAtInstruction)

	// Check for cancellation after edge building
	select {
	case <-ctx.Done():
		return ctx.Err()
	default:
	}

	// Synchronize the edges of global variables
	sm.SyncGlobals()
	// Update the locsets / marks of the nodes. The locsets are elements that can be used to check results against
	// other analyses. Currently, the locsets are the set of instructions that the data represented by a given node
	// flows to.
	state.moveLocSetsToSummary()
	// Mark the summary as constructed
	sm.Constructed = true
	// If we have errors, return one. This is sufficient to warn the user that the results are incorrect.
	// TODO: manage error messages for better debugging
	for _, err := range state.errors {
		return fmt.Errorf("error in intraprocedural analysis: %w", err)
	}
	return nil
}

// Dataflow edges in the summary graph are added by the following functions. Those can be called after the iterative
// analysis has computed where all marks reach values at each instruction.

func (state *IntraAnalysisState) makeEdgesAtInstruction(_ int, instr ssa.Instruction) {
	switch typedInstr := instr.(type) {
	case ssa.CallInstruction:
		state.makeEdgesAtCallSite(typedInstr)
	case *ssa.MakeClosure:
		state.makeEdgesAtClosure(typedInstr)
	case *ssa.Return:
		state.makeEdgesAtReturn(typedInstr)
	case *ssa.Store:
		state.makeEdgesAtStoreInCapturedLabel(typedInstr)
	case *ssa.If:
		state.makeEdgesAtIf(typedInstr)
	}
	// Always check if it's a synthetic node
	state.makeEdgesSyntheticNodes(instr)
}

// makeEdgesAtCallsite generates all the edges specific to a given call site.
// Those are the edges to and from call arguments and to and from the call Value.
func (state *IntraAnalysisState) makeEdgesAtCallSite(callInstr ssa.CallInstruction) {
	if isHandledBuiltinCall(callInstr) {
		makeEdgesAtBuiltinCall(state, callInstr)
		return
	}
	// add call node edges for call instructions whose Value corresponds to a function (i.e. the Method is nil)
	if callInstr.Common().Method == nil {
		for _, mark := range state.getMarks(callInstr, callInstr.Common().Value, "", true) {
			state.summary.addCallEdge(mark, nil, callInstr)
			if closure, isMakeClosure := mark.Mark.Node.(*ssa.MakeClosure); isMakeClosure {
				state.updateBoundVarEdges(callInstr, closure)
			}
		}
	}

	args := lang.GetArgs(callInstr)
	// Iterate over each argument and add edges and marks when necessary
	for _, arg := range args {
		// Special case: a global is received directly as an argument
		switch argInstr := arg.(type) {
		case *ssa.Global:
			tmpSrc := state.flowInfo.GetNewMark(callInstr.(ssa.Node), Global, argInstr, NonIndexMark)
			state.summary.addCallArgEdge(MarkWithAccessPath{tmpSrc, ""}, nil, callInstr, argInstr)
		case *ssa.MakeClosure:
			state.updateBoundVarEdges(callInstr, argInstr)
		}
		marks := state.getMarks(callInstr, arg, "", false)
		for _, mark := range marks {
			// Add any necessary edge in the summary flow graph (incoming edges at call site)
			c := state.checkFlow(mark.Mark, callInstr, arg)
			if c.Satisfiable {
				var applicableCond *ConditionInfo
				if c2 := c.AsPredicateTo(arg); len(c2.Conditions) > 0 {
					applicableCond = &c2
				}
				// Add the condition only if it is a predicate on the argument, i.e. there are boolean functions
				// that apply to the destination Value
				state.summary.addCallArgEdge(mark, applicableCond, callInstr, arg)
				argId := state.flowInfo.ValueID[arg] // base argument value is guaranteed to be indexed
				// Add edges to parameters if the call may modify caller's arguments
				for x := range state.paramAliases[argId] {
					if lang.IsNillableType(x.Type()) {
						state.summary.addParamEdge(mark, applicableCond, x)
					}
				}
				for y := range state.freeVarAliases[argId] {
					if lang.IsNillableType(y.Type()) {
						state.summary.addFreeVarEdge(mark, applicableCond, y)
					}
				}
			}
		}
	}
}

// updateBoundVarEdges updates the edges to bound variables.
func (state *IntraAnalysisState) updateBoundVarEdges(instr ssa.Instruction, x *ssa.MakeClosure) {
	for _, boundVar := range x.Bindings {
		for _, boundVarMark := range state.getMarks(instr, boundVar, "", false) {
			state.summary.addBoundVarEdge(boundVarMark, &ConditionInfo{Satisfiable: true}, x, boundVar)
		}
	}
}

// makeEdgesAtClosure adds all the edges corresponding the closure creation site: bound variable edges and any edge
// to parameters and free variables.
func (state *IntraAnalysisState) makeEdgesAtClosure(x *ssa.MakeClosure) {
	for _, boundVar := range x.Bindings {
		for _, markWithPath := range state.getMarks(x, boundVar, "", false) {
			mark := markWithPath.Mark
			if mark.IsClosure() && mark.Node == x {
				continue // avoid spurious edges from closure to its own bound variables
			}
			state.summary.addBoundVarEdge(markWithPath, nil, x, boundVar)
			boundVarID, ok := state.flowInfo.GetValueID(boundVar)
			if !ok {
				continue
			}
			for y := range state.paramAliases[boundVarID] {
				state.summary.addParamEdge(markWithPath, nil, y)
			}

			for y := range state.freeVarAliases[boundVarID] {
				state.summary.addFreeVarEdge(markWithPath, nil, y)
			}
		}
	}
}

// makeEdgesAtReturn creates all the edges to the return node
func (state *IntraAnalysisState) makeEdgesAtReturn(x *ssa.Return) {
	n := state.flowInfo.NumValues
	iID := state.flowInfo.GetInstrPos(x)
	for _, abstractValue := range state.flowInfo.MarkedValues[iID : iID+n] {
		if abstractValue == nil {
			continue
		}
		markedValue := abstractValue.value
		switch val := markedValue.(type) {
		case *ssa.Call:
			// calling Type() may cause segmentation error
			break
		default:
			// Check the state of the analysis at the final return to see which parameters or free variables might
			// have been modified by the function
			if lang.IsNillableType(val.Type()) {
				for _, mark := range abstractValue.AllMarks() {
					markedValueID, ok := state.flowInfo.GetValueID(markedValue)
					if !ok {
						continue
					}
					for aliasedParam := range state.paramAliases[markedValueID] {
						state.summary.addParamEdge(mark, nil, aliasedParam)
					}
					for aliasedFreeVar := range state.freeVarAliases[markedValueID] {
						state.summary.addFreeVarEdge(mark, nil, aliasedFreeVar)
					}
				}
			}
		}
	}

	for tupleIndex, result := range x.Results {
		switch r := result.(type) {
		case *ssa.MakeClosure:
			state.updateBoundVarEdges(x, r)
		}

		for _, origin := range state.getMarks(x, result, "", true) {
			state.summary.addReturnEdge(origin, nil, x, tupleIndex)
		}
	}
}

// makeEdgesAtStoreInCapturedLabel creates edges for store instruction where the target is a pointer that is
// captured by a closure somewhere. The capture information is flow- and context insensitive, so the edge creation is
// too. The interprocedural information will be completed later.
func (state *IntraAnalysisState) makeEdgesAtStoreInCapturedLabel(x *ssa.Store) {
	bounds := state.isCapturedBy(x.Addr)
	if len(bounds) > 0 {
		for _, label := range bounds {
			for target := range state.parentAnalyzerState.BoundingInfo[label.Value()] {
				state.summary.addBoundLabelNode(x, label, *target)
			}
		}
		for _, origin := range state.getMarks(x, x.Addr, "", false) {
			state.summary.addBoundLabelEdge(origin, nil, x)
		}
	}
}

func (state *IntraAnalysisState) makeEdgesAtIf(x *ssa.If) {
	for _, origin := range state.getMarks(x, x.Cond, "", false) {
		state.summary.addIfEdge(origin, nil, x)
	}
}

// makeEdgesSyntheticNodes analyzes the synthetic
func (state *IntraAnalysisState) makeEdgesSyntheticNodes(instr ssa.Instruction) {
	aState := state.parentAnalyzerState
	if state.shouldTrack == nil || !state.shouldTrack(aState, instr.(ssa.Node)) {
		return
	}
	if asValue, ok := instr.(ssa.Value); ok {
		for _, origin := range state.getMarks(instr, asValue, "", false) {
			_, isField := instr.(*ssa.Field)
			_, isFieldAddr := instr.(*ssa.FieldAddr)
			// check flow to avoid duplicate edges between synthetic nodes
			if isField || isFieldAddr {
				state.summary.addSyntheticEdge(origin, nil, instr, "")
			}
		}
	} else if storeInstr, isStore := instr.(*ssa.Store); isStore {
		for _, origin := range state.getMarks(instr, storeInstr.Val, "", false) {
			state.summary.addSyntheticEdge(origin, nil, instr, "")
		}
	}
}

func (state *IntraAnalysisState) moveLocSetsToSummary() {
	for mark, locSet := range state.flowInfo.LocSet {
		for _, graphNode := range state.summary.selectNodesFromMark(*mark) {
			graphNode.SetLocs(locSet)
		}
	}
}

// checkFlow checks whether there can be a flow between the source and the targetInfo instruction and returns a
// condition c. If c.Satisfiable is false, there is no path. If it is true, then there may be a non-empty set of
// conditions in the Conditions list.
//
// The destination must be an instruction. destVal can be used to specify that the flow is to the destination
// (the location) through a specific value. For example, destVal can be the argument of a function call.
//
// Note that in the flow-sensitive analysis, the condition returned should always be satisfiable, but we use the
// condition expressions to decorate edges and allow checking whether a flow is validated in the dataflow analysis.
// We should think of ways to accumulate conditions without using the checkFlow function, which was designed initially
// to filter the spurious flows of the flow-insensitive analysis.
func (state *IntraAnalysisState) checkFlow(source *Mark, dest ssa.Instruction, destVal ssa.Value) ConditionInfo {
	sourceInstr, ok := source.Node.(ssa.Instruction)
	if !ok {
		// if destination is parameter or free variable, this check is not meant to do anything
		// (the flow to a parameter or free var is observed AFTER the function returns)
		_, isDestParam := destVal.(*ssa.Parameter)
		_, isDestFreeVar := destVal.(*ssa.Parameter)
		if !source.IsParameter() || len(dest.Parent().Blocks) <= 0 || isDestFreeVar || isDestParam {
			return ConditionInfo{Satisfiable: true}
		}
		sourceInstr = dest.Parent().Blocks[0].Instrs[0]
	}

	if destVal == nil {
		return state.checkPathBetweenInstructions(sourceInstr, dest)
	}

	// If the destination instruction is a Defer and the destination value is a reference (pointer type) then the
	// taint will always flow to it, since the Defer will be executed after the source.
	if _, isDefer := dest.(*ssa.Defer); isDefer {
		if lang.IsNillableType(destVal.Type()) {
			return ConditionInfo{Satisfiable: true}
		}
		return state.checkPathBetweenInstructions(sourceInstr, dest)
	}
	if asVal, isVal := dest.(ssa.Value); isVal {
		// If the destination is a value of function type, then there is a flow when the source occurs before
		// any instruction that refers to the function (e.g. the function is returned, or called)
		// This is often the case when there is a flow through a closure that binds variables by reference, and
		// the variable is tainted after the closure is created.
		if _, isFunc := asVal.Type().Underlying().(*types.Signature); isFunc {
			return funcutil.FindMap(*asVal.Referrers(),
				func(i ssa.Instruction) ConditionInfo { return state.checkPathBetweenInstructions(sourceInstr, i) },
				func(c ConditionInfo) bool { return c.Satisfiable }).ValueOr(ConditionInfo{Satisfiable: false})
		}
	}
	return state.checkPathBetweenInstructions(sourceInstr, dest)

}

func (state *IntraAnalysisState) checkPathBetweenInstructions(source ssa.Instruction,
	dest ssa.Instruction) ConditionInfo {
	var sourceIndex, destIndex int
	for k, instr := range source.Block().Instrs {
		if instr == source {
			sourceIndex = k
		}
		if instr == dest {
			destIndex = k
		}
	}

	if source.Block().Index == dest.Block().Index && sourceIndex < destIndex {
		n := newImpossiblePath()
		n.Cond.Satisfiable = true
		return ConditionInfo{Satisfiable: true}
	}

	pos := IndexT(source.Block().Index)*state.flowInfo.NumBlocks + IndexT(dest.Block().Index)
	if c := state.paths[pos]; c != nil {
		return *c
	}
	b := FindIntraProceduralPath(source, dest)
	state.paths[pos] = &b.Cond
	return b.Cond
}

// isCapturedBy checks the bounding analysis to query whether the value is captured by some closure, in which case an
// edge will need to be added
// Guarantees that all label values in the slice of pointer labels returned are non-nil.
func (state *IntraAnalysisState) isCapturedBy(value ssa.Value) []*pointer.Label {
	var maps []*pointer.Label
	if ptr, ok := state.parentAnalyzerState.PointerAnalysis.Queries[value]; ok {
		for _, label := range ptr.PointsTo().Labels() {
			if label == nil || label.Value() == nil {
				continue
			}
			_, isBound := state.parentAnalyzerState.BoundingInfo[label.Value()]
			if isBound {
				maps = append(maps, label)
			}
		}
	}
	if ptr, ok := state.parentAnalyzerState.PointerAnalysis.IndirectQueries[value]; ok {
		for _, label := range ptr.PointsTo().Labels() {
			if label == nil || label.Value() == nil {
				continue
			}
			_, isBound := state.parentAnalyzerState.BoundingInfo[label.Value()]
			if isBound {
				maps = append(maps, label)
			}
		}
	}
	return maps
}

// ============================================================================
// Immutable Analysis Part
// ============================================================================

// ImmutableAnalysisResult contains the results of analyzing which parameters are immutable
type ImmutableAnalysisResult struct {
	IsSatisfied  bool             // Whether the immutable condition is satisfied
	NoLHSParams  []*ssa.Parameter // Parameters that should never appear on LHS
	NoRHSParams  []*ssa.Parameter // Parameters that should never appear on RHS
	NoFlowParams []*ssa.Parameter // Parameters that should have no flows at all
}

// immutableAnalysisResult contains the results of analyzing which parameters are immutable
type immutableAnalysisResult struct {
	IsSatisfied  bool             // Whether the immutable condition is satisfied
	NoLHSParams  []*ssa.Parameter // Parameters that should never appear on LHS
	NoRHSParams  []*ssa.Parameter // Parameters that should never appear on RHS
	NoFlowParams []*ssa.Parameter // Parameters that should have no flows at all
}

// IsSpecSatisfyImmutable checks if the summary satisfies the immutable specification
// by comparing it against a full flow summary where every parameter can flow to every other parameter and return
func IsSpecSatisfyImmutable(summaryUnderCheck *SummaryGraph) ImmutableAnalysisResult {
	result := ImmutableAnalysisResult{
		IsSatisfied:  false,
		NoLHSParams:  []*ssa.Parameter{},
		NoRHSParams:  []*ssa.Parameter{},
		NoFlowParams: []*ssa.Parameter{},
	}

	if summaryUnderCheck == nil || summaryUnderCheck.Parent == nil {
		return result
	}

	// Create a full flow summary where every parameter can flow to every other parameter and return
	fullFlowSummary := createFullFlowSummary(summaryUnderCheck)
	if fullFlowSummary == nil {
		return result
	}

	// Compare the summaries to find missing flows
	missingFlows := findMissingFlows(summaryUnderCheck, fullFlowSummary)

	// Categorize the missing flows to see if they fit the immutable pattern
	if categorizeImmutableFlows(summaryUnderCheck, missingFlows, &result) {
		result.IsSatisfied = true
	}

	return result
}

// CheckParametersImmutableInSSA verifies that the identified immutable parameters
// don't actually appear in SSA instructions where they shouldn't
func CheckParametersImmutableInSSA(result ImmutableAnalysisResult, function *ssa.Function) (bool, string) {
	if !result.IsSatisfied {
		return false, "immutable analysis not satisfied"
	}

	// Create sets for efficient lookup
	noLHSSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoLHSParams {
		noLHSSet[param] = true
	}

	noRHSSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoRHSParams {
		noRHSSet[param] = true
	}

	noFlowSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoFlowParams {
		noFlowSet[param] = true
	}

	// Iterate through all instructions in the function
	for _, block := range function.Blocks {
		for _, instr := range block.Instrs {
			// Check if parameters appear where they shouldn't

			// Check LHS (assignment targets) - these are instructions that define values
			if value, ok := instr.(ssa.Value); ok {
				// If this instruction defines a value that's a parameter that should never be on LHS
				if param, isParam := value.(*ssa.Parameter); isParam && noLHSSet[param] {
					return false, fmt.Sprintf("no-LHS parameter %s appears on LHS but should not", param.Name())
				}
				if param, isParam := value.(*ssa.Parameter); isParam && noFlowSet[param] {
					return false, fmt.Sprintf("no-flow parameter %s appears in instruction", param.Name())
				}
			}

			// Check RHS (operands/sources)
			var operands []*ssa.Value
			operands = instr.Operands(operands)
			for _, operand := range operands {
				if operand != nil {
					if param, isParam := (*operand).(*ssa.Parameter); isParam {
						// NoFlowParams should never appear anywhere
						if noFlowSet[param] {
							return false, fmt.Sprintf("no-flow parameter %s appears as operand", param.Name())
						}
						// NoLHSParams can appear as operands for operations like pointer dereferencing
						// They just shouldn't appear as sources in dataflows
						// NoRHSParams can appear as operands - they just never appear as targets in flows
					}
				}
			}
		}
	}

	return true, "all immutable parameters verified in SSA"
}

// createFullFlowSummary creates a summary where every parameter flows to every other parameter and return
func createFullFlowSummary(original *SummaryGraph) *SummaryGraph {
	if original == nil || original.Parent == nil {
		return nil
	}

	// Create a simple summary structure
	fullSummary := &SummaryGraph{
		ID:      original.ID,
		Parent:  original.Parent,
		Params:  make(map[ssa.Node]*ParamNode),
		Returns: make(map[ssa.Instruction][]*ReturnValNode),
	}

	// Copy parameters
	for node, paramNode := range original.Params {
		newParamNode := &ParamNode{
			id:      paramNode.id,
			parent:  fullSummary,
			ssaNode: paramNode.ssaNode,
			argPos:  paramNode.argPos,
			out:     make(map[GraphNode][]EdgeInfo),
			in:      make(map[GraphNode]EdgeInfo),
		}
		fullSummary.Params[node] = newParamNode
	}

	// Copy returns
	for instr, returnNodes := range original.Returns {
		newReturnNodes := make([]*ReturnValNode, len(returnNodes))
		for i, retNode := range returnNodes {
			if retNode != nil {
				newRetNode := &ReturnValNode{
					id:     retNode.id,
					parent: fullSummary,
					index:  retNode.index,
					in:     make(map[GraphNode]EdgeInfo),
					out:    make(map[GraphNode][]EdgeInfo),
				}
				newReturnNodes[i] = newRetNode
			}
		}
		fullSummary.Returns[instr] = newReturnNodes
	}

	// Create full connectivity: every parameter flows to every other parameter and return
	allTargets := []GraphNode{}

	// Add all parameters as targets
	for _, paramNode := range fullSummary.Params {
		allTargets = append(allTargets, paramNode)
	}

	// Add all return nodes as targets
	for _, returnNodes := range fullSummary.Returns {
		for _, retNode := range returnNodes {
			if retNode != nil {
				allTargets = append(allTargets, retNode)
			}
		}
	}

	// Create edges from every parameter to every target (including other parameters and returns)
	for _, sourceParam := range fullSummary.Params {
		for _, target := range allTargets {
			if sourceParam != target { // Avoid self-loops
				edgeInfo := EdgeInfo{
					RelPath: map[string]map[string]bool{"*": {"": true}},
					Index:   0,
					Cond:    nil,
				}
				sourceParam.out[target] = []EdgeInfo{edgeInfo}
				target.In()[sourceParam] = edgeInfo
			}
		}
	}

	return fullSummary
}

// findMissingFlows identifies flows that exist in the full summary but not in the summary under check
func findMissingFlows(summaryUnderCheck, fullFlowSummary *SummaryGraph) map[string]bool {
	missingFlows := make(map[string]bool)

	// Get flows from both summaries
	actualFlows := extractParameterFlows(summaryUnderCheck)
	fullFlows := extractParameterFlows(fullFlowSummary)

	// Find flows that exist in full but not in actual
	for flow := range fullFlows {
		if !actualFlows[flow] {
			missingFlows[flow] = true
		}
	}

	return missingFlows
}

// extractParameterFlows extracts parameter-to-parameter and parameter-to-return flows
func extractParameterFlows(summary *SummaryGraph) map[string]bool {
	flows := make(map[string]bool)

	if summary == nil {
		return flows
	}

	for _, paramNode := range summary.Params {
		// Check direct outgoing flows
		for target := range paramNode.Out() {
			// Only consider flows to parameters and returns
			switch target.(type) {
			case *ParamNode, *ReturnValNode:
				flowKey := fmt.Sprintf("%s -> %s", paramNode.String(), target.String())
				flows[flowKey] = true
			}
		}
	}

	return flows
}

// categorizeImmutableFlows analyzes missing flows to see if they fit immutable patterns
func categorizeImmutableFlows(summary *SummaryGraph, missingFlows map[string]bool, result *ImmutableAnalysisResult) bool {

	if len(missingFlows) == 0 {
		return true // No missing flows means it's already complete
	}

	// Track which parameters appear as sources or targets in actual flows
	paramsAsSource := make(map[*ssa.Parameter]bool)
	paramsAsTarget := make(map[*ssa.Parameter]bool)
	paramsUsedInSSA := make(map[*ssa.Parameter]bool)
	allParams := make(map[*ssa.Parameter]bool)

	// Initialize all parameters
	for _, paramNode := range summary.Params {
		param := paramNode.SsaNode()
		allParams[param] = true
	}

	// Check SSA instructions to see which parameters are actually used
	if summary.Parent != nil {
		for _, block := range summary.Parent.Blocks {
			for _, instr := range block.Instrs {
				// Check operands (RHS usage)
				var operands []*ssa.Value
				operands = instr.Operands(operands)
				for _, operand := range operands {
					if operand != nil {
						if param, isParam := (*operand).(*ssa.Parameter); isParam {
							paramsUsedInSSA[param] = true
						}
					}
				}

				// Check if the instruction defines a parameter (unusual but possible)
				if value, ok := instr.(ssa.Value); ok {
					if param, isParam := value.(*ssa.Parameter); isParam {
						paramsUsedInSSA[param] = true
					}
				}
			}
		}
	}

	// Check actual flows in the summary to categorize parameter usage
	actualFlows := extractParameterFlows(summary)

	for flow := range actualFlows {
		parts := parseFlowString(flow)
		if len(parts) != 2 {
			continue
		}

		sourceParam := findParameterByString(summary, parts[0])
		targetParam := findParameterByString(summary, parts[1])

		if sourceParam != nil {
			paramsAsSource[sourceParam] = true
		}
		if targetParam != nil {
			paramsAsTarget[targetParam] = true
		}
	}

	// Check missing flows to detect mutual parameter flow (indicating mutability)
	// Only mark a parameter as target if there's actual evidence of mutual flow
	for flow := range missingFlows {
		parts := parseFlowString(flow)
		if len(parts) != 2 {
			continue
		}

		sourceParam := findParameterByString(summary, parts[0])
		targetParam := findParameterByString(summary, parts[1])

		// Only mark as target if BOTH parameters appear as sources AND
		// there are actual flows between parameters (not just to returns)
		if sourceParam != nil && targetParam != nil &&
			paramsAsSource[sourceParam] && paramsAsSource[targetParam] {

			// Check if there are any actual parameter-to-parameter flows
			hasParamToParamFlow := false
			for actualFlow := range actualFlows {
				actualParts := parseFlowString(actualFlow)
				if len(actualParts) == 2 {
					actualSourceParam := findParameterByString(summary, actualParts[0])
					actualTargetParam := findParameterByString(summary, actualParts[1])
					if actualSourceParam != nil && actualTargetParam != nil {
						hasParamToParamFlow = true
						break
					}
				}
			}

			// Only mark as target if there are actual parameter-to-parameter flows
			// This indicates true mutability, not just source-only parameters
			if hasParamToParamFlow {
				paramsAsTarget[targetParam] = true
			}
		}
	}

	// Categorize parameters based on their usage patterns
	neverSourceParams := make(map[*ssa.Parameter]bool) // NoLHSParams - never appear as sources
	neverTargetParams := make(map[*ssa.Parameter]bool) // NoRHSParams - never appear as targets
	neverUsedParams := make(map[*ssa.Parameter]bool)   // NoFlowParams - never appear in any flows

	for param := range allParams {
		isSource := paramsAsSource[param]
		isTarget := paramsAsTarget[param]
		usedInSSA := paramsUsedInSSA[param]

		if !usedInSSA {
			// Parameter is never used in SSA instructions at all
			neverUsedParams[param] = true
		} else if !isSource && !isTarget {
			// Parameter is used in SSA but doesn't participate in parameter flows
			// This likely means it's target-only (like pointer parameters being written to)
			neverSourceParams[param] = true
		} else if isTarget && !isSource {
			// Parameter only appears as target in flows, never as source
			neverSourceParams[param] = true
		} else if isSource && !isTarget {
			// Parameter only appears as source in flows, never as target
			neverTargetParams[param] = true
		} else if isSource && isTarget {
			// Parameter appears as both source and target, it's mutable (not immutable)
			return false
		}
	}

	// Check if all missing flows can be explained by immutable patterns
	for flow := range missingFlows {
		parts := parseFlowString(flow)
		if len(parts) != 2 {
			return false // Invalid flow string
		}

		sourceParam := findParameterByString(summary, parts[0])
		targetParam := findParameterByString(summary, parts[1])
		isReturnFlow := strings.Contains(parts[1], "return")

		// Check if this missing flow fits an immutable pattern
		validImmutableFlow := false

		// Case 1: Source parameter never flows anywhere (never-source/never-used)
		if sourceParam != nil && (neverSourceParams[sourceParam] || neverUsedParams[sourceParam]) {
			validImmutableFlow = true
		}

		// Case 2: Target parameter is never flowed to (never-target/never-used)
		if targetParam != nil && (neverTargetParams[targetParam] || neverUsedParams[targetParam]) {
			validImmutableFlow = true
		}

		// Case 3: Flow to return from parameters that are never sources or never used
		if isReturnFlow && sourceParam != nil && (neverSourceParams[sourceParam] || neverUsedParams[sourceParam]) {
			validImmutableFlow = true
		}

		if !validImmutableFlow {
			return false // This missing flow doesn't fit immutable patterns
		}
	}

	// Fill in the result with categorized parameters
	for param := range neverSourceParams {
		result.NoLHSParams = append(result.NoLHSParams, param)
	}

	for param := range neverTargetParams {
		result.NoRHSParams = append(result.NoRHSParams, param)
	}

	for param := range neverUsedParams {
		result.NoFlowParams = append(result.NoFlowParams, param)
	}

	return true
}

// IsSpecSatisfyimmutable checks if the summary satisfies the immutable specification
// by comparing it against a full flow summary where every parameter can flow to every other parameter and return
// The immutable condition means: if the summaryUnderCheck compares to the full flow summary,
// the missing dataflows are all like: some parameters never flow to other parameters, or it's never flowed to.
// Only when ALL the missing dataflows are in this format, we could make the check true.
func IsSpecSatisfyimmutable(summaryUnderCheck *SummaryGraph) immutableAnalysisResult {
	result := immutableAnalysisResult{
		IsSatisfied:  false,
		NoLHSParams:  []*ssa.Parameter{},
		NoRHSParams:  []*ssa.Parameter{},
		NoFlowParams: []*ssa.Parameter{},
	}

	if summaryUnderCheck == nil || summaryUnderCheck.Parent == nil {
		return result
	}

	// Create a full flow summary where every parameter can flow to every other parameter and return
	fullFlowSummary := createFullFlowSummary(summaryUnderCheck)
	if fullFlowSummary == nil {
		return result
	}

	// Compare the summaries to find missing flows
	missingFlows := findMissingFlows(summaryUnderCheck, fullFlowSummary)

	// Categorize the missing flows to see if they fit the immutable pattern
	if categorizeimmutableFlows(summaryUnderCheck, missingFlows, &result) {
		result.IsSatisfied = true
	}

	return result
}

// CheckParametersimmutableInSSA verifies that the identified immutable parameters
// don't actually appear in SSA instructions where they shouldn't
func CheckParametersimmutableInSSA(result immutableAnalysisResult, function *ssa.Function) (bool, string) {
	if !result.IsSatisfied {
		return false, "immutable analysis not satisfied"
	}

	// Create sets for efficient lookup
	noLHSSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoLHSParams {
		noLHSSet[param] = true
	}

	noRHSSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoRHSParams {
		noRHSSet[param] = true
	}

	noFlowSet := make(map[*ssa.Parameter]bool)
	for _, param := range result.NoFlowParams {
		noFlowSet[param] = true
	}

	// Iterate through all instructions in the function
	for _, block := range function.Blocks {
		for _, instr := range block.Instrs {
			// Check if parameters appear where they shouldn't

			// Check LHS (assignment targets) - these are instructions that define values
			if value, ok := instr.(ssa.Value); ok {
				// If this instruction defines a value that's a parameter that should never be on LHS
				if param, isParam := value.(*ssa.Parameter); isParam && noLHSSet[param] {
					return false, fmt.Sprintf("no-LHS parameter %s appears on LHS but should not", param.Name())
				}
				if param, isParam := value.(*ssa.Parameter); isParam && noFlowSet[param] {
					return false, fmt.Sprintf("no-flow parameter %s appears in instruction", param.Name())
				}
			}

			// Check RHS (operands/sources)
			var operands []*ssa.Value
			operands = instr.Operands(operands)
			for _, operand := range operands {
				if operand != nil {
					if param, isParam := (*operand).(*ssa.Parameter); isParam {
						// NoFlowParams should never appear anywhere
						if noFlowSet[param] {
							return false, fmt.Sprintf("no-flow parameter %s appears as operand", param.Name())
						}
						// NoRHSParams should never appear on the right-hand side
						if noRHSSet[param] {
							return false, fmt.Sprintf("no-RHS parameter %s appears as operand", param.Name())
						}
					}
				}
			}
		}
	}

	return true, "all immutable parameters verified in SSA"
}

// categorizeimmutableFlows analyzes missing flows to see if they fit immutable patterns
// The immutable pattern is stricter than immutable: parameters must either never flow out
// OR never be flowed to, creating a clear separation of dataflow responsibilities
func categorizeimmutableFlows(summary *SummaryGraph, missingFlows map[string]bool, result *immutableAnalysisResult) bool {
	if len(missingFlows) == 0 {
		return true // No missing flows means it's already complete
	}

	// Track which parameters appear as sources or targets in actual flows
	paramsAsSource := make(map[*ssa.Parameter]bool)
	paramsAsTarget := make(map[*ssa.Parameter]bool)
	paramsUsedInSSA := make(map[*ssa.Parameter]bool)
	allParams := make(map[*ssa.Parameter]bool)

	// Initialize all parameters
	for _, paramNode := range summary.Params {
		param := paramNode.SsaNode()
		allParams[param] = true
	}

	// Check SSA instructions to see which parameters are actually used
	if summary.Parent != nil {
		for _, block := range summary.Parent.Blocks {
			for _, instr := range block.Instrs {
				// Check operands (RHS usage)
				var operands []*ssa.Value
				operands = instr.Operands(operands)
				for _, operand := range operands {
					if operand != nil {
						if param, isParam := (*operand).(*ssa.Parameter); isParam {
							paramsUsedInSSA[param] = true
						}
					}
				}

				// Check if the instruction defines a parameter (unusual but possible)
				if value, ok := instr.(ssa.Value); ok {
					if param, isParam := value.(*ssa.Parameter); isParam {
						paramsUsedInSSA[param] = true
					}
				}
			}
		}
	}

	// Check actual flows in the summary to categorize parameter usage
	actualFlows := extractParameterFlows(summary)

	for flow := range actualFlows {
		parts := parseFlowString(flow)
		if len(parts) != 2 {
			continue
		}

		sourceParam := findParameterByString(summary, parts[0])
		targetParam := findParameterByString(summary, parts[1])

		if sourceParam != nil {
			paramsAsSource[sourceParam] = true
		}
		if targetParam != nil {
			paramsAsTarget[targetParam] = true
		}
	}

	// Categorize parameters based on their usage patterns for immutable analysis
	// For immutable: parameters must be strictly categorized - no mixing of roles
	neverSourceParams := make(map[*ssa.Parameter]bool) // NoLHSParams - never appear as sources (input-only)
	neverTargetParams := make(map[*ssa.Parameter]bool) // NoRHSParams - never appear as targets (output-only)
	neverUsedParams := make(map[*ssa.Parameter]bool)   // NoFlowParams - never appear in any flows

	for param := range allParams {
		isSource := paramsAsSource[param]
		isTarget := paramsAsTarget[param]
		usedInSSA := paramsUsedInSSA[param]

		if !usedInSSA {
			// Parameter is never used in SSA instructions at all
			neverUsedParams[param] = true
		} else if !isSource && !isTarget {
			// Parameter is used in SSA but doesn't participate in dataflow at all
			neverUsedParams[param] = true
		} else if isTarget && !isSource {
			// Parameter only appears as target in flows, never as source (input-only)
			neverSourceParams[param] = true
		} else if isSource && !isTarget {
			// Parameter only appears as source in flows, never as target (output-only)
			neverTargetParams[param] = true
		} else if isSource && isTarget {
			// Parameter appears as both source and target - this violates immutable pattern
			// In immutable analysis, parameters should have strict roles
			return false
		}
	}

	// For immutable analysis: ALL missing flows must be explainable by strict parameter roles
	for flow := range missingFlows {
		parts := parseFlowString(flow)
		if len(parts) != 2 {
			return false // Invalid flow string
		}

		sourceParam := findParameterByString(summary, parts[0])
		targetParam := findParameterByString(summary, parts[1])
		isReturnFlow := strings.Contains(parts[1], "return")

		// Check if this missing flow fits the immutable pattern
		validimmutableFlow := false

		// Case 1: Source parameter never flows anywhere (never-source/never-used)
		if sourceParam != nil && (neverSourceParams[sourceParam] || neverUsedParams[sourceParam]) {
			validimmutableFlow = true
		}

		// Case 2: Target parameter is never flowed to (never-target/never-used)
		if targetParam != nil && (neverTargetParams[targetParam] || neverUsedParams[targetParam]) {
			validimmutableFlow = true
		}

		// Case 3: Flow to return from parameters that are never sources or never used
		if isReturnFlow && sourceParam != nil && (neverSourceParams[sourceParam] || neverUsedParams[sourceParam]) {
			validimmutableFlow = true
		}

		// Case 4: Parameter-to-parameter flows where one is input-only and other is output-only
		if sourceParam != nil && targetParam != nil {
			sourceIsInputOnly := neverSourceParams[sourceParam] || neverUsedParams[sourceParam]
			targetIsOutputOnly := neverTargetParams[targetParam] || neverUsedParams[targetParam]
			if sourceIsInputOnly || targetIsOutputOnly {
				validimmutableFlow = true
			}
		}

		if !validimmutableFlow {
			return false // This missing flow doesn't fit immutable patterns
		}
	}

	// Fill in the result with categorized parameters
	for param := range neverSourceParams {
		result.NoLHSParams = append(result.NoLHSParams, param)
	}

	for param := range neverTargetParams {
		result.NoRHSParams = append(result.NoRHSParams, param)
	}

	for param := range neverUsedParams {
		result.NoFlowParams = append(result.NoFlowParams, param)
	}

	return true
}

// parseFlowString parses a flow string like "param1 -> param2" into [source, target]
func parseFlowString(flow string) []string {
	parts := strings.Split(flow, " -> ")
	if len(parts) != 2 {
		return []string{}
	}
	return []string{strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])}
}

// findParameterByString finds a parameter node by its string representation
func findParameterByString(summary *SummaryGraph, nodeStr string) *ssa.Parameter {
	for _, paramNode := range summary.Params {
		// Check if the node string exactly matches the parameter node string
		if paramNode.String() == nodeStr {
			return paramNode.SsaNode()
		}

		// More precise parameter matching using the parameter name and position
		if strings.Contains(nodeStr, "parameter") {
			paramName := paramNode.SsaNode().Name()
			// Look for the parameter name followed by " : " (parameter type separator)
			// or parameter name followed by " of " (parameter of function)
			if strings.Contains(nodeStr, "parameter "+paramName+" :") ||
				strings.Contains(nodeStr, "parameter "+paramName+" of") {
				return paramNode.SsaNode()
			}
		}
	}
	return nil
}

// ShouldBuildSummary returns true if the function's summary should be *built* during the single function analysis
// pass. This is not necessary for functions that have summaries that are externally defined, for example.
//
// ShouldBuildSummary returns true when:
//   - the state, the function or the function's package is nil (nil function must be handled by summary builder)
//   - the function summary is always required, as specified by [summaries.IsSummaryRequired]
//   - summaries are not built on demand
//   - the function is not filtered out by the pkg-filter (i.e. the pkg-filter matches the function when present)
//   - the function is not already summarized by a predefined summary or has an external contract
func ShouldBuildSummary(state *State, function *ssa.Function) bool {
	if state.Config != nil && state.Config.SummarizeOnDemand {
		return false
	}

	if state == nil || function == nil || summaries.IsSummaryRequired(function) {
		return true
	}

	pkg := function.Package()
	if pkg == nil {
		return true
	}

	// Is PkgPrefix specified?
	if state.Config != nil && state.Config.PkgFilter != "" {
		pkgKey := pkg.Pkg.Path()
		return state.Config.MatchPkgFilter(pkgKey) || pkgKey == "command-line-arguments"
	}
	// Check package summaries
	return !(summaries.PkgHasSummaries(pkg) || state.HasExternalContractSummary(function))
}

// ============================================================================
// Lightweight Reaching Definition Analysis
// ============================================================================

// PerformLightweightReachingDefinition performs lightweight reaching definition analysis
// using SSA properties directly, without calling RunIntraProcedural
func PerformLightweightReachingDefinition(state *State, function *ssa.Function) map[ssa.Value]map[*ssa.Parameter]bool {
	// Map from SSA value to set of parameters that can reach it
	reachingDefs := make(map[ssa.Value]map[*ssa.Parameter]bool)

	// Initialize parameters - each parameter reaches itself
	for _, param := range function.Params {
		reachingDefs[param] = map[*ssa.Parameter]bool{param: true}
	}

	// Initialize free variables (for closures)
	for _, fv := range function.FreeVars {
		reachingDefs[fv] = make(map[*ssa.Parameter]bool)
		// Free variables don't come from parameters, so they start empty
	}

	// Walk through all blocks in the function
	for _, block := range function.Blocks {
		AnalyzeBlockForReachingDefs(state, block, reachingDefs)
	}

	return reachingDefs
}

// AnalyzeBlockForReachingDefs analyzes a single basic block for reaching definitions
func AnalyzeBlockForReachingDefs(state *State, block *ssa.BasicBlock, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	for _, instr := range block.Instrs {
		AnalyzeInstructionForReachingDefs(state, instr, reachingDefs)
	}
}

// AnalyzeInstructionForReachingDefs analyzes a single SSA instruction for reaching definitions
func AnalyzeInstructionForReachingDefs(state *State, instr ssa.Instruction, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	switch inst := instr.(type) {
	case *ssa.Phi:
		// φ-node: merge reaching definitions from all edges
		HandlePhiInstruction(state, inst, reachingDefs)

	case *ssa.UnOp, *ssa.BinOp, *ssa.Convert, *ssa.ChangeType, *ssa.ChangeInterface:
		// Unary/binary operations: reaching defs flow through operands
		if val, ok := instr.(ssa.Value); ok {
			HandleArithmeticInstruction(state, val, reachingDefs)
		}

	case *ssa.Extract, *ssa.Field, *ssa.FieldAddr, *ssa.Index, *ssa.IndexAddr, *ssa.Slice:
		// Field/index access: reaching defs flow through the accessed value
		if val, ok := instr.(ssa.Value); ok {
			HandleAccessInstruction(state, val, reachingDefs)
		}

	case *ssa.MakeInterface, *ssa.MakeSlice, *ssa.MakeMap, *ssa.MakeChan:
		// Make operations: reaching defs flow through operands
		if val, ok := instr.(ssa.Value); ok {
			HandleMakeInstruction(state, val, reachingDefs)
		}

	case ssa.CallInstruction:
		// Function calls: ignore internal effects (lightweight analysis)
		// Only consider direct parameter passthrough for simple cases
		HandleCallInstruction(state, inst, reachingDefs)

	case *ssa.Alloc:
		// Allocation creates new value with no reaching parameters
		reachingDefs[inst] = make(map[*ssa.Parameter]bool)

	case *ssa.Store:
		// Store instruction: doesn't create a value, just updates memory
		// We ignore stores in this lightweight analysis

	case *ssa.Return:
		// Return instruction: we'll handle this when building the summary
		// No new value created by return

	default:
		// For unknown instructions that create values, assume no parameters reach them
		if val, ok := instr.(ssa.Value); ok {
			if _, exists := reachingDefs[val]; !exists {
				reachingDefs[val] = make(map[*ssa.Parameter]bool)
			}
		}
	}
}

// HandlePhiInstruction handles φ-nodes by merging reaching definitions from all incoming edges
func HandlePhiInstruction(state *State, phi *ssa.Phi, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	merged := make(map[*ssa.Parameter]bool)

	// Merge reaching definitions from all edges
	for _, edge := range phi.Edges {
		if sourceDefs, exists := reachingDefs[edge]; exists {
			for param := range sourceDefs {
				merged[param] = true
			}
		}
	}

	reachingDefs[phi] = merged
}

// HandleArithmeticInstruction handles arithmetic operations by propagating reaching definitions from operands
func HandleArithmeticInstruction(state *State, val ssa.Value, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	merged := make(map[*ssa.Parameter]bool)

	// Get operands from the instruction
	var operands []*ssa.Value
	operands = val.(ssa.Instruction).Operands(operands)

	// Merge reaching definitions from all operands
	for _, operand := range operands {
		if operand != nil {
			if sourceDefs, exists := reachingDefs[*operand]; exists {
				for param := range sourceDefs {
					merged[param] = true
				}
			}
		}
	}

	reachingDefs[val] = merged
}

// HandleAccessInstruction handles field/index access by propagating reaching definitions from accessed value
func HandleAccessInstruction(state *State, val ssa.Value, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	merged := make(map[*ssa.Parameter]bool)

	// Get operands from the instruction
	var operands []*ssa.Value
	operands = val.(ssa.Instruction).Operands(operands)

	// Usually the first operand is the accessed value
	if len(operands) > 0 && operands[0] != nil {
		if sourceDefs, exists := reachingDefs[*operands[0]]; exists {
			for param := range sourceDefs {
				merged[param] = true
			}
		}
	}

	reachingDefs[val] = merged
}

// HandleMakeInstruction handles make operations by propagating reaching definitions from operands
func HandleMakeInstruction(state *State, val ssa.Value, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	merged := make(map[*ssa.Parameter]bool)

	// Get operands from the instruction
	var operands []*ssa.Value
	operands = val.(ssa.Instruction).Operands(operands)

	// Merge reaching definitions from all operands
	for _, operand := range operands {
		if operand != nil {
			if sourceDefs, exists := reachingDefs[*operand]; exists {
				for param := range sourceDefs {
					merged[param] = true
				}
			}
		}
	}

	reachingDefs[val] = merged
}

// HandleCallInstruction handles function calls in a lightweight manner by ignoring internal call effects
func HandleCallInstruction(state *State, call ssa.CallInstruction, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	// For lightweight analysis, we ignore the internal effects of function calls
	// We could optionally handle simple cases like identity functions, but for now keep it minimal

	// If the call produces a value, assume it has no reaching parameters (conservative)
	if val, ok := call.(ssa.Value); ok {
		reachingDefs[val] = make(map[*ssa.Parameter]bool)
	}

	// Note: In a more sophisticated version, we might:
	// - Handle builtin functions specially (e.g., len, cap preserve their argument's reaching defs)
	// - Handle known pure functions that just pass through their arguments
	// But for lightweight analysis, we keep it simple
}

// BuildSummaryFromReachingDefs builds a summary graph from reaching definition analysis results
func BuildSummaryFromReachingDefs(state *State, summary *SummaryGraph, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	function := summary.Parent

	// Walk through all return instructions to see which parameters can reach returns
	for _, block := range function.Blocks {
		for _, instr := range block.Instrs {
			if ret, ok := instr.(*ssa.Return); ok {
				AddReturnFlowsFromReachingDefs(state, summary, ret, reachingDefs)
			}
		}
	}
}

// AddReturnFlowsFromReachingDefs adds flows from parameters to returns based on reaching definition analysis
func AddReturnFlowsFromReachingDefs(state *State, summary *SummaryGraph, ret *ssa.Return, reachingDefs map[ssa.Value]map[*ssa.Parameter]bool) {
	// For each return value, see which parameters can reach it
	for tupleIndex, returnVal := range ret.Results {
		if returnVal != nil {
			// Get the set of parameters that can reach this return value
			if reachingParams, exists := reachingDefs[returnVal]; exists {
				// Create return node if it doesn't exist
				if summary.Returns[ret] == nil {
					returnNodes := make([]*ReturnValNode, len(ret.Results))
					summary.Returns[ret] = returnNodes
				}

				// Create return node for this tuple index if it doesn't exist
				if summary.Returns[ret][tupleIndex] == nil {
					returnNode := &ReturnValNode{
						id:     summary.newNodeID(),
						parent: summary,
						index:  tupleIndex,
						in:     make(map[GraphNode]EdgeInfo),
						out:    make(map[GraphNode][]EdgeInfo),
					}
					summary.Returns[ret][tupleIndex] = returnNode
				}

				returnNode := summary.Returns[ret][tupleIndex]

				// Add flows from each reaching parameter to this return
				for param := range reachingParams {
					AddParameterToReturnFlow(state, summary, param, returnNode)
				}
			}
		}
	}
}

// AddParameterToReturnFlow adds a flow edge from a parameter to a return node
func AddParameterToReturnFlow(state *State, summary *SummaryGraph, param *ssa.Parameter, returnNode *ReturnValNode) {
	// Create parameter node if it doesn't exist
	if summary.Params[param] == nil {
		paramNode := &ParamNode{
			id:      summary.newNodeID(),
			parent:  summary,
			ssaNode: param,
			out:     make(map[GraphNode][]EdgeInfo),
			in:      make(map[GraphNode]EdgeInfo),
			argPos:  -1, // We could compute this, but for lightweight analysis it's not critical
		}
		summary.Params[param] = paramNode
	}

	paramNode := summary.Params[param]

	// Create edge info representing the flow
	edgeInfo := EdgeInfo{
		RelPath: map[string]map[string]bool{"": {"": true}}, // Direct flow
		Index:   0,
		Cond:    nil, // Unconditional flow
	}

	// Add outgoing edge from parameter to return
	if paramNode.out[returnNode] == nil {
		paramNode.out[returnNode] = []EdgeInfo{edgeInfo}
	} else {
		// Check if this edge already exists to avoid duplicates
		edgeExists := false
		for _, existingEdge := range paramNode.out[returnNode] {
			if compareEdgeInfoForReachingDefs(existingEdge, edgeInfo) {
				edgeExists = true
				break
			}
		}
		if !edgeExists {
			paramNode.out[returnNode] = append(paramNode.out[returnNode], edgeInfo)
		}
	}

	// Add incoming edge to return from parameter
	returnNode.in[paramNode] = edgeInfo
}

// compareEdgeInfoForReachingDefs compares two EdgeInfo structures for reaching definition analysis
func compareEdgeInfoForReachingDefs(ei1, ei2 EdgeInfo) bool {
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
	for inPath1, outPaths1 := range ei1.RelPath {
		outPaths2, exists := ei2.RelPath[inPath1]
		if !exists {
			return false
		}

		if len(outPaths1) != len(outPaths2) {
			return false
		}

		for outPath1 := range outPaths1 {
			if _, exists := outPaths2[outPath1]; !exists {
				return false
			}
		}
	}

	return true
}
