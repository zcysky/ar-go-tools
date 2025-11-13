package dataflow

import (
	"fmt"
	"go/types"
	"strings"

	"github.com/awslabs/ar-go-tools/internal/pointer"
	"golang.org/x/tools/go/ssa"
)

// StepwiseSoundnessEnabled controls whether the new 5-step pipeline is used.
// TODO: later expose via config; for now set true to exercise new logic.
const StepwiseSoundnessEnabled = true

// checkSummarySoundnessStepwise implements the new 5-step progressive elimination algorithm.
// It does NOT mutate existing legacy logic; it reuses existing helpers.
func (g *InterProceduralFlowGraph) checkSummarySoundnessStepwise(
	function *ssa.Function,
	summaryUnderCheck *SummaryGraph,
	recursionDepth int,
	visited map[*ssa.Function]bool,
	cache map[*ssa.Function]bool,
) (bool, string, map[*ssa.Function]*SummaryGraph) {
	// Safeguards & cache
	if result, cached := cache[function]; cached {
		return result, "cached", nil
	}
	if visited[function] {
		return true, "cycle assume sound", nil
	}
	if recursionDepth > 100 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		return true, "depth cap", nil
	}
	visited[function] = true
	defer delete(visited, function)

	// Step1: full-flow equality shortcut
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP1: MOST GENERAL] func=%s begin", function.String())
	}
	full := createFullFlowSummary(summaryUnderCheck)
	if g.compareSummaries(summaryUnderCheck, full) {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP1: MOST GENERAL] func=%s status=equals-full-flow -> SOUND", function.String())
		}
		summaryUnderCheck.IsSound = true
		cache[function] = true
		return true, "equals full-flow", nil
	}

	// Define Sg directly as S_full (complete param mutual connectivity + param->return)
	// We intentionally do NOT call createMostGeneralSummary here: the stepwise algorithm
	// derives soundness by progressively removing edges from this maximal set.
	Sg := full

	// Missing flows: parameter/return only
	missing := g.stepwiseFindMissing(summaryUnderCheck, Sg)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP1: MOST GENERAL] func=%s initial-missing=%d", function.String(), len(missing))
	}
	// With Sg = S_full and equality already excluded above, missing must be > 0 here.

	// Step2: simple type infeasible
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] func=%s start remaining=%d", function.String(), len(missing))
	}
	before := len(missing)
	missing = g.filterMissingSimpleType(missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] func=%s status=all-type-infeasible -> SOUND", function.String())
		}
		return true, "all type-infeasible", nil
	}

	// Step3: immutability-based pruning
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] func=%s start remaining=%d", function.String(), len(missing))
	}
	before = len(missing)
	missing = g.filterMissingImmutability(function, summaryUnderCheck, missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] func=%s status=cleared-by-immutability -> SOUND", function.String())
		}
		return true, "cleared by immutability", nil
	}

	// Step4: reaching-def with full-call assumption
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP4: REACH-DEFs] func=%s start remaining=%d", function.String(), len(missing))
	}
	before = len(missing)
	missing = g.filterMissingReachingFull(function, missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP4: REACH-DEFs] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP4: REACH-DEFs] func=%s status=cleared-by-reaching-full -> SOUND", function.String())
		}
		return true, "cleared by reaching(full)", nil
	}

	// Step5: recursive + subspec using remaining flows directly
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s start remaining=%d", function.String(), len(missing))
	}
	// Reuse existing machinery (identifyPotentialCalleeSubspecs expects NodePair slice from older path; we build mapping)
	rc := g.recursivelyCheckAllCallees(summaryUnderCheck, recursionDepth, visited, cache)
	options := g.identifyPotentialCalleeSubspecs(summaryUnderCheck, missing)
	if len(options) == 0 {
		if rc.CalleeCount == 0 { // leaf
			// For leaf internal: re-run intra-procedural
			if len(function.Blocks) > 0 && len(function.Blocks[0].Instrs) > 0 {
				if intra, err := g.PerformFreshDataflowAnalysis(function); err == nil && g.isSummarySubset(intra, summaryUnderCheck) {
					summaryUnderCheck.IsSound = true
					cache[function] = true
					return true, "leaf intra subset", nil
				}
			} else { // external leaf
				if g.isSummarySubset(summaryUnderCheck, Sg) {
					summaryUnderCheck.IsSound = true
					cache[function] = true
					return true, "external subset", nil
				}
			}
			return false, fmt.Sprintf("leaf residual=%d", len(missing)), nil
		}
		if rc.AllCalleesSound {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s fail missing=%d no-subspec-options", function.String(), len(missing))
			}
			return false, fmt.Sprintf("missing=%d no subspec options", len(missing)), nil
		}
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s fail missing=%d callee-unsound=%s", function.String(), len(missing), rc.FirstFailureReason)
		}
		return false, fmt.Sprintf("missing=%d callee unsound %s", len(missing), rc.FirstFailureReason), nil
	}
	cover := g.greedySetCoverAlgorithm(options, missing)
	if len(cover.Uncovered) > 0 {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s fail uncovered=%d after set-cover", function.String(), len(cover.Uncovered))
		}
		return false, fmt.Sprintf("uncovered=%d after set-cover", len(cover.Uncovered)), nil
	}
	deeper, err := g.generateSelectedSubspecsWithRecursiveCheck(summaryUnderCheck, cover, recursionDepth, visited, cache)
	if err != nil {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s fail recursive-subspec err=%v", function.String(), err)
		}
		return false, fmt.Sprintf("recursive subspec fail: %v", err), nil
	}
	summaryUnderCheck.IsSound = true
	cache[function] = true
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[STEP5: RECURSIVE] func=%s status=sound-via-subspec flows=%d callees=%d -> SOUND", function.String(), len(missing), len(deeper))
	}
	return true, fmt.Sprintf("sound via subspec (%d flows, %d callees)", len(missing), len(deeper)), deeper
}

// stepwiseFindMissing: collect parameter->parameter / parameter->return edges present in Sg but absent in Su
func (g *InterProceduralFlowGraph) stepwiseFindMissing(Su, Sg *SummaryGraph) []NodePair {
	var res []NodePair
	if Su == nil || Sg == nil {
		return res
	}
	// Build fast membership (sourceID,targetID) for Su
	suEdges := make(map[uint32]map[uint32]bool)
	Su.ForAllNodes(func(n GraphNode) {
		for tgt := range n.Out() {
			if suEdges[n.ID()] == nil {
				suEdges[n.ID()] = map[uint32]bool{}
			}
			suEdges[n.ID()][tgt.ID()] = true
		}
	})
	Sg.ForAllNodes(func(src GraphNode) {
		switch src.(type) {
		case *ParamNode, *ReturnValNode:
			for tgt := range src.Out() {
				switch tgt.(type) {
				case *ParamNode, *ReturnValNode:
					if !suEdges[src.ID()][tgt.ID()] {
						res = append(res, NodePair{Source: src, Target: tgt})
					}
				}
			}
		}
	})
	return res
}

// --- Step2 helpers ---
func (g *InterProceduralFlowGraph) filterMissingSimpleType(missing []NodePair) []NodePair {
	var out []NodePair
	for _, mp := range missing {
		st := g.nodeType(mp.Source)
		dt := g.nodeType(mp.Target)

		// CRITICAL: flows into return parameters should NEVER be pruned by simple type checks.
		// Even if types are not assignable or not pointer-like, functions can still produce
		// return values via conversions or intermediate computations.
		// We therefore keep ALL flows to return parameters regardless of any type analysis.
		if _, isReturn := mp.Target.(*ReturnValNode); isReturn {
			out = append(out, mp)
			continue
		}

		// NEW LOGIC: For param-to-param flows, if both types cannot point (are not pointer-like),
		// then there is no (non-local) dataflow between the two parameters inside the function.
		if sp, ok1 := mp.Source.(*ParamNode); ok1 {
			if tp, ok2 := mp.Target.(*ParamNode); ok2 {
				// Use CanPoint logic to check if types are pointer-like
				if st != nil && dt != nil {
					srcCanPoint := pointer.CanPoint(st)
					dstCanPoint := pointer.CanPoint(dt)

					if !srcCanPoint && !dstCanPoint {
						if g.AnalyzerState.Logger.LogsDebug() {
							g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] drop %s -> %s param-param both non-pointer-like", mp.Source.String(), mp.Target.String())
						}
						continue
					}
				}

				// Additional check: drop param->param edges whose types are not identical (positions differ) as infeasible
				if sp.argPos != tp.argPos {
					if st == nil || dt == nil || !types.Identical(st, dt) {
						if g.AnalyzerState.Logger.LogsDebug() {
							g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] drop %s -> %s param-param non-identical", mp.Source.String(), mp.Target.String())
						}
						continue
					}
				}
			}
		}

		// Apply other type-based feasibility checks (but only for non-return targets)
		if g.simpleTypeInfeasible(st, dt) {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[STEP2: SIMPLE TYPE] drop %s -> %s type-infeasible", mp.Source.String(), mp.Target.String())
			}
			continue
		}
		out = append(out, mp)
	}
	return out
}

func (g *InterProceduralFlowGraph) nodeType(n GraphNode) types.Type {
	switch x := n.(type) {
	case *ParamNode:
		return x.Type()
	case *ReturnValNode:
		return x.Type()
	}
	return nil
}
func (g *InterProceduralFlowGraph) simpleTypeInfeasible(src, dst types.Type) bool {
	if src == nil || dst == nil {
		return false
	}
	// Quick reject: not assignable & not convertible
	if !types.AssignableTo(src, dst) && !types.ConvertibleTo(src, dst) {
		return true
	}
	// Extra heuristic: value-type target vs pointer-rich source
	if g.isImmutableBasic(dst) && g.containsPointer(src) {
		return true
	}
	return false
}
func (g *InterProceduralFlowGraph) isImmutableBasic(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	if !ok {
		return false
	}
	switch b.Kind() {
	case types.Bool,
		types.Int, types.Int8, types.Int16, types.Int32, types.Int64,
		types.Uint, types.Uint8, types.Uint16, types.Uint32, types.Uint64, types.Uintptr,
		types.Float32, types.Float64,
		types.Complex64, types.Complex128,
		types.String:
		return true
	}
	return false
}
func (g *InterProceduralFlowGraph) containsPointer(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Pointer, *types.Slice, *types.Map, *types.Chan, *types.Signature, *types.Interface:
		return true
	case *types.Array:
		return g.containsPointer(u.Elem())
	case *types.Struct:
		for i := 0; i < u.NumFields(); i++ {
			if g.containsPointer(u.Field(i).Type()) {
				return true
			}
		}
	}
	return false
}

// --- Step3 immutability ---
func (g *InterProceduralFlowGraph) filterMissingImmutability(function *ssa.Function, summary *SummaryGraph, missing []NodePair) []NodePair {
	if function == nil || len(function.Params) == 0 {
		return missing
	}

	// Skip Step 3 for functions without SSA body (external/builtins),
	// to avoid misclassifying params as unused/unmodified due to missing referrers.
	if len(function.Blocks) == 0 {
		return missing
	}

	// Check if pointer analysis is available
	if g.AnalyzerState == nil || g.AnalyzerState.PointerAnalysis == nil {
		if g.AnalyzerState != nil && g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] func=%s fallback to simple analysis (no pointer analysis)", function.String())
		}
		return g.filterMissingImmutabilitySimple(function, missing)
	}

	// --- Step 3.1: Identify parameters that are never modified using pointer analysis ---
	unmodifiedParams := make(map[int]bool)
	for i, p := range function.Params {
		isModified := g.isParameterModifiedViaPointerAnalysis(p, function)
		if !isModified {
			unmodifiedParams[i] = true
		}
	}

	// --- Step 3.2: Identify parameters that are never read using pointer analysis ---
	unusedParams := make(map[int]bool)
	for i, p := range function.Params {
		isRead := g.isParameterReadViaPointerAnalysis(p, function)
		if !isRead {
			unusedParams[i] = true
		}
	}

	// --- Step 3.3: Filter missing flows ---
	var out []NodePair
	for _, mp := range missing {
		if src, ok := mp.Source.(*ParamNode); ok {
			if unusedParams[src.argPos] {
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] drop %s -> %s (source unused via pointer analysis)", mp.Source.String(), mp.Target.String())
				}
				continue
			}
		}
		if tgt, ok := mp.Target.(*ParamNode); ok {
			if unmodifiedParams[tgt.argPos] {
				if g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] drop %s -> %s (target unmodified via pointer analysis)", mp.Source.String(), mp.Target.String())
				}
				continue
			}
		}
		out = append(out, mp)
	}
	return out
}

// isParameterModifiedViaPointerAnalysis uses pointer analysis to determine if a parameter is modified
func (g *InterProceduralFlowGraph) isParameterModifiedViaPointerAnalysis(param ssa.Value, function *ssa.Function) bool {
	// Get the points-to set for the parameter
	paramAliases := g.getParameterAliasesViaPointerAnalysis(param)

	// Check all instructions in the function for modifications to any alias
	for _, block := range function.Blocks {
		for _, instr := range block.Instrs {
			if store, ok := instr.(*ssa.Store); ok {
				// Check if store address could alias the parameter
				storeAddr := store.Addr
				if g.valuesCouldAlias(param, storeAddr, paramAliases) {
					return true
				}
			}

			// Check for modification via function call (conservative)
			if call, ok := instr.(ssa.CallInstruction); ok {
				for _, arg := range call.Common().Args {
					if g.valuesCouldAlias(param, arg, paramAliases) {
						// Treat pointer-like arguments as potentially modifiable by calls
						if pointer.CanPoint(arg.Type()) {
							return true
						}
					}
				}
			}
		}
	}
	return false
}

// isParameterReadViaPointerAnalysis uses pointer analysis to determine if a parameter is read
func (g *InterProceduralFlowGraph) isParameterReadViaPointerAnalysis(param ssa.Value, function *ssa.Function) bool {
	paramAliases := g.getParameterAliasesViaPointerAnalysis(param)

	// Check all instructions in the function for reads of any alias
	for _, block := range function.Blocks {
		for _, instr := range block.Instrs {
			// Check store values (reading from parameter)
			if store, ok := instr.(*ssa.Store); ok {
				if g.valuesCouldAlias(param, store.Val, paramAliases) {
					return true
				}
			}

			// Check dereference operations
			if uop, ok := instr.(*ssa.UnOp); ok {
				if g.valuesCouldAlias(param, uop.X, paramAliases) {
					return true
				}
			}

			// Check function call arguments
			if call, ok := instr.(ssa.CallInstruction); ok {
				for _, arg := range call.Common().Args {
					if g.valuesCouldAlias(param, arg, paramAliases) {
						return true
					}
				}
			}

			// Check return statements
			if ret, ok := instr.(*ssa.Return); ok {
				for _, rv := range ret.Results {
					if g.valuesCouldAlias(param, rv, paramAliases) {
						return true
					}
				}
			}

			// Check phi nodes
			if phi, ok := instr.(*ssa.Phi); ok {
				for _, edge := range phi.Edges {
					if g.valuesCouldAlias(param, edge, paramAliases) {
						return true
					}
				}
			}
		}
	}
	return false
}

// getParameterAliasesViaPointerAnalysis collects all values that might alias with the parameter
func (g *InterProceduralFlowGraph) getParameterAliasesViaPointerAnalysis(param ssa.Value) map[ssa.Value]bool {
	aliases := make(map[ssa.Value]bool)
	aliases[param] = true

	// Get direct pointer information
	if ptr, exists := g.AnalyzerState.PointerAnalysis.Queries[param]; exists {
		// For each label in the points-to set, find other values that point to the same locations
		paramLabels := make(map[*pointer.Label]bool)
		for _, label := range ptr.PointsTo().Labels() {
			paramLabels[label] = true
		}

		// Find other values with overlapping points-to sets
		for value, otherPtr := range g.AnalyzerState.PointerAnalysis.Queries {
			if value == param {
				continue
			}
			for _, label := range otherPtr.PointsTo().Labels() {
				if paramLabels[label] {
					aliases[value] = true
					break
				}
			}
		}
	}

	// Get indirect pointer information
	if ptr, exists := g.AnalyzerState.PointerAnalysis.IndirectQueries[param]; exists {
		paramLabels := make(map[*pointer.Label]bool)
		for _, label := range ptr.PointsTo().Labels() {
			paramLabels[label] = true
		}

		for value, otherPtr := range g.AnalyzerState.PointerAnalysis.IndirectQueries {
			if value == param {
				continue
			}
			for _, label := range otherPtr.PointsTo().Labels() {
				if paramLabels[label] {
					aliases[value] = true
					break
				}
			}
		}
	}

	return aliases
}

// valuesCouldAlias checks if two values could alias based on pointer analysis
func (g *InterProceduralFlowGraph) valuesCouldAlias(val1, val2 ssa.Value, val1Aliases map[ssa.Value]bool) bool {
	if val1 == val2 {
		return true
	}

	// Check if val2 is in the precomputed aliases of val1
	if val1Aliases[val2] {
		return true
	}

	// Check direct pointer analysis queries
	if ptr1, exists1 := g.AnalyzerState.PointerAnalysis.Queries[val1]; exists1 {
		if ptr2, exists2 := g.AnalyzerState.PointerAnalysis.Queries[val2]; exists2 {
			// Check if points-to sets intersect
			labels1 := make(map[*pointer.Label]bool)
			for _, label := range ptr1.PointsTo().Labels() {
				labels1[label] = true
			}
			for _, label := range ptr2.PointsTo().Labels() {
				if labels1[label] {
					return true
				}
			}
		}
	}

	return false
}

// filterMissingImmutabilitySimple is the fallback implementation when pointer analysis is not available
func (g *InterProceduralFlowGraph) filterMissingImmutabilitySimple(function *ssa.Function, missing []NodePair) []NodePair {
	// --- Step 3.1: Identify parameters that are never modified (written to) using simple analysis ---
	unmodifiedParams := make(map[int]bool)
	for i, p := range function.Params {
		// Simple alias analysis: find all values derived from the parameter
		q := []ssa.Value{p}
		visited := map[ssa.Value]bool{p: true}
		isModified := false
		for len(q) > 0 {
			v := q[0]
			q = q[1:]

			if v.Referrers() == nil {
				continue
			}
			for _, instr := range *v.Referrers() {
				// Check for direct modification
				if store, ok := instr.(*ssa.Store); ok && store.Addr == v {
					isModified = true
					break
				}
				// Check for modification via function call (conservative)
				if call, ok := instr.(ssa.CallInstruction); ok {
					for _, arg := range call.Common().Args {
						if arg == v {
							// Treat only pointer-like arguments as modifiable by calls
							if g.containsPointer(v.Type()) {
								isModified = true
								break
							}
						}
					}
				}
				if isModified {
					break
				}

				// Follow aliases
				if val, ok := instr.(ssa.Value); ok {
					if !visited[val] {
						switch instr.(type) {
						case *ssa.FieldAddr, *ssa.IndexAddr, *ssa.ChangeType, *ssa.Convert, *ssa.UnOp:
							visited[val] = true
							q = append(q, val)
						}
					}
				}
			}
			if isModified {
				break
			}
		}
		if !isModified {
			unmodifiedParams[i] = true
		}
	}

	// --- Step 3.2: Identify parameters that are never read using simple analysis ---
	unusedParams := make(map[int]bool)
	for i, p := range function.Params {
		isRead := false
		q := []ssa.Value{p}
		visited := map[ssa.Value]bool{p: true}
		for len(q) > 0 && !isRead {
			v := q[0]
			q = q[1:]
			if v.Referrers() == nil {
				continue
			}
			for _, instr := range *v.Referrers() {
				// Reading cases
				if store, ok := instr.(*ssa.Store); ok {
					if store.Val == v { // value used as the stored value
						isRead = true
						break
					}
					// store.Addr == v is not a read
					continue
				}
				// Dereference read: *v
				if uop, ok := instr.(*ssa.UnOp); ok {
					if uop.X == v {
						isRead = true
						break
					}
				}
				if call, ok := instr.(ssa.CallInstruction); ok {
					for _, arg := range call.Common().Args {
						if arg == v {
							isRead = true
							break
						}
					}
					if isRead {
						break
					}
				}
				if ret, ok := instr.(*ssa.Return); ok {
					for _, rv := range ret.Results {
						if rv == v {
							isRead = true
							break
						}
					}
					if isRead {
						break
					}
				}
				if phi, ok := instr.(*ssa.Phi); ok {
					for _, edge := range phi.Edges {
						if edge == v {
							isRead = true
							break
						}
					}
					if isRead {
						break
					}
				}
				// Follow aliases
				if val, ok := instr.(ssa.Value); ok {
					if !visited[val] {
						switch instr.(type) {
						case *ssa.FieldAddr, *ssa.IndexAddr, *ssa.ChangeType, *ssa.Convert, *ssa.UnOp:
							visited[val] = true
							q = append(q, val)
						}
					}
				}
			}
		}
		if !isRead {
			unusedParams[i] = true
		}
	}

	// --- Step 3.3: Filter missing flows ---
	var out []NodePair
	for _, mp := range missing {
		if src, ok := mp.Source.(*ParamNode); ok {
			if unusedParams[src.argPos] {
				if g.AnalyzerState != nil && g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] drop %s -> %s (source unused)", mp.Source.String(), mp.Target.String())
				}
				continue
			}
		}
		if tgt, ok := mp.Target.(*ParamNode); ok {
			if unmodifiedParams[tgt.argPos] {
				if g.AnalyzerState != nil && g.AnalyzerState.Logger.LogsDebug() {
					g.AnalyzerState.Logger.Debugf("[STEP3: IMMUTABLE] drop %s -> %s (target unmodified)", mp.Source.String(), mp.Target.String())
				}
				continue
			}
		}
		out = append(out, mp)
	}
	return out
}

// --- Step4 reaching-def with full-call assumption ---
func (g *InterProceduralFlowGraph) filterMissingReachingFull(function *ssa.Function, missing []NodePair) []NodePair {
	if function == nil || len(missing) == 0 {
		return missing
	}
	// Skip Step 4 for functions without SSA body (external/builtins),
	// as we cannot determine parameter reachability without function body.
	if len(function.Blocks) == 0 {
		return missing
	}
	pCount := len(function.Params)
	// collect returns types length
	rCount := 0
	if function.Signature.Results() != nil {
		rCount = function.Signature.Results().Len()
	}
	reachPP := make([][]bool, pCount)
	reachPR := make([][]bool, pCount)
	for i := 0; i < pCount; i++ {
		reachPP[i] = make([]bool, pCount)
		reachPR[i] = make([]bool, rCount)
		reachPP[i][i] = true
	}
	used := make([]bool, pCount)
	for _, b := range function.Blocks {
		for _, instr := range b.Instrs {
			if call, ok := instr.(ssa.CallInstruction); ok {
				for _, a := range call.Common().Args {
					if p, ok2 := a.(*ssa.Parameter); ok2 {
						for idx, fp := range function.Params {
							if fp == p {
								used[idx] = true
								break
							}
						}
					}
				}
			}
		}
	}
	any := false
	for _, v := range used {
		if v {
			any = true
			break
		}
	}
	if any {
		for i := 0; i < pCount; i++ {
			for j := 0; j < pCount; j++ {
				if i != j {
					reachPP[i][j] = true
				}
			}
			for r := 0; r < rCount; r++ {
				reachPR[i][r] = true
			}
		}
	}
	var out []NodePair
	for _, pair := range missing {
		keep := true
		if src, ok := pair.Source.(*ParamNode); ok {
			si := src.argPos
			switch t := pair.Target.(type) {
			case *ParamNode:
				ti := t.argPos
				if si < pCount && ti < pCount && !reachPP[si][ti] {
					keep = false
				}
			case *ReturnValNode:
				ri := t.index
				if si < pCount && ri < rCount && !reachPR[si][ri] {
					keep = false
				}
			}
		}
		if !keep {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[STEP4: REACH-DEFs] drop unreachable %s -> %s", pair.Source.String(), pair.Target.String())
			}
			continue
		}
		out = append(out, pair)
	}
	return out
}

// nodeType pretty string (optional debug helper)
func (g *InterProceduralFlowGraph) nodeTypeStr(t types.Type) string {
	if t == nil {
		return "<nil>"
	}
	return strings.TrimSpace(t.String())
}
