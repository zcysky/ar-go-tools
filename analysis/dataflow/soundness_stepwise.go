package dataflow

import (
	"fmt"
	"go/types"
	"strings"

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
		g.AnalyzerState.Logger.Debugf("[SND STEP1] func=%s begin", function.String())
	}
	full := createFullFlowSummary(summaryUnderCheck)
	if g.compareSummaries(summaryUnderCheck, full) {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP1] func=%s status=equals-full-flow -> SOUND", function.String())
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
		g.AnalyzerState.Logger.Debugf("[SND STEP1] func=%s initial-missing=%d", function.String(), len(missing))
	}
	// With Sg = S_full and equality already excluded above, missing must be > 0 here.

	// Step2: simple type infeasible
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP2] func=%s start remaining=%d", function.String(), len(missing))
	}
	before := len(missing)
	missing = g.filterMissingSimpleType(missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP2] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP2] func=%s status=all-type-infeasible -> SOUND", function.String())
		}
		return true, "all type-infeasible", nil
	}

	// Step3: immutability-based pruning
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP3] func=%s start remaining=%d", function.String(), len(missing))
	}
	before = len(missing)
	missing = g.filterMissingImmutability(function, summaryUnderCheck, missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP3] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP3] func=%s status=cleared-by-immutability -> SOUND", function.String())
		}
		return true, "cleared by immutability", nil
	}

	// Step4: reaching-def with full-call assumption
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP4] func=%s start remaining=%d", function.String(), len(missing))
	}
	before = len(missing)
	missing = g.filterMissingReachingFull(function, missing)
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP4] func=%s removed=%d remain=%d", function.String(), before-len(missing), len(missing))
	}
	if len(missing) == 0 {
		summaryUnderCheck.IsSound = true
		cache[function] = true
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP4] func=%s status=cleared-by-reaching-full -> SOUND", function.String())
		}
		return true, "cleared by reaching(full)", nil
	}

	// Step5: recursive + subspec using remaining flows directly
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s start remaining=%d", function.String(), len(missing))
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
				g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s fail missing=%d no-subspec-options", function.String(), len(missing))
			}
			return false, fmt.Sprintf("missing=%d no subspec options", len(missing)), nil
		}
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s fail missing=%d callee-unsound=%s", function.String(), len(missing), rc.FirstFailureReason)
		}
		return false, fmt.Sprintf("missing=%d callee unsound %s", len(missing), rc.FirstFailureReason), nil
	}
	cover := g.greedySetCoverAlgorithm(options, missing)
	if len(cover.Uncovered) > 0 {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s fail uncovered=%d after set-cover", function.String(), len(cover.Uncovered))
		}
		return false, fmt.Sprintf("uncovered=%d after set-cover", len(cover.Uncovered)), nil
	}
	deeper, err := g.generateSelectedSubspecsWithRecursiveCheck(summaryUnderCheck, cover, recursionDepth, visited, cache)
	if err != nil {
		if g.AnalyzerState.Logger.LogsDebug() {
			g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s fail recursive-subspec err=%v", function.String(), err)
		}
		return false, fmt.Sprintf("recursive subspec fail: %v", err), nil
	}
	summaryUnderCheck.IsSound = true
	cache[function] = true
	if g.AnalyzerState.Logger.LogsDebug() {
		g.AnalyzerState.Logger.Debugf("[SND STEP5] func=%s status=sound-via-subspec flows=%d callees=%d -> SOUND", function.String(), len(missing), len(deeper))
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
		// NEW: drop param->param edges whose types are not identical (positions differ) as infeasible
		if sp, ok1 := mp.Source.(*ParamNode); ok1 {
			if tp, ok2 := mp.Target.(*ParamNode); ok2 && sp.argPos != tp.argPos {
				if st == nil || dt == nil || !types.Identical(st, dt) {
					if g.AnalyzerState.Logger.LogsDebug() {
						g.AnalyzerState.Logger.Debugf("[SND STEP2] drop %s -> %s param-param non-identical", mp.Source.String(), mp.Target.String())
					}
					continue
				}
			}
		}
		if g.simpleTypeInfeasible(st, dt) {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[SND STEP2] drop %s -> %s type-infeasible", mp.Source.String(), mp.Target.String())
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
	result := IsSpecSatisfyimmutable(summary)
	if !result.IsSatisfied {
		return missing
	}
	ok, _ := CheckParametersimmutableInSSA(result, function)
	if !ok {
		return missing
	}
	// Build param index map
	paramIndex := map[*ssa.Parameter]int{}
	for i, p := range function.Params {
		paramIndex[p] = i
	}
	imm := map[int]bool{}
	add := func(ps []*ssa.Parameter) {
		for _, p := range ps {
			if idx, ok := paramIndex[p]; ok {
				imm[idx] = true
			}
		}
	}
	add(result.NoLHSParams)
	add(result.NoRHSParams)
	add(result.NoFlowParams)
	isImm := func(n GraphNode) bool {
		if pn, ok := n.(*ParamNode); ok {
			return imm[pn.argPos]
		}
		return false
	}
	var out []NodePair
	for _, mp := range missing {
		if isImm(mp.Source) || isImm(mp.Target) {
			if g.AnalyzerState.Logger.LogsDebug() {
				g.AnalyzerState.Logger.Debugf("[SND STEP3] drop %s -> %s immut", mp.Source.String(), mp.Target.String())
			}
			continue
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
				g.AnalyzerState.Logger.Debugf("[SND STEP4] drop unreachable %s -> %s", pair.Source.String(), pair.Target.String())
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
