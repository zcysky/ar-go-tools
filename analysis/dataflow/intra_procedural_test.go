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

package dataflow_test

import (
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"testing"

	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/analysis/ptr"
	"github.com/awslabs/ar-go-tools/analysis/summaries"
	"github.com/awslabs/ar-go-tools/internal/analysistest"
	"github.com/awslabs/ar-go-tools/internal/funcutil/result"
	"golang.org/x/tools/go/ssa"
)

//gocyclo:ignore
func TestFunctionSummaries(t *testing.T) {
	dir := filepath.Join("testdata", "summaries")
	lp, err := analysistest.LoadTest(
		testfsys, dir, []string{}, analysistest.LoadTestOptions{ApplyRewrite: true}).Value()
	if err != nil {
		t.Fatalf("failed to load test: %v", err)
	}
	state, err := result.Bind(ptr.NewState(lp), dataflow.NewState).Value()
	if err != nil {
		t.Fatalf("failed to build analyzer state: %v", err)
	}
	numRoutines := runtime.NumCPU() - 1
	if numRoutines <= 0 {
		numRoutines = 1
	}

	dataflow.RunIntraProceduralPass(state, numRoutines, dataflow.IntraAnalysisParams{
		ShouldBuildSummary: dataflow.ShouldBuildSummary,
		ShouldTrack:        dataflow.IsNodeOfInterest,
	})

	if len(state.FlowGraph.Summaries) == 0 {
		t.Fatalf("analyzer state does not contain any summaries")
	}

	for function, summary := range state.FlowGraph.Summaries {
		summaryIds := map[uint32]dataflow.GraphNode{}
		// Check that summary's nodes all have different ids
		summary.ForAllNodes(func(n dataflow.GraphNode) {
			if x, ok := summaryIds[n.ID()]; ok && x != n {
				t.Errorf("node ids should be unique, but %d repeats: %s and %s [%t]", n.ID(), x, n, x == n)
			}
			summaryIds[n.ID()] = n
		})

		if function.Name() == "main" {
			ok := len(summary.Returns) == 0 // main does not return any data
			ok = ok && len(summary.Params) == 0
			ok = ok && len(summary.Callees) == 8 // 7 regular function calls + 1 closure
			if !ok {
				t.Errorf("main graph is not as expected")
			}
		}

		if function.Name() == "Bar" {
			ok := len(summary.Returns) == 1
			ok = ok && len(summary.Params) == 1
			ok = ok && len(summary.Callees) == 1
			if !ok {
				t.Errorf("Bar graph is not as expected")
			}
			for _, paramNode := range summary.Params {
				if len(paramNode.Out()) < 2 {
					t.Errorf("Bar parameter should only have at least two outgoing edges to a function call argument, but got: %v", paramNode.Out())
				}
				hasCallOrReturn := false
				for dest := range paramNode.Out() {
					_, isCallNodeArg := dest.(*dataflow.CallNodeArg)
					_, isReturnNode := dest.(*dataflow.ReturnValNode)
					if isCallNodeArg || isReturnNode {
						hasCallOrReturn = true
					}

					if len(dest.In()) < 1 {
						t.Errorf("Bar parameter outgoing edge have at least 1 incoming edge, but got: %v", dest.In())
					}
					hasParam := false
					for src := range dest.In() {
						if _, ok := src.(*dataflow.ParamNode); ok {
							hasParam = true
						}
					}
					if !hasParam {
						t.Errorf("Bar parameter outgoing edge's should have an incoming edge that is a parameter node, but got: %v", dest.In())
					}
				}
				if !hasCallOrReturn {
					t.Errorf("Bar parameter outgoing edge should have a CallNodeArg or ReturnNode, but got: %v", paramNode.Out())
				}
			}
		}

		if function.Name() == "Foo" {
			ok := len(summary.Returns) == 1
			ok = ok && len(summary.Params) == 3
			ok = ok && len(summary.Callees) == 2
			if !ok {
				t.Errorf("Foo graph is not as expected")
			}
			for _, paramNode := range summary.Params {
				if paramNode.SsaNode().Name() == "s" {
					if len(paramNode.Out()) < 1 {
						t.Errorf("in Foo, s should have at least one outgoing edge, but got: %v", paramNode.Out())
					}
					hasCall := false
					for out := range paramNode.Out() {
						if _, ok := out.(*dataflow.CallNodeArg); ok {
							hasCall = true
						}

						if len(out.In()) != 1 {
							t.Errorf("in Foo, the outgoing edge of param s should have one incoming edge, but got: %v", out.In())
						}

						for in := range out.In() {
							if _, ok := in.(*dataflow.ParamNode); !ok {
								t.Errorf(
									"in Foo, the incoming edge of the outgoing edge of param s should be a parameter node, but got: %T",
									in)
							}
						}
					}
					if !hasCall {
						t.Errorf("in Foo, an outgoing edge of param s should be a call node argument, but got: %v", paramNode.Out())
					}

					// even though there is a statement `a[0] = s` in the
					// function body of Foo, there are no incoming edges from
					// parameter s because s is never modified in Foo
					if len(paramNode.In()) != 0 {
						t.Errorf("in Foo, param s should not have any incoming edges, but got: %v", paramNode.In())
					}
				}
				if paramNode.SsaNode().Name() == "s2" {
					if len(paramNode.Out()) != 1 {
						t.Errorf("in Foo, s2 should have one outgoing edge, but got: %v", paramNode.Out())
					}
					for out := range paramNode.Out() {
						// statement `l := Bar(*s2)`
						if _, ok := out.(*dataflow.CallNodeArg); !ok {
							t.Errorf("in Foo, the outgoing edge of param s2 should be a call node argument, but got: %T", out)
						}

						if len(out.In()) != 2 {
							t.Errorf("in Foo, the outgoing edge of param s2 should have 2 incoming edges, but got: %v", out.In())
						}

						hasParam := false
						hasCall := false
						for in := range out.In() {
							if _, ok := in.(*dataflow.ParamNode); ok {
								hasParam = true
							}
							// statement `*s2 = obj.f(a[9])` comes before the call to `Bar(*s2)`
							if call, ok := in.(*dataflow.CallNode); ok {
								if call.FuncString() != "(command-line-arguments.A).f" && call.FuncString() != "(github.com/awslabs/ar-go-tools/analysis/dataflow/testdata/summaries.A).f" {
									t.Errorf(
										"in Foo, an incoming edge of the outgoing edge of param s2 is not a call to (A).f, but got: %s",
										call.FuncString())
								}
								hasCall = true
							}
						}
						if !hasParam {
							t.Errorf("in Foo, 1 incoming edge of the outgoing edge of param s2 should be a parameter node")
						}
						if !hasCall {
							t.Errorf("in Foo, 1 incoming edge of the outgoing edge of param s2 should be a call node")
						}
					}

					// s2 has one incoming edge because its Value is only
					// modified once in Foo:
					// `*s2 = obj.f(a[9])`
					if len(paramNode.In()) != 2 {
						t.Errorf("in Foo, param s2 should have two incoming edges, but got: %v", paramNode.In())
					}
					for in := range paramNode.In() {
						if call, ok := in.(*dataflow.CallNode); ok {
							if call.FuncString() != "(command-line-arguments.A).f" && call.FuncString() != "(github.com/awslabs/ar-go-tools/analysis/dataflow/testdata/summaries.A).f" {
								t.Errorf("in Foo, incoming edge of param s2 is not a call to (A).f, but got: %s", call.FuncString())
							}
						} else if _, ok := in.(*dataflow.CallNodeArg); !ok {
							t.Errorf("in Foo, incoming edge of param s2 should be a call node, but got: %T", in)
						}
					}
				}
			}

			for _, tRet := range summary.Returns {
				for _, ret := range tRet {
					if len(ret.Out()) != 0 {
						t.Errorf("in Foo, return should not have any outgoing edges, but got: %v", ret.Out())
					}

					// from statements:
					// ```
					// l := Bar(*s2)
					// return l
					// ```
					if len(ret.In()) != 1 {
						t.Errorf("in Foo, return should have one incoming edge, but got: %v", ret.In())
					}
					for in := range ret.In() {
						if call, ok := in.(*dataflow.CallNode); ok {
							if call.FuncString() != "command-line-arguments.Bar" && call.FuncString() != "github.com/awslabs/ar-go-tools/analysis/dataflow/testdata/summaries.Bar" {
								t.Errorf("in Foo, incoming edge of return is not a call to Bar, but got: %s",
									call.FuncString())
							}
						} else {
							t.Errorf("in Foo, incoming edge of return should be a call node, but got: %T", in)
						}
					}
				}
			}
		}

		if function.Name() == "FooBar" {
			ok := len(summary.Returns) == 0 // FooBar does not return data
			// for statements:
			// `s := B{Source: x}`
			// `s3 := Foo(s.Source, &s2, A{})`
			ok = ok && len(summary.SyntheticNodes) >= 2
			if !ok {
				t.Errorf("FooBar graph is not as expected")
			}

			for _, tRet := range summary.Returns {
				for _, ret := range tRet {
					if len(ret.Out()) != 0 {
						t.Errorf("in FooBar, return should not have any outgoing edges, but got: %v", ret.Out())
					}

					if len(ret.In()) != 0 {
						t.Errorf("in FooBar, return should not have any incoming edges, but got: %v", ret.In())
					}
				}
			}

			for _, param := range summary.Params {
				if len(param.Out()) < 1 {
					t.Errorf("in FooBar, param node should have at least one outgoing edge, but got: %v",
						param.Out())
				}

				hasSynthetic := false
				for out := range param.Out() {
					// func FooBar(x string) {
					//     s := B{Source: x}
					if _, ok := out.(*dataflow.SyntheticNode); ok {
						hasSynthetic = true
					}
				}

				if !hasSynthetic {
					t.Errorf("in FooBar, param node should have an outgoing edge to a synthetic node")
				}
			}

			hasFieldAddr := false
			hasParam := false
			for _, synth := range summary.SyntheticNodes {
				if _, ok := synth.Instr().(*ssa.FieldAddr); ok {
					hasFieldAddr = true
					if (len(synth.In()) > 0) && (len(synth.Out()) < 1) {
						t.Errorf("in FooBar, synthetic node with incoming edge"+
							" should have at least 1 outgoing edge, but got: %v", synth.Out())
					}

					for in := range synth.In() {
						if _, ok := in.(*dataflow.ParamNode); ok {
							hasParam = true
						}
					}

				}
			}
			if !hasFieldAddr {
				t.Errorf("in FooBar, a synthetic node should be a *ssa.FieldAddr")
			}
			if !hasParam {
				t.Errorf("in FooBar, one synthetic node should have an incoming edge that is a parameter")
			}
		}

		if function.Name() == "Baz" {
			if len(summary.AccessGlobalNodes) < 1 {
				t.Errorf("in Baz, summary should have at least 1 access global node, but got: %v",
					summary.AccessGlobalNodes)
			}
			hasSyntheticIn := false
			hasCallOut := false
			for _, globalSet := range summary.AccessGlobalNodes {
				if len(globalSet) == 0 {
					t.Errorf("in Baz, set of globals should be present")
				}
				for _, global := range globalSet {
					for in := range global.In() {
						if _, ok := in.(*dataflow.SyntheticNode); ok {
							hasSyntheticIn = true
						}
					}
					for out := range global.Out() {
						if _, ok := out.(*dataflow.CallNodeArg); ok {
							hasCallOut = true

							hasGlobal := false
							for in := range out.In() {
								if _, ok := in.(*dataflow.AccessGlobalNode); ok {
									hasGlobal = true
								}
							}
							if !hasGlobal {
								t.Errorf("in Baz, a global's outgoing node's incoming nodes should contain "+
									"a global, but got: %v", out.In())
							}
						}
					}
				}
			}
			if !hasSyntheticIn {
				t.Errorf("in Baz, a global should have a synthetic incoming node")
			}
			if !hasCallOut {
				t.Errorf("in Baz, a global should have an outgoing call node argument")
			}

			if len(summary.CreatedClosures) < 1 {
				t.Errorf("in Baz, summary should have at least 1 created closure node, but got: %v",
					summary.CreatedClosures)
			}
			for _, closure := range summary.CreatedClosures {
				if len(closure.BoundVars()) < 2 {
					t.Errorf("in Baz, closure should have at least 2 bound variable, but got: %v",
						closure.BoundVars())
				}
				// `ok` is the bound var
				// ```
				// ok := "ok"
				// closure := func(s string) string {
				// 	Sink(s1)
				// 	s4 := fmt.Sprintf("%s", s)
				// 	Sink(s4)
				// 	return s + ok
				// }
				// s5 := closure(ok)
				// ok = s.Source // this node will be a BoundLabel node because of how flow-sensitive graphs are built
				// ```
				hasCallArgOut := false
				hasCallIn := false

				for _, boundvar := range closure.BoundVars() {
					for out := range boundvar.Out() {
						if _, ok := out.(*dataflow.CallNodeArg); ok {
							hasCallArgOut = true
						}
					}
					for in := range boundvar.In() {
						if _, ok := in.(*dataflow.CallNode); ok {
							hasCallIn = true
						}
					}
				}
				if !hasCallArgOut {
					t.Errorf("in Baz, a bound var of the closure should have an outgoing edge that is a call node arg")
				}
				if !hasCallIn {
					t.Errorf("in Baz, a bound var of the closure should have an incoming edge that is a call node")
				}

			}

			if len(summary.BoundLabelNodes) == 1 {
				t.Errorf("in Baz, summary should have exactly 1 bound label node")
			} else {
				hasSynthIn := false
				for _, boundLabelGroup := range summary.BoundLabelNodes {
					for _, boundlb := range boundLabelGroup {
						for out := range boundlb.In() {
							if _, ok := out.(*dataflow.SyntheticNode); ok {
								hasSynthIn = true
							}
						}
					}
				}
				if !hasSynthIn {
					t.Errorf("in Baz, a bound label of the closure should have an incoming edge that is a synthetic node")
				}
			}

			if len(summary.Callees) < 3 {
				t.Errorf("in Baz, summary should have at least 3 callees, but got: %v", summary.Callees)
			}
			for _, callees := range summary.Callees {
				for _, callee := range callees {
					for _, arg := range callee.Args() {
						name := callee.FuncString()
						if name == "command-line-arguments.Sink" || name == "github.com/awslabs/ar-go-tools/analysis/dataflow/testdata/summaries.Sink" {
							if len(arg.Out()) >= 2 {
								t.Errorf("in Baz, all callee args to %s should less than 2 outgoing edges, but got: %v", name, arg.Out())
							}

							if len(arg.In()) < 1 {
								t.Errorf("in Baz, callee arg to %s should have at least one incoming edge, but got: %v", name, arg.In())
							}
							hasCall := false
							for in := range arg.In() {
								if _, ok := in.(*dataflow.CallNode); ok {
									hasCall = true
								}
							}
							if !hasCall {
								t.Errorf("in Baz, callee arg to %s should have an incoming edge that is a call node, but got: %v", name, arg.In())
							}
						} else if strings.HasPrefix(name, "make closure Baz$1") {
							if len(arg.Out()) != 2 {
								t.Errorf("in Baz, callee arg to %s should have 2 outgoing edges, but got: %v", name, arg.Out())
							}

							if len(arg.In()) != 1 {
								t.Errorf("in Baz, callee arg to %s should have 1 incoming edges, but got: %v", name, arg.In())
							}
						} else if name == "fmt.Sprintf" {
							// ignore the first arg to fmt.Sprintf (format string)
							if arg.Index() == 0 {
								continue
							}
							if len(arg.Out()) != 0 {
								t.Errorf("in Baz, callee arg to %s should not have any outgoing edges, but got: %v", name, arg.Out())
							}

							if len(arg.In()) < 3 {
								t.Errorf("in Baz, callee arg to %s should have at least 3 incoming edges, but got: %v", name, arg.In())
							}
							hasGlobal := false
							hasSynth := false
							for in := range arg.In() {
								if _, ok := in.(*dataflow.SyntheticNode); ok {
									hasSynth = true
								}
								if _, ok := in.(*dataflow.AccessGlobalNode); ok {
									hasGlobal = true
								}
							}
							if !hasSynth {
								t.Errorf("in Baz, callee arg to %s should have a synthetic node incoming edge, but got: %v", name, arg.In())
							}
							if !hasGlobal {
								t.Errorf("in Baz, callee arg to %s should have a global node incoming edge, but got: %v", name, arg.In())
							}
						} else {
							t.Errorf("in Baz, callee arg to %s is not expected", name)
						}
					}
				}
			}
		}

		if function.Name() == "Baz$1" {
			if len(summary.FreeVars) < 1 {
				t.Errorf("in Baz, closure should have at least one free variable, but got: %v", summary.FreeVars)
			}

			hasCallNodeArgOut := false
			hasReturnOut := false
			for _, freevar := range summary.FreeVars {
				if len(freevar.Out()) < 1 {
					t.Errorf("in Baz, closure freevar should have at least one outgoing edge, but got: %v", freevar.Out())
				}
				for out := range freevar.Out() {
					if arg, ok := out.(*dataflow.CallNodeArg); ok {
						if arg.ParentNode().FuncString() == "command-line-arguments.Sink" || arg.ParentNode().FuncString() == "github.com/awslabs/ar-go-tools/analysis/dataflow/testdata/summaries.Sink" {
							hasCallNodeArgOut = true
						}
					}
					if _, ok := out.(*dataflow.ReturnValNode); ok {
						hasReturnOut = true
					}
				}
				if freevar.SsaNode().Name() == "s1" && len(freevar.In()) != 1 {
					t.Errorf("in Baz, closure freevar %s should have 1 incoming edge, but got: %v",
						freevar.String(), freevar.In())
				}
				if freevar.SsaNode().Name() != "s1" && len(freevar.In()) != 0 {
					t.Errorf("in Baz, closure freevar %s should have no incoming edges, but got: %v",
						freevar.String(), freevar.In())
				}
			}
			if !hasCallNodeArgOut {
				t.Errorf("in Baz, a closure freevar outgoing edge should be a call arg to Sink()")
			}
			if !hasReturnOut {
				t.Errorf("in Baz, a closure freevar outgoing edge should be a return")
			}
		}

		if function.Name() == "ImplicitFlow" {
			for _, callee := range summary.Callees {
				for _, call := range callee {
					if call.FuncName() == "Source" {
						flowsToLen := false
						for out := range call.Out() {
							if _, ok := out.(*dataflow.BuiltinCallNode); ok {
								flowsToLen = true
							}
						}
						if !flowsToLen {
							t.Errorf("in ImplicitFlow, a call to Source() outgoing edge should be a bultin")
						}
					}
				}
			}

			for _, ifn := range summary.Ifs {
				hasCallNodeIn := false
				for in := range ifn.In() {
					if call, ok := in.(*dataflow.BuiltinCallNode); ok {
						hasCallNodeIn = call.FuncName() == "len"
					}
				}
				if !hasCallNodeIn {
					t.Errorf("in ImplicitFlow, an if incoming edge should be a call to len")
				}

				if len(ifn.Out()) != 0 {
					t.Errorf("in ImplicitFlow, an if node should have no outgoing edges")
				}
			}
		}
	}
}

// TestImmutableAnalysis tests the immutable parameter analysis feature
func TestImmutableAnalysis(t *testing.T) {
	dir := filepath.Join("testdata", "immutable")
	lp, err := analysistest.LoadTest(
		testfsys, dir, []string{}, analysistest.LoadTestOptions{ApplyRewrite: true}).Value()
	if err != nil {
		t.Fatalf("failed to load test: %v", err)
	}

	state, err := result.Bind(ptr.NewState(lp), dataflow.NewState).Value()
	if err != nil {
		t.Fatalf("failed to build analyzer state: %v", err)
	}

	numRoutines := runtime.NumCPU() - 1
	if numRoutines <= 0 {
		numRoutines = 1
	}

	// Run intra-procedural analysis to build summaries
	dataflow.RunIntraProceduralPass(state, numRoutines, dataflow.IntraAnalysisParams{
		ShouldBuildSummary: dataflow.ShouldBuildSummary,
		ShouldTrack:        dataflow.IsNodeOfInterest,
	})

	if len(state.FlowGraph.Summaries) == 0 {
		t.Fatalf("analyzer state does not contain any summaries")
	}

	// Test each function's immutable analysis results
	for function, summary := range state.FlowGraph.Summaries {
		functionName := function.Name()

		// Skip main and other non-test functions
		if functionName == "main" || functionName == "init" {
			continue
		}

		t.Run(functionName, func(t *testing.T) {
			// Run the immutable analysis
			result := dataflow.IsSpecSatisfyImmutable(summary)

			// Test specific expected outcomes
			switch functionName {
			case "UnusedParams":
				// All parameters should be unused (NoFlowParams)
				if !result.IsSatisfied {
					t.Errorf("UnusedParams should satisfy immutable spec")
				}
				if len(result.NoFlowParams) != 3 {
					t.Errorf("UnusedParams should have 3 no-flow params, got %d", len(result.NoFlowParams))
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("UnusedParams SSA check failed: %s", reason)
				}

			case "OnlySourceParams":
				// Parameters should only appear on RHS (as sources)
				if !result.IsSatisfied {
					t.Errorf("OnlySourceParams should satisfy immutable spec")
				}
				if len(result.NoRHSParams) != 2 {
					t.Errorf("OnlySourceParams should have 2 no-RHS params, got %d", len(result.NoRHSParams))
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("OnlySourceParams SSA check failed: %s", reason)
				}

			case "OnlyTargetParams":
				// In Go SSA form, parameters are read-only, so discarded parameters become NoFlow
				if !result.IsSatisfied {
					t.Errorf("OnlyTargetParams should satisfy immutable spec")
				}
				if len(result.NoFlowParams) != 2 {
					t.Errorf("OnlyTargetParams should have 2 no-flow params (a,b), got %d", len(result.NoFlowParams))
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("OnlyTargetParams SSA check failed: %s", reason)
				}

			case "MutableParams":
				// Parameters that flow to multiple return values (both as sources)
				if !result.IsSatisfied {
					t.Errorf("MutableParams should satisfy immutable spec (both params only sources)")
				}
				if len(result.NoRHSParams) != 2 {
					t.Errorf("MutableParams should have 2 no-RHS params, got %d", len(result.NoRHSParams))
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("MutableParams SSA check failed: %s", reason)
				}

			case "UnusedWithReturn":
				// Parameter is unused
				if !result.IsSatisfied {
					t.Errorf("UnusedWithReturn should satisfy immutable spec")
				}
				if len(result.NoFlowParams) != 1 {
					t.Errorf("UnusedWithReturn should have 1 no-flow param, got %d", len(result.NoFlowParams))
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("UnusedWithReturn SSA check failed: %s", reason)
				}

			case "NoParams":
				// No parameters, should be satisfied trivially
				if !result.IsSatisfied {
					t.Errorf("NoParams should satisfy immutable spec (no parameters)")
				}
				if len(result.NoFlowParams) != 0 && len(result.NoLHSParams) != 0 && len(result.NoRHSParams) != 0 {
					t.Errorf("NoParams should have empty parameter lists")
				}

			case "SingleParam":
				// Single parameter used normally - should be RHS only
				if !result.IsSatisfied {
					t.Errorf("SingleParam should satisfy immutable spec")
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("SingleParam SSA check failed: %s", reason)
				}

			case "IndirectFlow":
				// 'source' flows indirectly, 'unused' doesn't flow
				if !result.IsSatisfied {
					t.Errorf("IndirectFlow should satisfy immutable spec")
				}
				// Should have at least one no-flow param (unused)
				if len(result.NoFlowParams) == 0 {
					t.Errorf("IndirectFlow should have at least 1 no-flow param")
				}
				// Verify SSA check passes
				if valid, reason := dataflow.CheckParametersImmutableInSSA(result, function); !valid {
					t.Errorf("IndirectFlow SSA check failed: %s", reason)
				}
			}

			// Log results for debugging
			t.Logf("Function %s: IsSatisfied=%v, NoFlow=%d, NoLHS=%d, NoRHS=%d",
				functionName, result.IsSatisfied, len(result.NoFlowParams), len(result.NoLHSParams), len(result.NoRHSParams))
		})
	}
}

// TestImmutableAnalysisIntegration tests the integration with soundness checking
func TestImmutableAnalysisIntegration(t *testing.T) {
	dir := filepath.Join("testdata", "immutable")
	lp, err := analysistest.LoadTest(
		testfsys, dir, []string{}, analysistest.LoadTestOptions{ApplyRewrite: true}).Value()
	if err != nil {
		t.Fatalf("failed to load test: %v", err)
	}

	state, err := result.Bind(ptr.NewState(lp), dataflow.NewState).Value()
	if err != nil {
		t.Fatalf("failed to build analyzer state: %v", err)
	}

	numRoutines := runtime.NumCPU() - 1
	if numRoutines <= 0 {
		numRoutines = 1
	}

	// Run intra-procedural analysis
	dataflow.RunIntraProceduralPass(state, numRoutines, dataflow.IntraAnalysisParams{
		ShouldBuildSummary: dataflow.ShouldBuildSummary,
		ShouldTrack:        dataflow.IsNodeOfInterest,
	})

	// Build inter-procedural graph to test soundness checking integration
	state.FlowGraph.BuildGraph()

	// Test the integration by checking soundness for functions with immutable parameters
	for function, summary := range state.FlowGraph.Summaries {
		functionName := function.Name()

		// Test functions that should benefit from immutable optimization
		if functionName == "UnusedParams" || functionName == "UnusedWithReturn" {
			t.Run(functionName+"_Integration", func(t *testing.T) {
				// This should trigger the immutable analysis optimization in CheckSummarySoundness
				isSound, reason, needsDeeperCheck := state.FlowGraph.CheckSummarySoundness(function, summary)

				// Should be sound due to immutable optimization
				if !isSound {
					t.Errorf("Function %s should be sound via immutable optimization, but got: %s", functionName, reason)
				}

				// Should not need deeper analysis since immutable analysis handled it
				if len(needsDeeperCheck) != 0 {
					t.Errorf("Function %s should not need deeper analysis via immutable optimization, but got %d callees to check",
						functionName, len(needsDeeperCheck))
				}

				// Verify the reason mentions immutable
				if !strings.Contains(reason, "immutable") && !strings.Contains(reason, "parameters confirmed") {
					t.Errorf("Soundness reason should mention immutable analysis: %s", reason)
				}

				t.Logf("Function %s soundness: %v, reason: %s", functionName, isSound, reason)
			})
		}
	}
}

// test some methods that are meant to be nil-safe
func TestStringNilSafety(t *testing.T) {
	var gr *dataflow.SummaryGraph
	gr.PopulateGraphFromSummary(summaries.Summary{}, false)
	gr.Print(true, os.Stdout)
	var p *dataflow.ParamNode
	_ = p.String()
	var n *dataflow.CallNodeArg
	_ = n.String()
	var m *dataflow.CallNode
	_ = m.String()
	var s *dataflow.SyntheticNode
	_ = s.String()
	var r *dataflow.ReturnValNode
	_ = r.String()
	var f *dataflow.FreeVarNode
	_ = f.String()
	var b *dataflow.BoundVarNode
	_ = b.String()
	var bl *dataflow.BoundLabelNode
	_ = bl.String()
	var g *dataflow.AccessGlobalNode
	_ = g.String()
	var c *dataflow.ClosureNode
	_ = c.String()
	var i *dataflow.IfNode
	_ = i.String()
}
