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
	"fmt"
	"go/types"
	"strings"
	"sync/atomic"

	"github.com/awslabs/ar-go-tools/analysis/lang"
	"github.com/awslabs/ar-go-tools/analysis/summaries"
	"golang.org/x/tools/go/ssa"
)

// SsaInfo is holds all the information from a built ssa program with main packages
type SsaInfo struct {
	Prog     *ssa.Program
	Packages []*ssa.Package
	Mains    []*ssa.Package
}

// This global variable should only be read and modified through GetUniqueFunctionID
var uniqueFunctionIDCounter uint32 = 0

// GetUniqueFunctionID increments and returns the Value of the global used to give unique function ids.
func GetUniqueFunctionID() uint32 {
	x := atomic.AddUint32(&uniqueFunctionIDCounter, 1)
	return x
}

// ResolveFunction resolves a function summary to an ssa.Function
func ResolveFunction(prog *ssa.Program, summary summaries.FrontendDataflowSummary) (*ssa.Function, error) {
	switch s := summary.(type) {
	case summaries.FunctionFlowSummary:
		return lang.FindFunction(prog, s.Function), nil
	case summaries.ReceiverMethodFlowSummary:
		return lang.FindMethodForType(prog, s.Receiver, s.Method), nil
	case summaries.IfaceMethodFlowSummary:
		// We don't resolve interface methods to a specific implementation here.
		// This is handled by the contract mechanism.
		return nil, nil
	default:
		return nil, fmt.Errorf("unknown summary type")
	}
}

// ComputeMethodImplementations computes the map from method identifiers to their implementations.
func ComputeMethodImplementations(prog *ssa.Program,
	implementationsByType map[string]map[*ssa.Function]bool,
	contracts map[string]*SummaryGraph,
	methodKeys map[string]string) error {
	for _, t := range prog.RuntimeTypes() {
		mset := prog.MethodSets.MethodSet(t)
		for i := 0; i < mset.Len(); i++ {
			meth := mset.At(i)
			if meth.Obj() == nil {
				continue
			}
			if meth.Obj().Pkg() == nil {
				continue
			}
			if meth.Obj().Type() == nil {
				continue
			}

			if _, ok := meth.Obj().Type().(*types.Signature); !ok {
				continue
			}

			implementingFunction := prog.MethodValue(meth)
			if implementingFunction == nil {
				continue
			}

			methodID := meth.Obj().Id()
			if !strings.Contains(methodID, "(") {
				methodID = fmt.Sprintf("%s.%s", t.String(), meth.Obj().Name())
			}

			if _, ok := implementationsByType[methodID]; !ok {
				implementationsByType[methodID] = map[*ssa.Function]bool{}
			}
			implementationsByType[methodID][implementingFunction] = true
			methodKeys[implementingFunction.String()] = methodID
		}
	}

	// Also add contract implementations to the map
	for methodID, summary := range contracts {
		if summary != nil {
			if _, ok := implementationsByType[methodID]; !ok {
				implementationsByType[methodID] = map[*ssa.Function]bool{}
			}
			implementationsByType[methodID][summary.Parent] = true
		}
	}
	computeErrorBuiltinImplementations(prog, implementationsByType, contracts, methodKeys)
	return nil
}

// computeErrorBuiltinImplementations adds the implementations of the builtin error interface (the error.Error method)
// to the implementations map
func computeErrorBuiltinImplementations(p *ssa.Program, implementations map[string]map[*ssa.Function]bool,
	contracts map[string]*SummaryGraph, keys map[string]string) {
	key := "error.Error"
	for _, typ := range p.RuntimeTypes() {
		set := p.MethodSets.MethodSet(typ)
		// Does it implement the error builtin?
		for i := 0; i < set.Len(); i++ {
			method := set.At(i)
			// Get the function implementation
			methodValue := p.MethodValue(method)
			if methodValue == nil || methodValue.Name() != "Error" || len(methodValue.Params) > 1 {
				continue
			}
			results := methodValue.Signature.Results()
			if results.Len() != 1 {
				continue
			}
			expectedString := results.At(0).Type().Underlying()
			if expectedString.String() != "string" {
				continue
			}

			keys[methodValue.String()] = key
			// Get the interface method being implemented
			addImplementation(implementations, key, methodValue)
			addContractSummaryGraph(contracts, key, methodValue, GetUniqueFunctionID())
		}
	}
}

// addImplementation sets the Value of key in implementationsMap to function, handling the creation of nested maps.
// @requires implementationMap != nil
func addImplementation(implementationMap map[string]map[*ssa.Function]bool, key string, function *ssa.Function) {
	if implementations, ok := implementationMap[key]; ok {
		if !implementations[function] {
			implementationMap[key][function] = true
		}
	} else {
		implementationMap[key] = map[*ssa.Function]bool{function: true}
	}
}

// addContractSummaryGraph sets the Value of contract[methodId] to a new summary of function if the methodId key
// is present in contracts but the associated Value is nil
// Does nothing if contracts is nil.
func addContractSummaryGraph(contracts map[string]*SummaryGraph, methodID string, function *ssa.Function, id uint32) {
	if contracts == nil || function == nil {
		return
	}
	// Entry must be present
	if curSummary, ok := contracts[methodID]; ok {
		if curSummary == nil {
			contracts[methodID] = NewSummaryGraph(nil, function, id, nil, nil)
		}
	}
}

func methodSetToNameMap(methodSet *types.MethodSet) map[string]*types.Selection {
	nameMap := map[string]*types.Selection{}

	for i := 0; i < methodSet.Len(); i++ {
		method := methodSet.At(i)
		nameMap[method.Obj().Name()] = method
	}
	return nameMap
}
