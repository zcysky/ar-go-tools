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

package lang

import (
	"strings"

	"golang.org/x/tools/go/ssa"
)

// FindFunction finds a function by its full name (e.g. "package/path.MyFunction")
func FindFunction(prog *ssa.Program, fullName string) *ssa.Function {
	for _, pkg := range prog.AllPackages() {
		if strings.HasPrefix(fullName, pkg.Pkg.Path()) {
			funcName := strings.TrimPrefix(fullName, pkg.Pkg.Path()+".")
			if member := pkg.Members[funcName]; member != nil {
				if f, ok := member.(*ssa.Function); ok {
					return f
				}
			}
		}
	}
	// Fallback for functions in main package
	if member := prog.AllPackages()[0].Members[fullName]; member != nil {
		if f, ok := member.(*ssa.Function); ok {
			return f
		}
	}
	return nil
}

// FindMethodForType finds a method for a given receiver type and method name.
func FindMethodForType(prog *ssa.Program, receiverType string, methodName string) *ssa.Function {
	for _, pkg := range prog.AllPackages() {
		if t := pkg.Type(strings.TrimPrefix(receiverType, pkg.Pkg.Path()+".")); t != nil {
			if mset := prog.MethodSets.MethodSet(t.Type()); mset != nil {
				if sel := mset.Lookup(pkg.Pkg, methodName); sel != nil {
					return prog.MethodValue(sel)
				}
			}
			if mset := prog.MethodSets.MethodSet(t.Type().Underlying()); mset != nil {
				if sel := mset.Lookup(pkg.Pkg, methodName); sel != nil {
					return prog.MethodValue(sel)
				}
			}
		}
	}
	return nil
}
