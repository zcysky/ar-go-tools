package main

import "fmt"

// ========== Basic Parameter Flow Tests ==========

// SimpleFlow demonstrates intra-procedural flow that should be caught by lightweight reaching definition analysis
func SimpleFlow(a, b string) string {
	// Simple case: parameter flows to return through local operations only
	x := a + "suffix"
	return x
}

// SingleParamReturn - one parameter flows directly to return
func SingleParamReturn(input string) string {
	return input
}

// MultiParamReturn - multiple parameters to multiple returns
func MultiParamReturn(a, b, c string) (string, string, string) {
	return a, b, c
}

// UnusedParameter - parameter never used in function body
func UnusedParameter(used, unused string) string {
	return used + "_processed"
}

// ParameterReused - same parameter used multiple times
func ParameterReused(param string) string {
	first := param + "_first"
	second := param + "_second"
	return first + second
}

// ========== Arithmetic & Operations Tests ==========

// ArithmeticFlow - binary/unary operations preserving reaching definitions
func ArithmeticFlow(a, b int) int {
	sum := a + b
	doubled := sum * 2
	return doubled
}

// StringOperations - string concatenation and formatting
func StringOperations(base, suffix string) string {
	concat := base + suffix
	formatted := fmt.Sprintf("%s_formatted", concat)
	return formatted
}

// ConversionFlow - type conversions
func ConversionFlow(input int) string {
	converted := string(rune(input))
	return converted
}

// ========== Control Flow Tests ==========

// TwoParamFlow demonstrates multiple parameters flowing to return
func TwoParamFlow(a, b string) (string, string) {
	// Both parameters flow to different returns
	return a + "_modified", b + "_suffix"
}

// ConditionalFlow demonstrates conditional parameter flows
func ConditionalFlow(flag bool, data string) string {
	if flag {
		return data + "_true"
	}
	return data + "_false"
}

// PhiNodeFlow - if/else merging parameter flows
func PhiNodeFlow(cond bool, a, b string) string {
	var result string
	if cond {
		result = a
	} else {
		result = b
	}
	return result + "_merged"
}

// LoopFlow - for loop with parameters
func LoopFlow(input string, count int) string {
	result := input
	for i := 0; i < count; i++ {
		result = result + "_loop"
	}
	return result
}

// SwitchFlow - switch statements
func SwitchFlow(selector int, a, b, c string) string {
	switch selector {
	case 1:
		return a
	case 2:
		return b
	default:
		return c
	}
}

// ========== Field & Index Access Tests ==========

type TestStruct struct {
	Field1 string
	Field2 int
	Nested NestedStruct
}

type NestedStruct struct {
	Value string
}

// StructFieldFlow - accessing struct fields
func StructFieldFlow(param string) TestStruct {
	return TestStruct{
		Field1: param,
		Field2: 42,
	}
}

// ArrayIndexFlow - array/slice indexing
func ArrayIndexFlow(input string) string {
	arr := []string{input, "other"}
	return arr[0]
}

// NestedStructFlow - nested field access
func NestedStructFlow(param string) string {
	s := TestStruct{
		Nested: NestedStruct{
			Value: param,
		},
	}
	return s.Nested.Value
}

// ========== Function Call Tests ==========

// CallWithoutEffect - calls shouldn't leak internal effects (lightweight analysis ignores internals)
func CallWithoutEffect(param string) string {
	// The analysis should NOT see internal flows of fmt.Sprintf
	result := fmt.Sprintf("prefix_%s", param)
	return result
}

// BuiltinCallFlow - builtin functions like len, cap
func BuiltinCallFlow(param []string) int {
	length := len(param)
	return length
}

// MethodCallFlow - method calls on parameters
func MethodCallFlow(param TestStruct) string {
	// Method calls should be treated conservatively
	return param.Field1 + "_method"
}

// ========== Complex Scenarios ==========

// ChainedFlow demonstrates chained operations within function
func ChainedFlow(input string) string {
	step1 := input + "_step1"
	step2 := step1 + "_step2"
	return step2
}

// ConditionalChaining - complex control + data flow
func ConditionalChaining(cond1, cond2 bool, a, b, c string) string {
	var intermediate string
	if cond1 {
		if cond2 {
			intermediate = a + b
		} else {
			intermediate = a + c
		}
	} else {
		intermediate = b + c
	}
	return intermediate + "_final"
}

// MultipleReturns - functions with multiple return statements
func MultipleReturns(selector int, a, b, c string) string {
	if selector == 1 {
		return a + "_path1"
	}
	if selector == 2 {
		return b + "_path2"
	}
	return c + "_default"
}

// NoParameterFlow - no parameters flow to return
func NoParameterFlow(a, b string) string {
	return "constant_value"
}

// PartialParameterFlow - only some parameters flow
func PartialParameterFlow(used1, unused, used2 string) string {
	return used1 + used2
}

// ========== Edge Cases ==========

// EmptyFunction - minimal function
func EmptyFunction(param string) {
	// No operations, parameter doesn't flow anywhere
}

// MultipleAssignments - parameter assigned to multiple variables
func MultipleAssignments(param string) string {
	a := param
	b := param
	c := a + b
	return c
}

// PointerOperations - pointer dereferencing (if applicable)
func PointerOperations(param *string) string {
	if param != nil {
		return *param + "_deref"
	}
	return "nil"
}

func main() {
	// Entry point for testing - not used directly
}
