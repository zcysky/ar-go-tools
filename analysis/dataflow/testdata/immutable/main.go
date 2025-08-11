package main

import "fmt"

// UnusedParams - parameters that are never used (should be NoFlowParams)
func UnusedParams(unused1 int, unused2 int, unused3 int) int {
	return 42 // constant result, parameters never used
}

// OnlySourceParams - parameters only used as sources (should be NoRHSParams)
func OnlySourceParams(a int, b int) int {
	return a + b // a and b only appear as sources, flow to return
}

// OnlyTargetParams - parameters that receive flows but never flow out (should be NoLHSParams)
func OnlyTargetParams(a int, b int, c int) int {
	// In SSA form, parameters are read-only, so a=c creates new local variables
	// Since a and b are never read, they should be NoFlow params
	_ = a    // prevent unused parameter optimization
	_ = b    // prevent unused parameter optimization
	return c // only c flows to return
}

// MutableParams - parameters that flow to each other (NOT immutable)
func MutableParams(a int, b int) (int, int) {
	// Create actual mutual parameter flows through conditional returns
	if a > 0 && b > 0 {
		return b, a // b flows to first return, a flows to second return
	} else if a > 0 {
		return a, b // a flows to first return, b flows to second return
	} else if b > 0 {
		return b, a // b flows to first return, a flows to second return
	}
	return a + b, a - b // both parameters flow to both returns
}

// MixedParams - some parameters are immutable, others are not
func MixedParams(used int, unused int, target int) int {
	target = used // 'used' flows to 'target', 'unused' is never used
	return used
}

// NoParams - function with no parameters (edge case)
func NoParams() int {
	return 42
}

// SingleParam - function with one parameter used normally
func SingleParam(param int) int {
	return param + 100
}

// UnusedWithReturn - unused parameter with return value
func UnusedWithReturn(unused int) int {
	return 42 // fixed value, parameter unused
}

// PartiallyUsedParams - some parameters used, some not
func PartiallyUsedParams(used1 int, unused1 int, used2 int, unused2 int) int {
	if used2 > 0 {
		return used1 + 10
	}
	return used1
}

// ComplexFlow - parameters with complex dataflow patterns
func ComplexFlow(a int, b int, c int) int {
	if c > 0 {
		b = a        // a flows to b
		return b + a // b flows back to return
	}
	return a
}

// IndirectFlow - parameters that flow through intermediate variables
func IndirectFlow(source int, unused int) int {
	temp := source // source flows to temp
	result := temp // temp flows to result
	return result  // result flows to return
}

// ConditionalUnused - parameter used only in unreachable code
func ConditionalUnused(maybe_unused int, condition int) int {
	if condition > 0 {
		return maybe_unused // used conditionally
	}
	return 42
}

// main function for testing
func main() {
	// Test calls to exercise the functions
	fmt.Println(UnusedParams(1, 2, 3))
	fmt.Println(OnlySourceParams(10, 20))
	fmt.Println(OnlyTargetParams(1, 2, 30))

	a, b := MutableParams(5, 7)
	fmt.Println(a, b)

	fmt.Println(MixedParams(100, 999, 200))
	fmt.Println(NoParams())
	fmt.Println(SingleParam(50))
	fmt.Println(UnusedWithReturn(123))
	fmt.Println(PartiallyUsedParams(10, 123, 1, 456))
	fmt.Println(ComplexFlow(30, 40, 1))
	fmt.Println(IndirectFlow(80, 456))
	fmt.Println(ConditionalUnused(99, 0))
}
