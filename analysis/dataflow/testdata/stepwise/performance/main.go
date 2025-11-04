package main

// Functions to test performance characteristics of stepwise algorithm
// Tests that the algorithm scales reasonably with function complexity

// Simple function with minimal complexity
func simpleFunction(a int) int {
	return a + 1
}

// Function with multiple parameters
func multipleParams(a int, b string, c *int, d []int, e map[string]int) int {
	_ = b
	_ = c
	_ = d
	_ = e
	return a
}

// Function with control flow
func withControlFlow(a int, b int, c int) int {
	if a > 0 {
		if b > 0 {
			return a + b
		}
		return a + c
	}
	if c > 0 {
		return b + c
	}
	return 0
}

// Function with loops
func withLoop(a []int, b int) int {
	sum := 0
	for _, v := range a {
		sum += v + b
	}
	return sum
}

// Function that calls other functions
func callsOthers(a int, b int) int {
	x := simpleFunction(a)
	y := multipleParams(b, "test", &a, []int{1, 2}, map[string]int{"k": 1})
	return x + y
}

// Recursive function
func recursive(n int) int {
	if n <= 1 {
		return n
	}
	return recursive(n-1) + recursive(n-2)
}

// Function with many local variables
func manyLocals(a int, b int, c int) int {
	x1 := a + 1
	x2 := b + 2
	x3 := c + 3
	x4 := x1 + x2
	x5 := x2 + x3
	x6 := x3 + x1
	x7 := x4 + x5
	x8 := x5 + x6
	x9 := x6 + x4
	x10 := x7 + x8 + x9
	return x10
}

func main() {
	// Test simple function
	result1 := simpleFunction(42)

	// Test multiple parameters
	slice := []int{1, 2, 3}
	m := map[string]int{"key": 42}
	x := 10
	result2 := multipleParams(42, "hello", &x, slice, m)

	// Test control flow
	result3 := withControlFlow(1, 2, 3)

	// Test loops
	result4 := withLoop(slice, 5)

	// Test function calls
	result5 := callsOthers(10, 20)

	// Test recursion (small input to avoid timeout)
	result6 := recursive(5)

	// Test many locals
	result7 := manyLocals(1, 2, 3)

	// Use results to avoid unused variable errors
	_ = result1
	_ = result2
	_ = result3
	_ = result4
	_ = result5
	_ = result6
	_ = result7
}
