package main

// Integration tests for stepwise soundness algorithm
// Tests that all steps work together properly

// Function that should be detected as equals full-flow (Step 1)
func equalsFullFlow(a *int, b *int) *int {
	// Simple function where summary should equal full flow
	if a != nil {
		return a
	}
	return b
}

// Function where type filtering should work (Step 2)
func typeFiltering(a int, b string) int {
	// Non-pointer parameters, some flows should be filtered by type
	_ = b
	return a
}

// Function with immutable parameters (Step 3)
func immutableParams(a int, b int) int {
	// Parameter 'b' is unused, flows from it should be filtered
	return a + 42
}

// Function with limited reachability (Step 4)
func limitedReachability(a int, b int, c int) int {
	// No function calls, so reachability is limited
	return a + b
}

// Function that needs recursive analysis (Step 5)
func needsRecursive(a *int, b *int) *int {
	return helper(a, b)
}

func helper(x *int, y *int) *int {
	if x != nil && y != nil {
		if *x > *y {
			return x
		}
		return y
	}
	if x != nil {
		return x
	}
	return y
}

// External function (no body available for analysis)
func externalFunc(a int, b int) int

// Function with mixed characteristics
func mixedFunction(a int, b *int, c []int, d string) (int, *int) {
	// Mix of pointer and non-pointer types
	// Some parameters used, others not
	// Some modified, others not
	if b != nil && len(c) > 0 {
		*b = a + len(c) // Modify b
		return c[0], b  // Use c and b
	}
	// d is never used
	return a, nil
}

// Function that tests caching behavior
func cachingTest(a int) int {
	return a * 2
}

// Function that tests recursion depth limits
func deepRecursion(n int) int {
	if n <= 0 {
		return 0
	}
	return 1 + deepRecursion(n-1)
}

func main() {
	x := 42
	y := 24
	z := 10

	// Test equals full flow
	result1 := equalsFullFlow(&x, &y)

	// Test type filtering
	result2 := typeFiltering(x, "hello")

	// Test immutable params
	result3 := immutableParams(x, y)

	// Test limited reachability
	result4 := limitedReachability(x, y, z)

	// Test recursive analysis
	result5 := needsRecursive(&x, &y)

	// Test mixed function
	w := 100
	slice := []int{1, 2, 3}
	r1, r2 := mixedFunction(x, &w, slice, "unused")

	// Test caching (call same function multiple times)
	cache1 := cachingTest(x)
	cache2 := cachingTest(x)

	// Test recursion (small depth to avoid issues)
	recursive1 := deepRecursion(5)

	// Use results to avoid unused variable errors
	_ = result1
	_ = result2
	_ = result3
	_ = result4
	_ = result5
	_ = r1
	_ = r2
	_ = cache1
	_ = cache2
	_ = recursive1
}
