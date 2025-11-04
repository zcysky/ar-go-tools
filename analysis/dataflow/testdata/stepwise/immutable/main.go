package main

// Functions to test Step 3: immutability-based pruning
// Tests unused parameters and unmodified parameters

// Parameter that is never used - flows from this should be filtered
func unusedParam(a int, b int) int {
	// Only use 'a', 'b' is unused
	return a + 10
}

// Parameter that is never modified - flows to this should be filtered
func unmodifiedParam(a int, b *int) int {
	// 'b' is read but never modified
	if b != nil {
		return a + *b
	}
	return a
}

// Parameters that are both used and modified - no flows should be filtered
func usedAndModified(a int, b *int) int {
	if b != nil {
		*b = a + 1 // 'b' is modified
		return *b  // 'b' is also used
	}
	return a
}

// Function that reads from parameters multiple times
func multipleReads(a int, b int) int {
	x := a + b
	y := a * b
	return x + y
}

// Function that modifies parameter through alias
func modifyThroughAlias(a *int, b int) int {
	if a != nil {
		ptr := a // Create alias
		*ptr = b // Modify through alias
		return *a
	}
	return b
}

// Function with parameter passed to function call
func passToFunction(a []int, b int) int {
	if len(a) > 0 {
		append(a, b) // 'a' is passed to function, could be modified
		return len(a)
	}
	return b
}

func main() {
	x := 1
	y := 2
	z := 3

	// Test unused parameter
	result1 := unusedParam(x, y)

	// Test unmodified parameter
	result2 := unmodifiedParam(x, &z)

	// Test used and modified
	w := 5
	result3 := usedAndModified(x, &w)

	// Test multiple reads
	result4 := multipleReads(x, y)

	// Test modify through alias
	v := 10
	result5 := modifyThroughAlias(&v, x)

	// Test pass to function
	slice := []int{1, 2, 3}
	result6 := passToFunction(slice, x)

	// Use results to avoid unused variable errors
	_ = result1
	_ = result2
	_ = result3
	_ = result4
	_ = result5
	_ = result6
}
