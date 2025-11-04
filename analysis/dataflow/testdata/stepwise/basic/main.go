package main

// Basic functions to test stepwise soundness algorithm
// This tests that the infrastructure works correctly

func basicIntFunction(a int, b int) int {
	return a + b
}

func basicPointerFunction(a *int, b *int) *int {
	if a != nil {
		return a
	}
	return b
}

func basicSliceFunction(a []int, b []int) []int {
	return append(a, b...)
}

func main() {
	x := 1
	y := 2

	// Test basic int function
	result := basicIntFunction(x, y)

	// Test pointer function
	ptrResult := basicPointerFunction(&x, &y)

	// Test slice function
	slice1 := []int{1, 2}
	slice2 := []int{3, 4}
	sliceResult := basicSliceFunction(slice1, slice2)

	// Use results to avoid unused variable errors
	_ = result
	_ = ptrResult
	_ = sliceResult
}
