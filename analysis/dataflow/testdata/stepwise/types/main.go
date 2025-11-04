package main

// Functions with different parameter types to test Step 2: type filtering
// Tests the canPoint logic and type-based flow elimination

// Both parameters are non-pointer types - should allow type-based filtering
func bothNonPointer(a int, b string) int {
	_ = b
	return a
}

// Mixed pointer and non-pointer types
func mixedTypes(a *int, b string) string {
	_ = a
	return b
}

// Both parameters are pointer types - should not be filtered by type
func bothPointers(a *int, b *string) *int {
	_ = b
	return a
}

// Function that returns values (flows to return should never be filtered)
func toReturn(a int, b string) (int, string) {
	return a, b
}

// Different pointer types
func differentPointers(a *int, b []int, c map[string]int) *int {
	_ = b
	_ = c
	return a
}

// Interface parameters
func withInterface(a interface{}, b int) interface{} {
	_ = b
	return a
}

// Channel parameters
func withChannel(a chan int, b int) chan int {
	_ = b
	return a
}

func main() {
	x := 42
	str := "hello"

	// Test non-pointer function
	result1 := bothNonPointer(x, str)

	// Test mixed types
	result2 := mixedTypes(&x, str)

	// Test both pointers
	result3 := bothPointers(&x, &str)

	// Test return flows
	r1, r2 := toReturn(x, str)

	// Test different pointer types
	slice := []int{1, 2, 3}
	m := map[string]int{"a": 1}
	result4 := differentPointers(&x, slice, m)

	// Test interface
	var iface interface{} = x
	result5 := withInterface(iface, x)

	// Test channel
	ch := make(chan int)
	result6 := withChannel(ch, x)

	// Use results to avoid unused variable errors
	_ = result1
	_ = result2
	_ = result3
	_ = r1
	_ = r2
	_ = result4
	_ = result5
	_ = result6
}
