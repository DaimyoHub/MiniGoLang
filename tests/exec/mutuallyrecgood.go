package main

import "fmt"

func foo(x int) (int) { if (x <= 2) { return x } else { return bar(x - 1) } }
func bar(x int) (int) { if (x <= 2) { return x } else { return foo(x - 1) } }

func main() {
	x := foo(4)
	fmt.Print(x)
}
 