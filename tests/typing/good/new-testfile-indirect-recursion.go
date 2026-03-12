package main

import "fmt"

func foo(x int) (int) { return bar(x) }
func bar(x int) (int) { return foo(x) }

func main() {
	x := foo(1)
	fmt.Print(x)
}
 
