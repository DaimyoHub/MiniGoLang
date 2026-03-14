package main

import "fmt"

func a() int { return b(); }
func b() int { return c(); }
func c() int { return 45; }

func main() {
	fmt.Print(d());
}

func d() int { return a(); }
