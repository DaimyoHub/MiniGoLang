package main
import "fmt"

func test(a int) int {
	return 4
}

func test2(b int, t bool) int {
	return b + test(3)
}

func main() {
	fmt.Print(test2(true))
}
