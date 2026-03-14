package main
import "fmt"

type U struct {
	x int
	y int
}

type T struct {
	a int
	u U
	b int
}

func main() {
	p := new(T)
	p.a = 10
	p.u.x = 20
	p.u.y = 30
	p.b = 40

	fmt.Print(p.a)
	fmt.Print("\n")
	fmt.Print(p.u.x)
	fmt.Print("\n")
	fmt.Print(p.u.y)
	fmt.Print("\n")
	fmt.Print(p.b)
	fmt.Print("\n")
}
