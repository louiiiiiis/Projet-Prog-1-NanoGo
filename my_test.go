package main
import "fmt"

type T struct { s int }

func main() {
	var x, y, z int
	x, y, z = 12, 14, 0
	var x *T
	for n := 0; n <= 10; n++ {
		fmt.Print(n, y)
		fmt.Print(n, x)
		fmt.Print("\n")
	}
}


