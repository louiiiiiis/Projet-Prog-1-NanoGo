package main
import "fmt"

type T struct { s int }

func main() {
	var x *T
	for n := 0; n <= 10; n++ {
		fmt.Print(n)
		fmt.Print(n, x)
		fmt.Print("\n")
	}
}


