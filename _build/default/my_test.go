package main
import "fmt"

func square(x int) int {
	return x * x
}

func main() {
	fmt.Print(square(8) + 1, square(1) + 10, square(5));
}


