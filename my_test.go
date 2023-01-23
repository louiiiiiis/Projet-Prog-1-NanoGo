package main
import "fmt"

func square(x int) int {
	return x * x
}

func main() {
	var x, y int;
	x = 5;
	y = 2;
	fmt.Print(square(x) + 1, " ", y, " ", square(y), " ", square(y) + 1, "\n");
}


