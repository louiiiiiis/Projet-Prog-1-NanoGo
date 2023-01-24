package main
import "fmt"

func square(x int) int {
	return x * x
}

func main() {
	for n := 0; n <= 10; n++ {
	fmt.Print("carré de ", n, " : ", square(n), "\n");
	}
}


