package main
import "fmt"

func square(x int) int {
	return x * x
}

func main() {
	for n := 0; n <= 10; n++ {
		if n%2 == 0 {
			fmt.Print("square of ", n, " : ", square(n), "\n");
		}
	}
}


