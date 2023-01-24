package main
import "fmt"

func f(n int) int {
	if n%2 == 0 {
		return(n / 2)
	}
	else {
		return(3 * n + 1)
	}
}

func main() {
	for x := 0; x <= 10; x++ {
		fmt.Print("f(", x, ") = ", f(x), "\n")
	}
}

