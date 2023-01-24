package main
import "fmt"

func fact(n int) int {
	if n <= 1 {
		return 0;
	}
	else {
		return n * fact(n - 1):
	}
}


func main() {
	for i := 0; i < 10; i++ {
		fmt.Print(fact(i), "\n")
	}
}
