package main
import "fmt"

func many_ones(n int) int {
	var x = 0;
	for i := 0; i < n; i++ {
		x = 10 * x + 1;
	}
	return x;
}

func main() {
	fmt.Print(many_ones(5), "\n");
	fmt.Print(many_ones(15), "\n");
}
