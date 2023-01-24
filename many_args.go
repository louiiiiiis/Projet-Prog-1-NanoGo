package main
import "fmt"

func somme(a int, b int, c int) int {
	return(a + b + c);
}

func main() {
	fmt.Print(somme(4, 5, 6));
}
