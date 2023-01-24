package main
import "fmt"

func main() {
	var x, y, z int;
	x = 5;
	y, z = x + 45, 22;
	fmt.Print(x, " ", y, " ", z, "\n");
	x++; y--;
	fmt.Print(x, " ", y, "\n");
}
