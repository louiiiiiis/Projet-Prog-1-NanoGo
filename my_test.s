	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_square:
	pushq %rbp
	movq %rsp, %rbp
	movq 16(%rbp), %rdi
	movq %rdi, %rsi
	movq 16(%rbp), %rdi
	imulq %rsi, %rdi
	movq %rdi, %rax
	jmp E_square
E_square:
	movq %rbp, %rsp
	popq %rbp
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $1, %rdi
	movq %rdi, %rsi
	movq $8, %rdi
	pushq %rdi
	call F_square
	movq %rax, %rdi
	addq %rsi, %rdi
	call print_int
	movq $S_3, %rdi
	call print_string
	movq $10, %rdi
	movq %rdi, %rsi
	movq $1, %rdi
	pushq %rdi
	call F_square
	movq %rax, %rdi
	addq %rsi, %rdi
	call print_int
	movq $S_2, %rdi
	call print_string
	movq $5, %rdi
	pushq %rdi
	call F_square
	movq %rax, %rdi
	call print_int
	movq $S_1, %rdi
	call print_string
E_main:
	movq %rbp, %rsp
	popq %rbp
	ret
print_int:
	movq %rdi, %rsi
	movq $S_int, %rdi
	xorq %rax, %rax
	call printf
	ret
print_string:
	movq %rdi, %rsi
	movq $S_string, %rdi
	xorq %rax, %rax
	call printf
	ret

	  	.data
S_int:
	.string "%ld"
S_string:
	.string "%s"
S_2:
	.string " "
S_3:
	.string " "
S_1:
	.string "\n"
