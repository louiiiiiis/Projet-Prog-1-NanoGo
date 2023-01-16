(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  next_local: int; (* 0, 1, ... *)
  ofs_var: (int, int) Hashtbl.t; (* donne l'offset des variables dans la pile, à partir de leur id *)
  mutable current: int (* donne la position actuelle du pointeur sur la pile *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0; ofs_var = Hashtbl.create 0; current = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) -> (* chaîne de caractères : on la rajoute dans la data *)
    let l = alloc_string s in
	movq (ilab l) (reg rdi)
  | TEbinop (Band, e1, e2) -> (* et lazy : si (non e1) alors false sinon e2 *)
	let l = new_label in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l ++ (expr env e2) ++ label l
  | TEbinop (Bor, e1, e2) -> (* ou lazy : si e1 alors true sinon e2 *)
    let l = new_label in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ jne l ++ (expr env e2) ++ label l
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) -> (* comparaison d'entiers : on place le drapeau correspondant à la comparaison puis on met le résultat dans rdi *)
	let l = new_label in
    (expr env e1) ++ movq (reg rdi) (reg rsi) ++ (expr env e2) ++ movq (reg rdi) (reg rdx)
	++ movq (imm 1) (reg rdi) ++ cmpq (reg rdx) (reg rsi) ++ (match op with | Blt -> jl | Ble -> jle | Bgt -> jg | Bge -> jge) l
	++ movq (imm 0) (reg rdi) ++ label l
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) -> (* opérations +, - et * pour les entiers *)
    (expr env e2) ++ movq (reg rdi) (reg rsi) ++ (expr env e1)
	++ (match op with | Badd -> addq | Bsub -> subq | Bmul -> imulq) (reg rsi) (reg rdi)
  | TEbinop (Bdiv | Bmod as op, e1, e2) -> (* opérations / et % pour les entiers *)
    (expr env e1) ++ movq (reg rdi) (reg rax) ++ (expr env e1) ++ movq (imm 0) (reg rdx)
	++ idivq (reg rdi) ++ movq (match op with | Bdiv -> (reg rax) | Bmod -> (reg rdx)) (reg rdi)
  | TEbinop (Beq | Bne as op, e1, e2) -> (* = et != *)
    let l = new_label in
    (expr env e1) ++ movq (reg rdi) (reg rsi) ++ (expr env e2) ++ movq (reg rdi) (reg rdx)
	++ movq (imm 1) (reg rdi) ++ cmpq (reg rsi) (reg rdi) ++ (match op with | Beq -> je | Bne -> jne) l
	++ movq (imm 0) (reg rdi) ++ label l
  | TEunop (Uneg, e1) -> (* négation d'entiers *)
    (expr env e1) ++ negq (reg rdi)
  | TEunop (Unot, e1) -> (* négation de booléens *)
    (expr env e1) ++ notq (reg rdi)
  | TEunop (Uamp, e1) -> (* récupération d'adresse *)
    (expr env e1) ++ movq (reg rdi) (reg rsi) ++ leaq (reg rsi) (reg rdi)
  | TEunop (Ustar, e1) -> (* valeur d'un pointeur *)
    (expr env e1) ++ movq (ind rdi) (reg rdi) 
  | TEprint el -> (* on a différentes fonctions pour print les différents types *)
    let rec aux = function
	| [] -> movq (ilab "S_newline") (reg rdi) ++ call "print_string"
	| t :: q -> begin
	  match t.expr_typ with
	  | Tint -> (expr env t) ++ call "print_int"
	  | Tptr -> (expr env t) ++ call "print_ptr"
	  | Tbool -> let l = new_label in (expr env t) ++ testq (reg rdi) (reg rdi) ++ movq (ilab "false") (reg rdi) ++ je l ++ movq (ilab "true") (reg rdi) ++ label l ++ call "print_string"
	  | Tstring -> (expr env t) ++ call "print_string"
	  end
	  ++ movq (ilab "S_space") (reg rdi) ++ call "print_string" ++ (aux q)
	in aux el
  | TEident x -> (* appel d'une variable *)
    movq (ind ~ofs:(Hashtbl.find env.ofs_var x.v_id) rbp) (reg rdi)
  | TEassign ([{expr_desc=TEident x}], [e1]) -> (* affectation unique *)
    (expr env e1) ++ (match x.v_name with | "_" -> nop | _ -> movq (reg rdi) (ind ~ofs:(Hashtbl.find env.ofs_var x.v_id) rbp))
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false 
  | TEassign (_, _) ->
    assert false
  | TEblock el -> (* traitement d'un block *)
    let rec aux = function
	| [] -> nop
	| {expr_desc = TEvars(vl)} :: reste -> begin
	  let rec aux2 en_cours = function
	  | [] -> en_cours
	  | x :: reste -> aux2 (if x.v_name = "_" then en_cours else (Hashtbl.add env.ofs_var x.v_id env.current; env.current <- env.current + (sizeof x.v_typ); pushq (imm 0) ++ en_cours)) reste
	  in aux2 nop el
	  end
	| e :: reste -> (expr env e) ++ aux reste
	in aux el
  | TEif (e1, e2, e3) -> (* if *)
    let l1 = new_label in
	let l2 = new_label in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l1 ++ (expr env e1) ++ jmp l2 ++ label l1 ++ (expr env e2) ++ label l2
  | TEfor (e1, e2) -> (* for *)
    let l1 = new_label in
    let l2 = new_label in
	label l1 ++ (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l2 ++ (expr env e2) ++ jmp l1 ++ label l2
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) ->
     (* TODO code pour appel fonction *) assert false
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    (* TODO code pour return e *) assert false
  | TEreturn [e1] ->
    (* TODO code pour return e1,... *) assert false
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) ->
    (* TODO code pour return e++, e-- *) assert false

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) let s = f.fn_name in label ("F_" ^ s) 

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  (* TODO code fonctions *) let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
	  label "print_int" ++ movq (reg rdi) (reg rsi) ++ movq (ilab "S_int") (reg rdi) ++ xorq (reg rax) (reg rax) ++ call "printf" ++ ret ++
	  label "print_ptr" ++ movq (reg rdi) (reg rsi) ++ movq (ilab "S_ptr") (reg rdi) ++ xorq (reg rax) (reg rax) ++ call "printf" ++ ret ++
	  label "print_string" ++ movq (reg rdi) (reg rsi) ++ movq (ilab "S_string") (reg rdi) ++ xorq (reg rax) (reg rax) ++ call "printf" ++ ret
   ;
   (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
	  label "S_ptr" ++ string "%p" ++
	  label "S_string" ++ string "%s" ++
	  label "S_space" ++ string " " ++
	  label "S_newline" ++ string "\n"
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
