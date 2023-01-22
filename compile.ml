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
  vars: (int, int) Hashtbl.t; (* stocke l'offset des variables dans la pile *)
  mutable current_ofs: int (* information sur la profondeur actuelle de pile *)
}

let new_env exit vars current =
  { exit_label = exit; vars = vars; current_ofs = current }

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
	let l = new_label () in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l ++ (expr env e2) ++ label l
  | TEbinop (Bor, e1, e2) -> (* ou lazy : si e1 alors true sinon e2 *)
    let l = new_label () in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ jne l ++ (expr env e2) ++ label l
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) -> (* comparaison d'entiers : on place le drapeau correspondant à la comparaison puis on met le résultat dans rdi *)
	let l = new_label () in
    (expr env e1) ++ movq (reg rdi) (reg rsi) ++ (expr env e2) ++ movq (reg rdi) (reg rdx)
	++ movq (imm 1) (reg rdi) ++ cmpq (reg rdx) (reg rsi) ++ (match op with | Blt -> jl | Ble -> jle | Bgt -> jg | Bge -> jge) l
	++ movq (imm 0) (reg rdi) ++ label l
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) -> (* opérations +, - et * pour les entiers *)
    (expr env e2) ++ movq (reg rdi) (reg rsi) ++ (expr env e1)
	++ (match op with | Badd -> addq | Bsub -> subq | Bmul -> imulq) (reg rsi) (reg rdi)
  | TEbinop (Bdiv | Bmod as op, e1, e2) -> (* opérations / et % pour les entiers *)
    (expr env e1) ++ movq (reg rdi) (reg rax) ++ (expr env e1) ++ movq (imm 0) (reg rdx)
	++ idivq (reg rdi) ++ movq (match op with | Bdiv -> (reg rax) | Bmod -> (reg rdx)) (reg rdi)
  | TEbinop (Beq | Bne as op, e1, e2) -> (* = et !=, mais seulement pour les entiers *)
    let l = new_label () in
    (expr env e1) ++ movq (reg rdi) (reg rsi) ++ (expr env e2) ++ movq (reg rdi) (reg rdx)
	++ movq (imm 1) (reg rdi) ++ cmpq (reg rsi) (reg rdi) ++ (match op with | Beq -> je | Bne -> jne) l
	++ movq (imm 0) (reg rdi) ++ label l
  | TEunop (Uneg, e1) -> (* négation d'entiers *)
    (expr env e1) ++ negq (reg rdi)
  | TEunop (Unot, e1) -> (* négation de booléens *)
    (expr env e1) ++ notq (reg rdi)
  | TEunop (Uamp, e1) ->
    (* TODO code pour & *) assert false 
  | TEunop (Ustar, e1) -> (* valeur d'un pointeur *)
    (expr env e1) ++ movq (ind rdi) (reg rdi)
  | TEprint el -> (* on a différentes fonctions pour print les différents types *)
    let rec aux = function
	| [] -> movq (ilab "S_newline") (reg rdi) ++ call "print_string"
	| t :: q -> begin
	  match t.expr_typ with
	  | Tint -> (expr env t) ++ call "print_int"
	  | Tbool -> let l = new_label in (expr env t) ++ testq (reg rdi) (reg rdi) ++ movq (ilab "false") (reg rdi) ++ je l ++ movq (ilab "true") (reg rdi) ++ label l ++ call "print_string"
	  | Tstring -> (expr env t) ++ call "print_string"
	  | _ -> failwith("not printable type, work in progress...")
	  end
	  ++ movq (ilab "S_space") (reg rdi) ++ call "print_string" ++ (aux q)
	in aux el
  | TEident x -> (* appel d'une variable *)
    movq (ind ~ofs:(Hashtbl.find env.vars x.v_id) rbp) (reg rdi)
  | TEassign ([{expr_desc=TEident x}], [e1]) -> (* assignation d'une valeur à une variable *)
    (expr env e1) ++ (match x.v_name with | "_" -> nop | _ -> movq (reg rdi) (ind ~ofs:(Hashtbl.find env.vars x.v_id) rbp))
  | TEassign (vl, el) -> (* assignations en parallèle *)
    let rec aux = function
	  | [], [] -> nop
	  | {expr_desc=TEident x} :: rv, e :: re -> (expr env e) ++ (match x.v_name with | "_" -> nop | _ -> movq (reg rdi) (ind ~ofs:(Hashtbl.find env.vars x.v_id) rbp)) ++ (aux (rv, re))
	in aux (vl, el)
  | TEassign (_, _) ->
     assert false
  | TEblock el -> (* traitement des blocs *)
    let rec aux = function
	  | [] -> nop
	  | e :: re -> (expr env e) ++ (aux re)
	in aux el
  | TEif (e1, e2, e3) -> (* if *)
    let l1 = new_label () in
	let l2 = new_label () in
    (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l1 ++ (expr env e1) ++ jmp l2 ++ label l1 ++ (expr env e2) ++ label l2
  | TEfor (e1, e2) -> (* for *)
    let l1 = new_label () in
    let l2 = new_label () in
	label l1 ++ (expr env e1) ++ testq (reg rdi) (reg rdi) ++ je l2 ++ (expr env e2) ++ jmp l1 ++ label l2
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) -> (* appel de fonction : on place tous les arguments sur la pile puis on sauvegarde %rbp et on appelle la fonction *)
    let rec aux = function
	  | [] -> nop
	  | e :: re -> (aux re) ++ (expre env e) ++ pushq (reg rdi)
	in aux el
	++ call ("F_" ^ f.fn_name)
	++ movq (reg rax) (reg rdi)
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars (vl, el) -> (* déclaration de variables et assignation de valeurs *)
    let rec aux = function
	  | [], [] -> nop
	  | v :: rv, e :: re -> begin
        env.current_ofs <- env.current_ofs - 8;
		Hashtbl.add env.vars v.v_id env.current_ofs;
		match e.expr_desc with 
		  | TEnil -> pushq (imm 0) ++ (aux reste)
		  | _ -> (expr env e) ++ pushq (reg rdi) ++ (aux reste)
	  end
	in aux (vl, el)
  | TEreturn [] -> (* retour de fonction de type unit *)
    movq (ind rbp) (reg rbp) ++ ret
  | TEreturn [e1] -> (* retour de fonction avec un seul élément, on le place dans %rax *)
    (expr env e1) ++ movq (reg rdi) (reg rax) ++ movq (reg rbp) (reg rsp) ++ movq (ind rbp) (reg rbp) ++ ret
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) ->
    (* TODO code pour return e++, e-- *) assert false

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  let env = new_env ("E_" ^ s) (Hashtbl.create 0) 0 in
  let rec aux ofs = function
    | [] -> ()
	| x :: rx -> Hashtbl.add env x.v_id ofs; aux (ofs + 8) rx
  in aux 8 f.fn_params;
  label ("F_" ^ s) ++ pushq (reg rbp) ++ movq (reg rsp) (reg rbp) ++ expr env e

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
	  label "print_string" ++ movq (reg rdi) (reg rsi) ++ movq (ilab "S_string") (reg rdi) ++ xorq (reg rax) (reg rax) ++ call "printf" ++ ret
   ;
   (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
	  label "S_string" ++ string "%s" ++
	  label "S_space" ++ string " " ++
	  label "S_newline" ++ string "\n"
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
