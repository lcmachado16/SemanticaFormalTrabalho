(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)



(*+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(*===== Tipos ========== *)
type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo
  (*------- TRABALHO: NOVOS TIPOS ----------*)
  | TyList of tipo
  | TyMaybe of tipo
              
(*------ Tipos "auxiliares" ---------*)
type ident = string
type op = Sum | Sub | Mult | Div | Eq | Gt | Lt | Geq | Leq 

(*===== Expressoes ========== *)
type expr =
  | Num of int
  | Var of ident
  | Bool of bool
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
  (*------- TRABALHO: Novas Expressoes ----------*)
  (*---- tipo maybe -----*)
  | Nothing     of tipo
  | Just        of expr 
  | MatchMaybe  of expr * expr * ident * expr
  (*------ tipo list ----- *)
  | Nil       of tipo 
  | Cons      of expr * expr
  | MatchList of expr * expr * ident * ident * expr 
  | Map       of expr * expr

(*===== VALORES ========== *)
type valor = 
    VNum of int
  | VBool of bool
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRClos of ident * ident * expr * renv 
 (*------ TRABALHO: Novos Valores ---------*)
  | VNothing  of tipo
  | VJust     of valor
  | VNil      of tipo 
  | VCons     of valor * valor
  (* | Vlist of valor*valor *)

and  
  renv = (ident * valor) list
              
type tenv = (ident * tipo) list
  
(* exceções que não devem ocorrer  *) 
exception BugParser
  
(*++++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*) 

exception TypeError of string


let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with 
  | Num _ -> TyInt 
  | Var x ->
      (match List.assoc_opt x tenv with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x))) 
  | Bool _ -> TyBool 
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt 
      then
        (match oper with
           Sum | Sub | Mult |Div -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else 
        raise (TypeError "operando nao é do tipo int") 
  (*------ PARES -----------*)
  | Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2) 
  | Fst e1 ->
      (match typeinfer tenv e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par")) 
  | Snd e1 ->
      (match typeinfer tenv e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "snd espera tipo par")) 
  (*------- If ----------*)
  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool")) 
  | Fn(x,t,e1) ->
      let t1 = typeinfer ((x,t) :: tenv) e1
      in TyFn(t,t1) 
  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  
           if (typeinfer tenv e2) = t 
           then 
             t'
           else 
             raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado")) 
  (*------- Expressoes Let ----------*)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer ((x,t) :: tenv) e2
      else raise (TypeError "expressão nao é do tipo declarado em Let" ) 
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = (f,tf) :: tenv in
      let tenv_com_tf_tx = (x,tx) :: tenv_com_tf in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then 
        typeinfer tenv_com_tf e2
      else 
        raise (TypeError "tipo da funcao recursiva é diferente do declarado")
  | LetRec _ -> raise BugParser
  (*==========  TRABALHO: ==================================*)
  (*------ Nothing ---------------- *)
  | Nothing(t) -> TyMaybe t 
  (*------ Just ------------------- *)
  | Just(e) -> 
      let t = typeinfer tenv e in 
      TyMaybe t
  (*------ MatchMaybe ------------- *)
  | MatchMaybe(e,e1,ident,e2) ->
      let t1 = typeinfer tenv e1 in
      (
        match t1 with
        | TyMaybe t' ->
            let t1 = typeinfer tenv e1 in
            let extended_env = (ident, t') :: tenv in
            let t2 = typeinfer extended_env e2 in
            if t1 = t2 then t1
            else raise (TypeError "[T-MatchMB] e2 e e3 devem ser iguais")
        | _ -> raise (TypeError "[T-MatchMB] e1 deve ser do tipo Maybe")
      )
  (*========== LISTAS  ===============*)
  (*------ Nil  ----------- *)
  | Nil(t) -> TyList t
  (*------ Cons ----------- *)
  | Cons(e1,e2) ->
      let t1 = typeinfer tenv e1 in 
      let t2 = typeinfer tenv e2 in 
      ( match t2 with
        | TyList t when t = t1 -> TyList t1
        | _ -> raise (TypeError "[CONS] segundo argumento deve ser to mesmo tipo do primeiro")
      )

        
  (*------ Match List ----------- *)
  (* 
    Γ⊢e:listT'  Γ⊢e1 :T Γ,x:T′,xs:listT′ ⊢e2 :T
    ---------------------------------------------
    Γ⊢match e with nil -> e1 | x::xs → e2 :T
  *)
  | MatchList(e1, e2, head_ident, tail_ident, e3) ->
      let t1 = typeinfer tenv e1 in
      (
        match t1 with
        | TyList t ->
            let t2 = typeinfer tenv e2 in
            let extended_env = (head_ident, t) :: (tail_ident, TyList t) :: tenv in
            let t3 = typeinfer extended_env e3 in
            if t2 = t3 
            then 
              t2
            else 
              raise(TypeError  "[T-MatchList] e1 e2 devem ser do mesmo tipo"
                   )
        | _ -> raise (TypeError "[T-MatchList] e deve ser do tipo lista")
      )
  (*------ Map ----------- *)
  | Map(e1, e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      (
        match t1 with
          TyList t ->
            (
              match t2 with
                TyFn(t3, t4) ->
                  if t3 = t  then TyList t4
                 else 
                   raise   (TypeError "[Map] função não é do tipo esperado")
             | _ -> raise  (TypeError "[Map] segundo argumento não é uma função")
            )
        | _ -> raise       (TypeError "[MAP] primeiro argumento não é uma lista")) 
  (* | _ -> raise BugParser *)

  
(*++++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*) 
exception BugTypeInfer
exception NotImplementedYet

(* função auxiliar que computa a operação *)

let compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
    (Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
  | (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2) 
  | (Div, VNum(n1),VNum(n2))  -> VNum (n1 / n2)    
  | (Eq, VNum(n1), VNum(n2))  -> VBool (n1 = n2) 
  | (Gt, VNum(n1), VNum(n2))  -> VBool (n1 > n2)  
  | (Lt, VNum(n1), VNum(n2))  -> VBool (n1 < n2)  
  | (Geq, VNum(n1), VNum(n2)) -> VBool (n1 >= n2) 
  | (Leq, VNum(n1), VNum(n2)) -> VBool (n1 <= n2) 
  | _ -> raise BugTypeInfer


let rec eval (renv:renv) (e:expr) :valor =
  match e with
    Num n -> VNum n 
  | Var x ->
      (
        match List.assoc_opt x renv with
          Some v -> v
        | None -> raise BugTypeInfer 
      ) 
  | Bool b -> VBool b 
  | Binop(oper,e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2 
  | Pair(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2
      in VPair(v1,v2) 
  | Fst e ->
      (match eval renv e with
       | VPair(v1,_) -> v1
       | _ -> raise BugTypeInfer) 
  | Snd e ->
      (match eval renv e with
       | VPair(_,v2) -> v2
       | _ -> raise BugTypeInfer) 
  | If(e1,e2,e3) ->
      (match eval renv e1 with
         VBool true  -> eval renv e2
       | VBool false -> eval renv e3
       | _ -> raise BugTypeInfer ) 
  | Fn(x,_,e1)  -> VClos(x,e1, renv) 
  | App(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (match v1 with 
         VClos(   x,e',renv') ->
           eval  (         (x,v2) :: renv')  e' 
       | VRClos(f,x,e',renv') -> 
           eval  ((f,v1) ::(x,v2) :: renv')  e' 
       | _  -> raise BugTypeInfer) 
  | Let(x,_,e1,e2) ->
      let v1 = eval renv e1
      in eval ((x,v1) :: renv) e2 
  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'=  (f, VRClos(f,x,e1,renv)) :: renv
      in eval renv' e2 
  | LetRec _ -> raise BugParser 
    
  (* Novas expressões para Maybe *)
  | Nothing t -> VNothing t
  | Just e1 -> VJust (eval renv e1)
  | MatchMaybe (e1, e2, ident, e3) ->
      (match eval renv e1 with
         VNothing _ -> eval renv e2
       | VJust v -> eval ((ident, v) :: renv) e3
       | _ -> raise (TypeError "MatchMaybe espera um valor Maybe"))

  (*========== LISTAS  ===============*)
  (*------ Nil  ----------- *)
  | Nil t -> VNil t
  (*------ Cons ----------- *)
  | Cons (e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (
        match v2 with
          VNil t -> VCons (v1, v2)
          | VCons (_, _) -> VCons (v1, v2)
          | _ -> raise (TypeError "Cons espera uma lista como segundo argumento")
       )
  (*------ Match List ----------- *)
  | MatchList (e, e1, head_ident, tail_ident, e2) ->
      (match eval renv e with
         VNil _ -> eval renv e1
       | VCons (v1, v2) ->
           eval ((head_ident, v1) :: (tail_ident, v2) :: renv) e2
       | _ -> raise (TypeError "MatchList espera uma lista")
      )
  | Map (e , e1) ->
      let v1 = eval renv e in
      let v2 = eval renv e1 in
      (
        match v1 with
          VNil _ -> VNil (TyInt)
          | VCons (v1, v2) ->
            VCons (eval renv (App (v2, v1)), eval renv (Map (v2, v1)))
            | _ -> raise (TypeError "Map espera uma lista")
      )
  | _ -> raise NotImplementedYet


(*================ <Funcoes Auxiliares> ================================================*)
(* função auxiliar que converte tipo para string  *) 
let rec ttos (t:tipo) : string =
  match t with
    TyInt         -> "int"
  | TyBool        -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | TyList t      -> "list " ^ (ttos t)
  | TyMaybe t     -> "maybe " ^ (ttos t)

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
    VNum n          -> string_of_int n
  | VBool true      -> "true"
  | VBool false     -> "false"
  | VPair(v1, v2)   ->  "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _         ->  "fn"
  | VRClos _        -> "fn"
  | VNothing t      -> "nothing " ^ (ttos t)
  | VJust v         -> "just " ^ (vtos v)
  | VNil t          -> "nil " ^ (ttos t)
  | VCons (v1, v2)  -> "cons " ^ (vtos v1) ^ " " ^ (vtos v2)
  (* | Vlist of valor*valor -> "list " ^ (vtos v1) ^ " " ^ (vtos v2) *)


(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec" 
(*================ </Funcoes Auxiliares> ================================================*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES  
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*=========== TYPEINFER ============================================*)
(* ------- CONS -------------*)
let teste_cons = Cons (Num 1, Cons (Num 2, Nil TyInt))
(* Inferência de tipos para teste_cons *)
let tipo_cons = typeinfer [] teste_cons

(* ------- MATCHLIST-------------*)
let lista_test = Cons (Num 42, Nil TyInt)

(* Usando MatchList para verificar o primeiro elemento da lista *)
let teste_match_list =
  MatchList (lista_test,  (* Lista de teste *)
             Bool false,   (* Caso da lista vazia: retornar false *)
             "x",          (* Nome do identificador para o cabeçote *)
             "xs",         (* Nome do identificador para a cauda *)
             If (           (* Caso da lista não vazia *)
               Binop (Eq, Var "x", Num 42), (* Verifica se o cabeçote é 42 *)
               Bool true,   (* Se verdadeiro, retorna true *)
               Bool false   (* Caso contrário, retorna false *)
             )
            )
(* ------- Map-------------*)
(* Função de incremento *)
let incremento_fn = Fn ("x", TyInt, Binop (Sum, Var "x", Num 1))

(* Lista de números *)
let lista_numeros = Cons (Num 1, Cons (Num 2, Cons (Num 3, Nil TyInt)))

(* Map aplicando incremento_fn à lista_numeros *)
let teste_map = Map (lista_numeros, incremento_fn)

(* Inferência de tipos para teste_map *)
let tipo_teste_map = typeinfer [] teste_map
         

          (*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)



(*+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(*===== Tipos ========== *)
type tipo =
TyInt
| TyBool
| TyFn of tipo * tipo
| TyPair of tipo * tipo
(*------- TRABALHO: NOVOS TIPOS ----------*)
| list of tipo
| maybe of tipo
          
(*------ Tipos "auxiliares" ---------*)
type ident = string
type op = Sum | Sub | Mult | Div | Eq | Gt | Lt | Geq | Leq 

(*===== Expressoes ========== *)
type expr =
| Num of int
| Var of ident
| Bool of bool
| Binop of op * expr * expr
| Pair of expr * expr
| Fst of expr
| Snd of expr
| If of expr * expr * expr
| Fn of ident * tipo * expr
| App of expr * expr
| Let of ident * tipo * expr * expr
| LetRec of ident * tipo * expr  * expr
(*------- TRABALHO: Novas Expressoes ----------*)
(*---- tipo maybe -----*)
| Nothing     of tipo
| Just        of expr 
| MatchMaybe  of expr * expr * ident * expr
(*------ tipo list ----- *)
| Nil       of tipo 
| Cons      of expr * expr
| MatchList of expr * expr * ident * ident * expr 
| Map       of expr * expr

(*===== VALORES ========== *)
type valor = 
VNum of int
| VBool of bool
| VPair of valor * valor
| VClos  of ident * expr * renv
| VRClos of ident * ident * expr * renv 
(*------ TRABALHO: Novos Valores ---------*)
| VNothing  of tipo
| VJust     of valor
| VNil      of tipo 
| VCons     of valor * valor
(* | Vlist of valor*valor *)

and  
renv = (ident * valor) list
          
type tenv = (ident * tipo) list

(* exceções que não devem ocorrer  *) 
exception BugParser

(*++++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*) 

exception TypeError of string


let rec typeinfer (tenv:tenv) (e:expr) : tipo =
match e with 
| Num _ -> TyInt 
| Var x ->
  (match List.assoc_opt x tenv with
     Some t -> t
   | None -> raise (TypeError ("variavel nao declarada:" ^ x))) 
| Bool _ -> TyBool 
| Binop(oper,e1,e2) ->
  let t1 = typeinfer tenv e1 in
  let t2 = typeinfer tenv e2 in
  if t1 = TyInt && t2 = TyInt 
  then
    (match oper with
       Sum | Sub | Mult |Div -> TyInt
     | Eq | Lt | Gt | Geq | Leq -> TyBool)
  else 
    raise (TypeError "operando nao é do tipo int") 
(*------ PARES -----------*)
| Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2) 
| Fst e1 ->
  (match typeinfer tenv e1 with
     TyPair(t1,_) -> t1
   | _ -> raise (TypeError "fst espera tipo par")) 
| Snd e1 ->
  (match typeinfer tenv e1 with
     TyPair(_,t2) -> t2
   | _ -> raise (TypeError "snd espera tipo par")) 
(*------- If ----------*)
| If(e1,e2,e3) ->
  (match typeinfer tenv e1 with
     TyBool ->
       let t2 = typeinfer tenv e2 in
       let t3 = typeinfer tenv e3
       in if t2 = t3 then t2
       else raise (TypeError "then/else com tipos diferentes")
   | _ -> raise (TypeError "condição de IF não é do tipo bool")) 
| Fn(x,t,e1) ->
  let t1 = typeinfer ((x,t) :: tenv) e1
  in TyFn(t,t1) 
| App(e1,e2) ->
  (match typeinfer tenv e1 with
     TyFn(t, t') ->  
       if (typeinfer tenv e2) = t 
       then 
         t'
       else 
         raise (TypeError "tipo argumento errado" )
   | _ -> raise (TypeError "tipo função era esperado")) 
(*------- Expressoes Let ----------*)
| Let(x,t,e1,e2) ->
  if (typeinfer tenv e1) = t then typeinfer ((x,t) :: tenv) e2
  else raise (TypeError "expressão nao é do tipo declarado em Let" ) 
| LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
  let tenv_com_tf = (f,tf) :: tenv in
  let tenv_com_tf_tx = (x,tx) :: tenv_com_tf in
  if (typeinfer tenv_com_tf_tx e1) = t2
  then 
    typeinfer tenv_com_tf e2
  else 
    raise (TypeError "tipo da funcao recursiva é diferente do declarado")
| LetRec _ -> raise BugParser
(*==========  TRABALHO: ==================================*)
(*------ Nothing ---------------- *)
| Nothing(t) -> maybe t 
(*------ Just ------------------- *)
| Just(e) -> 
  let t = typeinfer tenv e in 
  maybe t
(*------ MatchMaybe ------------- *)
| MatchMaybe(e,e1,ident,e2) ->
  let t1 = typeinfer tenv e1 in
  (
    match t1 with
    | maybe t' ->
        let t1 = typeinfer tenv e1 in
        let extended_env = (ident, t') :: tenv in
        let t2 = typeinfer extended_env e2 in
        if t1 = t2 then t1
        else raise (TypeError "[T-MatchMB] e2 e e3 devem ser iguais")
    | _ -> raise (TypeError "[T-MatchMB] e1 deve ser do tipo Maybe")
  )
(*========== LISTAS  ===============*)
(*------ Nil  ----------- *)
| Nil(t) -> list t
(*------ Cons ----------- *)
| Cons(e1,e2) ->
  let t1 = typeinfer tenv e1 in 
  let t2 = typeinfer tenv e2 in 
  ( match t2 with
    | list t when t = t1 -> list t1
    | _ -> raise (TypeError "[CONS] segundo argumento deve ser to mesmo tipo do primeiro")
  )

    
(*------ Match List ----------- *)
(* 
Γ⊢e:listT'  Γ⊢e1 :T Γ,x:T′,xs:listT′ ⊢e2 :T
---------------------------------------------
Γ⊢match e with nil -> e1 | x::xs → e2 :T
*)
| MatchList(e1, e2, head_ident, tail_ident, e3) ->
  let t1 = typeinfer tenv e1 in
  (
    match t1 with
    | list t ->
        let t2 = typeinfer tenv e2 in
        let extended_env = (head_ident, t) :: (tail_ident, list t) :: tenv in
        let t3 = typeinfer extended_env e3 in
        if t2 = t3 
        then 
          t2
        else 
          raise(TypeError  "[T-MatchList] e1 e2 devem ser do mesmo tipo"
               )
    | _ -> raise (TypeError "[T-MatchList] e deve ser do tipo lista")
  )
(*------ Map ----------- *)
| Map(e1, e2) ->
  let t1 = typeinfer tenv e1 in
  let t2 = typeinfer tenv e2 in
  (
    match t1 with
      list t ->
        (
          match t2 with
            TyFn(t3, t4) ->
              if t3 = t  then list t4
             else 
               raise   (TypeError "[Map] função não é do tipo esperado")
         | _ -> raise  (TypeError "[Map] segundo argumento não é uma função")
        )
    | _ -> raise       (TypeError "[MAP] primeiro argumento não é uma lista")) 
(* | _ -> raise BugParser *)


(*++++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*) 
exception BugTypeInfer
exception NotImplementedYet

(* função auxiliar que computa a operação *)

let compute (oper: op) (v1: valor) (v2: valor) : valor =
match (oper, v1, v2) with
(Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
| (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
| (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2) 
| (Div, VNum(n1),VNum(n2))  -> VNum (n1 / n2)    
| (Eq, VNum(n1), VNum(n2))  -> VBool (n1 = n2) 
| (Gt, VNum(n1), VNum(n2))  -> VBool (n1 > n2)  
| (Lt, VNum(n1), VNum(n2))  -> VBool (n1 < n2)  
| (Geq, VNum(n1), VNum(n2)) -> VBool (n1 >= n2) 
| (Leq, VNum(n1), VNum(n2)) -> VBool (n1 <= n2) 
| _ -> raise BugTypeInfer


let rec eval (renv:renv) (e:expr) :valor =
match e with
Num n -> VNum n 
| Var x ->
  (
    match List.assoc_opt x renv with
      Some v -> v
    | None -> raise BugTypeInfer 
  ) 
| Bool b -> VBool b 
| Binop(oper,e1,e2) ->
  let v1 = eval renv e1 in
  let v2 = eval renv e2 in
  compute oper v1 v2 
| Pair(e1,e2) ->
  let v1 = eval renv e1 in
  let v2 = eval renv e2
  in VPair(v1,v2) 
| Fst e ->
  (match eval renv e with
   | VPair(v1,_) -> v1
   | _ -> raise BugTypeInfer) 
| Snd e ->
  (match eval renv e with
   | VPair(_,v2) -> v2
   | _ -> raise BugTypeInfer) 
| If(e1,e2,e3) ->
  (match eval renv e1 with
     VBool true  -> eval renv e2
   | VBool false -> eval renv e3
   | _ -> raise BugTypeInfer ) 
| Fn(x,_,e1)  -> VClos(x,e1, renv) 
| App(e1,e2) ->
  let v1 = eval renv e1 in
  let v2 = eval renv e2 in
  (match v1 with 
     VClos(   x,e',renv') ->
       eval  (         (x,v2) :: renv')  e' 
   | VRClos(f,x,e',renv') -> 
       eval  ((f,v1) ::(x,v2) :: renv')  e' 
   | _  -> raise BugTypeInfer) 
| Let(x,_,e1,e2) ->
  let v1 = eval renv e1
  in eval ((x,v1) :: renv) e2 
| LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
  let renv'=  (f, VRClos(f,x,e1,renv)) :: renv
  in eval renv' e2 
| LetRec _ -> raise BugParser 

(* Novas expressões para Maybe *)
| Nothing t -> VNothing t
| Just e1 -> VJust (eval renv e1)
| MatchMaybe (e1, e2, ident, e3) ->
  (match eval renv e1 with
     VNothing _ -> eval renv e2
   | VJust v -> eval ((ident, v) :: renv) e3
   | _ -> raise (TypeError "MatchMaybe espera um valor Maybe"))

(*========== LISTAS  ===============*)
(*------ Nil  ----------- *)
| Nil t -> VNil t
(*------ Cons ----------- *)
| Cons (e1, e2) ->
  let v1 = eval renv e1 in
  let v2 = eval renv e2 in
  (
    match v2 with
      VNil t -> VCons (v1, v2)
      | VCons (_, _) -> VCons (v1, v2)
      | _ -> raise (TypeError "Cons espera uma lista como segundo argumento")
   )
(*------ Match List ----------- *)
| MatchList (e, e1, head_ident, tail_ident, e2) ->
  (match eval renv e with
     VNil _ -> eval renv e1
   | VCons (v1, v2) ->
       eval ((head_ident, v1) :: (tail_ident, v2) :: renv) e2
   | _ -> raise (TypeError "MatchList espera uma lista")
  )
| Map (e , e1) ->
  let v1 = eval renv e in
  let v2 = eval renv e1 in
  (
    match v1 with
      VNil _ -> VNil (TyInt)
      | VCons (v1, v2) ->
        VCons (eval renv (App (v2, v1)), eval renv (Map (v2, v1)))
        | _ -> raise (TypeError "Map espera uma lista")
  )
| _ -> raise NotImplementedYet


(*================ <Funcoes Auxiliares> ================================================*)
(* função auxiliar que converte tipo para string  *) 
let rec ttos (t:tipo) : string =
match t with
TyInt         -> "int"
| TyBool        -> "bool"
| TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
| TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
| list t      -> "list " ^ (ttos t)
| maybe t     -> "maybe " ^ (ttos t)

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
match v with
VNum n          -> string_of_int n
| VBool true      -> "true"
| VBool false     -> "false"
| VPair(v1, v2)   ->  "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
| VClos _         ->  "fn"
| VRClos _        -> "fn"
| VNothing t      -> "nothing " ^ (ttos t)
| VJust v         -> "just " ^ (vtos v)
| VNil t          -> "nil " ^ (ttos t)
| VCons (v1, v2)  -> "cons " ^ (vtos v1) ^ " " ^ (vtos v2)
(* | Vlist of valor*valor -> "list " ^ (vtos v1) ^ " " ^ (vtos v2) *)


(* principal do interpretador *)

let int_bse (e:expr) : unit =
try
let t = typeinfer [] e in
let v = eval [] e
in  print_string ((vtos v) ^ " : " ^ (ttos t))
with
TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
| BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
| BugParser     ->  print_string "corrigir bug no parser para let rec" 
(*================ </Funcoes Auxiliares> ================================================*)
(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES TESTES  
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(*=========== TYPEINFER ============================================*)
(* ------- CONS -------------*)
let teste_cons = Cons (Num 1, Cons (Num 2, Nil TyInt))
(* Inferência de tipos para teste_cons *)
let tipo_cons = typeinfer [] teste_cons

(* ------- MATCHLIST-------------*)
let lista_test = Cons (Num 42, Nil TyInt)

(* Usando MatchList para verificar o primeiro elemento da lista *)
let teste_match_list =
MatchList (lista_test,  (* Lista de teste *)
         Bool false,   (* Caso da lista vazia: retornar false *)
         "x",          (* Nome do identificador para o cabeçote *)
         "xs",         (* Nome do identificador para a cauda *)
         If (           (* Caso da lista não vazia *)
           Binop (Eq, Var "x", Num 42), (* Verifica se o cabeçote é 42 *)
           Bool true,   (* Se verdadeiro, retorna true *)
           Bool false   (* Caso contrário, retorna false *)
         )
        )
(* ------- Map-------------*)
(* Função de incremento *)
let incremento_fn = Fn ("x", TyInt, Binop (Sum, Var "x", Num 1))

(* Lista de números *)
let lista_numeros = Cons (Num 1, Cons (Num 2, Cons (Num 3, Nil TyInt)))

(* Map aplicando incremento_fn à lista_numeros *)
let teste_map = Map (lista_numeros, incremento_fn)

(* Inferência de tipos para teste_map *)
let tipo_teste_map = typeinfer [] teste_map
     

let rec lookup: int -> (int * int) list -> maybe in  = 
fn k:int => fn l: (int*int) list =>
match l with 
  nil      -> nothing 
| x :: xs -> if (fst x) = k 
    then just (snd x)
    else lookup k xs  in 

let base_dados : (int * int) list =  [(1,10), (2,20), (3,30), (4,40), (5,50)] in

let key:int = 3 in 

match lookup key base_dados with
noting -> 0
| just n -> n


let rec list_max: int list -> maybe int  = 
fn l:int list =>
match l with 
| nil -> nothing
| h :: t -> (
    match list_max t with
    | noting -> just h
    | just m -> just (if h >= m then h else m))
