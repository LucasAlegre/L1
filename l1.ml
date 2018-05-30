type variable = string

(* Outros operadores binário e unários podem ser adicionados a linguagem *) 

type operator = Sum | Diff | Mult | Div | Eq | Neq | Leq | Less | Geq | Greater | Or | And

type tipo  = TyInt | TyBool | TyFn of tipo * tipo | TyList of tipo

type expr = Num of int 
          | Bool of bool 
          | Bop of operator * expr * expr
          | If of expr * expr * expr 
          | Var of variable 
          | App of expr * expr 
          | Lam of variable * tipo * expr 
          | Let of variable * tipo * expr * expr
          | Lrec of variable * tipo * tipo * variable * tipo * expr * expr
          | Nil                   (* Expressões adicionadas a partir daqui *)
          | Cons of expr * expr
          | IsEmpty of expr
          | Hd of expr
          | Tl of expr
          | Raise
          | TryWith of expr * expr
          (* Expressões com tipagem implícita *)
          | LamI of variable * expr
          | LetI of variable * expr * expr
          | LrecI of variable * variable * expr * expr

type value = Vnum of int 
           | Vbool of bool 
           | Vclos of variable * expr * env
           | Vrclos of variable * variable * expr * env
           | Vnil                     (* Valores adicionados a partir daqui *)
           | Vcons of value * value
           | Raise    (* Raise NÂO DEVIA SER VALOR, MAS NÃO SEI COMO FAZER *)
and  
     env = (variable * value) list 

exception NoRuleApplies of string

(* AVALIADOR BIG STEP *)
let rec _eval (contexto : env) (e : expr) = ( match e with 
    
    (* BS-NUM *)
    Num(n) -> Vnum(n)
    (* BS-BOOL*)
    | Bool(b) -> Vbool(b) 
    (* BS-OP *)
    | Bop(op, e1, e2) -> (
        let e1' = _eval contexto e1 in
        let e2' = _eval contexto e2 in (
            match(op, e1', e2') with
              (Sum, Vnum n1, Vnum n2) -> Vnum(n1 + n2)
            | (Diff, Vnum n1, Vnum n2) -> Vnum(n1 - n2)
            | (Mult, Vnum n1, Vnum n2) -> Vnum(n1 * n2)
            | (Eq, Vnum n1, Vnum n2) -> Vbool(n1 == n2)
            | (Neq, Vnum n1, Vnum n2) -> Vbool(n1 != n2)
            | (Leq, Vnum n1, Vnum n2) -> Vbool(n1 <= n2)
            | (Less, Vnum n1, Vnum n2) -> Vbool(n1 < n2)
            | (Geq, Vnum n1, Vnum n2) -> Vbool(n1 >= n2)
            | (Greater, Vnum n1, Vnum n2) -> Vbool(n1 > n2)
            | (Or, Vbool b1, Vbool b2) -> Vbool(b1 || b2)
            | (And, Vbool b1, Vbool b2) -> Vbool(b1 && b2)
            | (Div, Vnum n1, Vnum n2) -> if n2 != 0 then Vnum(n1 / n2) else Raise
            | (_, Raise, _) -> Raise
            | (_, _, Raise) -> Raise
            | _ -> raise (NoRuleApplies "Binary Operation Error")
        )
    )
    (* BS-IF *)
    | If(e1, e2, e3) -> ( 
        let e1' = _eval contexto e1 in (
            match e1' with
              (Vbool true) -> _eval contexto e2
            | (Vbool false) -> _eval contexto e3
            | Raise -> Raise
            | _ -> raise (NoRuleApplies "If condition Error")
        )
    )
    (* BS-ID *)
    | Var(x) -> (snd (List.find (fun (variable, _) -> String.compare variable x == 0) contexto))
    (* BS-APP *)
    | App(e1, e2) -> (
        let e1' = _eval contexto e1 in
        let e2' = _eval contexto e2 in (
            match(e1', e2') with
            | (Vclos(x, e, env'), v) -> _eval ((x,v)::env') e
            | (Vrclos(f, x, e, env'), v) -> _eval ((x,v)::(f,Vrclos(f,x,e,env'))::env') e
            | (Raise,_) -> Raise
            | (_,Raise) -> Raise 
            | _ -> raise (NoRuleApplies "Application Error")
        )
    )
    (* BS-FN *)
    | Lam(x, t, e) -> Vclos(x, e, contexto)
    | LamI(x, e) -> Vclos(x, e, contexto)
    (* BS-LET *)
    | Let(x, t, e1, e2) -> let e1' = (_eval contexto e1) in (
                               match e1' with
                               | Raise -> Raise
                               | _ -> _eval ((x,e1')::contexto) e2
                            )
    | LetI(x, e1, e2) -> let e1' = (_eval contexto e1) in (
                               match e1' with
                               | Raise -> Raise
                               | _ -> _eval ((x,e1')::contexto) e2
                            )
    (* BS-LETREC *)
    | Lrec(f,t1,t2,x,t1',e1,e2) -> let rclos = Vrclos(f,x,e1,contexto) in
                                       _eval ((f,rclos)::contexto) e2
    | LrecI(f,x,e1,e2) -> let rclos = Vrclos(f,x,e1,contexto) in
                                       _eval ((f,rclos)::contexto) e2
    (* BS-NIL *)
    | Nil -> Vnil
    (* BS-CONS *)
    | Cons(e1, e2) -> (
        let e1' = _eval contexto e1 in
        let e2' = _eval contexto e2 in (
            match (e1', e2') with
            | (Raise,_) -> Raise
            | (_,Raise) -> Raise
            | _ -> Vcons(e1',e2') 
        )
    )
    (* BS-ISEMPTY *)
    | IsEmpty(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vnil -> (Vbool true)
            | Vcons(v1,v2) -> (Vbool false)
            | Raise -> Raise
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-HEAD *)
    | Hd(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vcons(v1,v2) -> v1
            | Vnil -> Raise
            | Raise -> Raise 
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-TAIL *)
    | Tl(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vcons(v1,v2) -> v2
            | Vnil -> Raise
            | Raise -> Raise 
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-RAISE *)
    | Raise -> Raise
    (* BS-TRYWITH *)
    | TryWith(e1,e2) -> (
        let e1' = _eval contexto e1 in (
            match e1' with
            | Raise -> _eval contexto e2
            | _ -> e1' 
        )
    )
)

let eval e = _eval [] e

(* Segue um exemplo de como o programa L1 abaixo pode ser representado internamente *)

(* let rec fat: int -> int = (fn x: int => if (x == 0) then 1 else x * (fat (x - 1)))
   in fat (5)
   end
*)

let e1 = (Lrec("fat", TyInt, TyInt, "x", TyInt,
    If(Bop(Eq, Var("x"), Num(0)),
    Num(1),
    Bop(Mult, Var("x"), App(Var("fat"), Bop(Diff, Var("x"), Num(1))))),
    App(Var("fat"), Num(5))))

let e2 = Cons(Bop(Sum,Num(5),Num(2)),(Cons(Num(1),Nil)))

