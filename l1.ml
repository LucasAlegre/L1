type variable = string

(* Outros operadores binário e unários podem ser adicionados a linguagem *) 

type operator = Sum | Diff | Mult | Div | Eq | Neq | Leq | Less | Geq | Greater | Or | And

type tipo  = TyInt | TyBool | TyFn of tipo * tipo | TyList of tipo | TyId of string

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


type nextuvar = NextUVar of string * uvargenerator
and uvargenerator = unit -> nextuvar

let uvargen =
  let rec f n () = NextUVar("?X_" ^ string_of_int n, f (n+1))
  in f 0

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


let rec recon ctx nextuvar t = match t with
  | App(t1,t2) ->
    let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
    let (tyT2,nextuvar2,constr2) = recon ctx nextuvar1 t2 in
    let NextUVar(tyX,nextuvar') = nextuvar2() in
    let newconstr = [(tyT1,TyFn(tyT2,TyId(tyX)))] in
    ((TyId(tyX)), nextuvar',
    List.concat [newconstr; constr1; constr2])
  | Num(t) -> (TyInt, nextuvar, [])
  | Bool(t) -> (TyBool, nextuvar, [])
  | If(t1,t2,t3) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = recon ctx nextuvar1 t2 in
      let (tyT3,nextuvar3,constr3) = recon ctx nextuvar2 t3 in
      let newconstr = [(tyT1,TyBool); (tyT2,tyT3)] in
      (tyT3, nextuvar3,
      List.concat [newconstr; constr1; constr2; constr3])
  | Raise ->
    let NextUVar(tyX,nextuvar') = nextuvar() in
    (TyId(tyX), nextuvar', [])
  | Nil ->
    let NextUVar(tyX,nextuvar') = nextuvar() in
    (TyList(TyId(tyX)), nextuvar', [])
  | IsEmpty(t) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
        ((TyId(tyX)), nextuvar',
        List.concat [newconstr; constr1])
  | TryWith(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = recon ctx nextuvar1 t2 in
      let newconstr = [(tyT1,tyT2)] in
      (tyT2, nextuvar2,
      List.concat [newconstr; constr1; constr2])
  | Hd(t1) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr1])
  | Tl(t1) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr1])
  | Cons(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = recon ctx nextuvar1 t2 in
      let newconstr = [(TyList tyT1,tyT2)] in
      (tyT2, nextuvar2,
      List.concat [newconstr; constr1; constr2])
  | Let(t1,t2,t3,t4) ->
      let (tyT3,nextuvar3,constr3) = recon ctx nextuvar t3 in
      let (tyT4,nextuvar4,constr4) = recon ctx nextuvar3 t4 in
      let newconstr = [(t2, tyT3)] in
      (tyT4, nextuvar4,
      List.concat [newconstr; constr3; constr4])
  | Lrec(t1,t2,t3,t4,t5,t6,t7) ->
      let (tyT6,nextuvar6,constr6) = recon ctx nextuvar t6 in
      let (tyT7,nextuvar7,constr7) = recon ctx nextuvar6 t7 in
      let newconstr = [(t3, tyT6)] in
      (tyT7, nextuvar7,
      List.concat [newconstr; constr6; constr7])
  | LetI(t1,t2,t3) ->
      let (tyT2,nextuvar2,constr2) = recon ctx nextuvar t2 in
      let (tyT3,nextuvar3,constr3) = recon ctx nextuvar2 t3 in
      let NextUVar(tyX,nextuvar') = nextuvar3() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr2; constr3])
  | LrecI(t1,t2,t3,t4) ->
      let (tyT3,nextuvar3,constr3) = recon ctx nextuvar t3 in
      let (tyT4,nextuvar4,constr4) = recon ctx nextuvar3 t4 in
      let NextUVar(tyX,nextuvar') = nextuvar4() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr3; constr4])
  | Bop(t1,t2,t3) -> (
      match t1 with
        | Sum ->
            let (tyT2,nextuvar2,constr2) = recon ctx nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = recon ctx nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT2, TyInt)] in
            (tyT3, nextuvar3,
            List.concat [newconstr; constr2; constr3])
        | _  ->
            let (tyT2,nextuvar2,constr2) = recon ctx nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = recon ctx nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT2, TyInt)] in
            (tyT3, nextuvar3,
            List.concat [newconstr; constr2; constr3])
        )


let getbinding (ctx) (i) =
  List.nth ctx i

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
