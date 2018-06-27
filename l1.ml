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
           | VRaise
and
     env = (variable * value) list
and
     tyenv = (variable * tipo) list
and
     tyeqs = (tipo * tipo) list

(* Novas variáveis para a coleta de tipos *)
type nextuvar = NextUVar of string * uvargenerator
and uvargenerator = unit -> nextuvar

let uvargen =
  let rec f n () = NextUVar("?X_" ^ string_of_int n, f (n+1))
  in f 0

(*****************************************)

(* AVALIADOR BIG STEP *)
exception NoRuleApplies of string
let rec _eval (contexto : env) (e : expr) : value = ( match e with

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
            | (Div, Vnum n1, Vnum n2) -> if n2 != 0 then Vnum(n1 / n2) else VRaise
            | (_, VRaise, _) -> VRaise
            | (_, _, VRaise) -> VRaise
            | _ -> raise (NoRuleApplies "Binary Operation Error")
        )
    )
    (* BS-IF *)
    | If(e1, e2, e3) -> (
        let e1' = _eval contexto e1 in (
            match e1' with
              (Vbool true) -> _eval contexto e2
            | (Vbool false) -> _eval contexto e3
            | VRaise -> VRaise
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
            | (VRaise,_) -> VRaise
            | (_,VRaise) -> VRaise
            | _ -> raise (NoRuleApplies "Application Error")
        )
    )
    (* BS-FN *)
    | Lam(x, t, e) -> Vclos(x, e, contexto)
    | LamI(x, e) -> Vclos(x, e, contexto)
    (* BS-LET *)
    | Let(x, t, e1, e2) -> let e1' = (_eval contexto e1) in (
                               match e1' with
                               | VRaise -> VRaise
                               | _ -> _eval ((x,e1')::contexto) e2
                            )
    | LetI(x, e1, e2) -> let e1' = (_eval contexto e1) in (
                               match e1' with
                               | VRaise -> VRaise
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
            | (VRaise,_) -> VRaise
            | (_,VRaise) -> VRaise
            | _ -> Vcons(e1',e2')
        )
    )
    (* BS-ISEMPTY *)
    | IsEmpty(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vnil -> (Vbool true)
            | Vcons(v1,v2) -> (Vbool false)
            | VRaise -> VRaise
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-HEAD *)
    | Hd(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vcons(v1,_) -> v1
            | Vnil -> VRaise
            | VRaise -> VRaise
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-TAIL *)
    | Tl(e) -> (
        let e' = _eval contexto e in (
            match e' with
            | Vcons(_,v2) -> v2
            | Vnil -> VRaise
            | VRaise -> VRaise
            | _ -> raise (NoRuleApplies "Invalid list")
        )
    )
    (* BS-RAISE *)
    | Raise -> VRaise
    (* BS-TRYWITH *)
    | TryWith(e1,e2) -> (
        let e1' = _eval contexto e1 in (
            match e1' with
            | VRaise -> _eval contexto e2
            | _ -> e1'
        )
    )
)

let eval (e: expr) : value = _eval [] e
(**********************************************************)


(** Auxiliares para testes **)
(* Transforma um tipo em uma STRING *)
let rec tipoToString (tp:tipo) : string =
  match tp with
  | TyBool -> "bool"
  | TyInt  -> "int"
  | TyList a -> (tipoToString a) ^ " list"
  | TyFn(tp1,tp2) -> "(" ^ (tipoToString tp1) ^ " -> " ^ (tipoToString tp2) ^ ")"
  | TyId(tp) -> "TyId:" ^ tp
;;

let rec valueToString (tp:value) : string =
  match tp with
  | Vbool(v1) -> "bool"
  | Vnum(v1)  -> "int"
  | Vclos (var1, expr1, env1) -> " clos"
  | Vrclos(var1,var2,expr1,env) -> "rclos"
  | Vnil -> "vnil"
  | Vcons(val1, val2) -> "vcons"
  | VRaise -> "raise"
;;

let valueToTipo (tp:value) : tipo =
  match tp with
  | Vbool(v1) -> TyBool
  | Vnum(v1)  -> TyInt
  | Vrclos(var1, var2, expr1, env1) -> TyFn(TyId(var1), TyId(var2))
  | Vclos(var1, expr1, env1) -> TyId(var1)
  | _ -> TyId("naosei")
;;

(* Transforma uma expressao em uma STRING *)
let rec exprToString (t:expr) : string =
  match t with
  | Num(x) -> string_of_int x
  | Bool(true) -> "true"
  | Bool(false) -> "false"
  | Hd(t1) -> "( Head " ^ (exprToString t1) ^ ")"
  | Tl(t1) -> "( Tail " ^ (exprToString t1) ^ ")"
  | IsEmpty (t1) -> "( IsEmpty " ^ (exprToString t1) ^ ")"
  | Bop(Sum,t1,t2) -> "(" ^ (exprToString t1) ^ " + " ^ (exprToString t2) ^ ")"
  | Bop(Eq,t1,t2) -> "(" ^ (exprToString t1) ^ " == " ^ (exprToString t2) ^ ")"
  | Bop(Diff,t1,t2) -> "(" ^ (exprToString t1) ^ " - " ^ (exprToString t2) ^ ")"
  | Bop(Mult,t1,t2) -> "(" ^ (exprToString t1) ^ " * " ^ (exprToString t2) ^ ")"
  | Bop(Div,t1,t2) -> "(" ^ (exprToString t1) ^ " / " ^ (exprToString t2) ^ ")"
  | Bop(Neq,t1,t2) -> "(" ^ (exprToString t1) ^ " != " ^ (exprToString t2) ^ ")"
  | Bop(Leq,t1,t2) -> "(" ^ (exprToString t1) ^ " <= " ^ (exprToString t2) ^ ")"
  | Bop(Less,t1,t2) -> "(" ^ (exprToString t1) ^ " < " ^ (exprToString t2) ^ ")"
  | Bop(Geq,t1,t2) -> "(" ^ (exprToString t1) ^ " >= " ^ (exprToString t2) ^ ")"
  | Bop(Greater,t1,t2) -> "(" ^ (exprToString t1) ^ " > " ^ (exprToString t2) ^ ")"
  | Bop(Or,t1,t2) -> "(" ^ (exprToString t1) ^ " || " ^ (exprToString t2) ^ ")"
  | Bop(And,t1,t2) -> "(" ^ (exprToString t1) ^ " && " ^ (exprToString t2) ^ ")"
  | If(t1,t2,t3) -> "(if " ^ (exprToString t1) ^ " then " ^ (exprToString t2) ^ " else " ^ (exprToString t3) ^ ")"
  | Var(x) -> x
  | App(t1,t2) -> "(" ^ (exprToString t1) ^ " " ^ (exprToString t2) ^ ")"
  | Lam(x,tp,t1) -> "(fun " ^ x ^ ":" ^ (tipoToString tp) ^ "=>" ^ (exprToString t1) ^ ")"
  | Let(x,tp,t1,t2) -> "(let " ^ x ^ ":" ^ (tipoToString tp) ^ "=" ^ (exprToString t1) ^ " in " ^ (exprToString t2) ^ ")"
  | Lrec(x,tp,t1,t2,t3,t4,t5) -> "(let rec " ^ x ^ ":" ^ (tipoToString tp) ^ "->" ^ (tipoToString t1) ^ " = (fn )" ^ t2 ^ ":" ^(tipoToString t3) ^ (exprToString t4) ^ " in " ^ (exprToString t5) ^ ")"
  | LamI(t1,t2) -> "(fun " ^ t1 ^ "=>" ^ (exprToString t2) ^ ")"
  | LetI(t1,t2,t3) -> "(let " ^ t1 ^ "=" ^ (exprToString t2) ^ " in " ^ (exprToString t3) ^ ")"
  | LrecI(t1,t2,t3,t4) -> "(let rec " ^ t1 ^ " = (fn )" ^ t2  ^ (exprToString t3) ^ " in " ^ (exprToString t4) ^ ")"
  | Nil -> "Nil";
  | Raise -> "Raise";
  | Cons(a,b) -> "(" ^ (exprToString a) ^ "::" ^ (exprToString b) ^ ")"
  | TryWith(a,b) -> "(try" ^ (exprToString a) ^ " with " ^ (exprToString b) ^ ")"
;;

let rec listToString (lista: tyeqs) =  match lista with
    | (head::tail) ->
        (match head with
          | t1, t2 -> print_endline ("(" ^ (tipoToString t1) ^ " --- " ^ (tipoToString t2) ^ ")"))
        ;
        listToString tail;
    | [] -> ();;

(*************************************************************)


(**** Collect type equations ****)
exception UndeclaredVariable of string

let rec collectTyEqs_rec (tyEnv:tyenv) (nextuvar:uvargenerator) (expression:expr) = match expression with
  | App(t1,t2) ->
    let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
    let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar1 t2 in
    let NextUVar(tyX,nextuvar') = nextuvar2() in
    let newconstr = [(tyT1,TyFn(tyT2,TyId(tyX)))] in
    ((TyId(tyX)), nextuvar',
    List.concat [newconstr; constr1; constr2])
  | Num(t) -> (TyInt, nextuvar, [])
  | Bool(t) -> (TyBool, nextuvar, [])
  | If(t1,t2,t3) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar1 t2 in
      let (tyT3,nextuvar3,constr3) = collectTyEqs_rec tyEnv nextuvar2 t3 in
      let newconstr = [(tyT1,TyBool); (tyT2,tyT3)] in
      (tyT3, nextuvar3, List.concat [newconstr; constr1; constr2; constr3])
  | Raise ->
    let NextUVar(tyX,nextuvar') = nextuvar() in
    (TyId(tyX), nextuvar', [])
  | Nil ->
    let NextUVar(tyX,nextuvar') = nextuvar() in
    (TyList(TyId(tyX)), nextuvar', [])
  | IsEmpty(t) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      (TyBool, nextuvar', List.concat [newconstr; constr1])
  | TryWith(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar1 t2 in
      let newconstr = [(tyT1,tyT2)] in
      (tyT2, nextuvar2, List.concat [newconstr; constr1; constr2])
  | Hd(t1) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      ((TyId(tyX)), nextuvar', List.concat [newconstr; constr1])
  | Tl(t1) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      (TyList((TyId(tyX))), nextuvar', List.concat [newconstr; constr1])
  | Cons(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar1 t2 in
      let newconstr = [(TyList tyT1,tyT2)] in
      (tyT2, nextuvar2, List.concat [newconstr; constr1; constr2])
  | Let(var1,t2,expr1,expr2) ->
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec tyEnv nextuvar expr1 in
      let NextUVar(tyX1,nextuvar2) = nextuvar1() in
      let newctx = [(var1,TyId(tyX1))] in
      let (tyT2,nextuvar3,constr2) = collectTyEqs_rec (List.concat [newctx;tyEnv]) nextuvar2 expr2 in
      let newconstr = [(t2, tyT1)] in
      (tyT2, nextuvar3, List.concat [newconstr; constr1; constr2])
  | Lrec(var1,t1,t2,var2,t3,expr1,expr2) ->
      let firstctx = [(var1, TyFn(t1,t2))] in
      let secondctx = [(var2, t3)] in
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec (List.concat [secondctx;firstctx;tyEnv]) nextuvar expr1 in
      let (tyT2,nextuvar2,constr2) = collectTyEqs_rec (List.concat [firstctx;tyEnv]) nextuvar1 expr2 in
      let newconstr = [(t3, tyT1)] in
      (tyT2, nextuvar2, List.concat [newconstr; constr1; constr2])
  | LetI(var1,expr1,expr2) ->
      let (tyT2,nextuvar1,constr2) = collectTyEqs_rec tyEnv nextuvar expr1 in
      let NextUVar(tyX1,nextuvar2) = nextuvar1() in
      let newctx = [(var1,TyId(tyX1))] in
      let (tyT3,nextuvar3,constr3) = collectTyEqs_rec (List.concat [newctx;tyEnv]) nextuvar2 expr2 in
      let NextUVar(tyX,nextuvar4) = nextuvar3() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar4, List.concat [newconstr; constr2; constr3])
  | LrecI(var1,var2,expr1,expr2) ->
      let NextUVar(tyX1,nextuvar1) = nextuvar() in
      let firstctx = [(var1, TyId(tyX1))] in
      let NextUVar(tyX2,nextuvar2) = nextuvar1() in
      let secondctx = [(var2, TyId(tyX2))] in
      let (tyT3,nextuvar3,constr3) = collectTyEqs_rec (List.concat [secondctx;firstctx;tyEnv]) nextuvar2 expr1 in
      let (tyT4,nextuvar4,constr4) = collectTyEqs_rec (List.concat [firstctx;tyEnv]) nextuvar3 expr2 in
      let NextUVar(tyX,nextuvar5) = nextuvar4() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar5, List.concat [newconstr; constr3; constr4])
  | Lam(v1,t1,e1) ->
      let newctx = [(v1,t1)] in
      let (tyT1,nextuvar1,constr1) = collectTyEqs_rec (List.concat [newctx;tyEnv]) nextuvar e1 in
      (TyFn(t1,tyT1), nextuvar1, List.concat [constr1])
  | LamI(v1,e1) ->
      let NextUVar(tyX1,nextuvar1) = nextuvar() in
      let newctx = [(v1,TyId(tyX1))] in
      let (tyT1,nextuvar2,constr1) = collectTyEqs_rec (List.concat [newctx;tyEnv]) nextuvar1 e1 in
      (TyFn(TyId(tyX1),tyT1), nextuvar2, List.concat [constr1])
  | Var(e1) ->
    (try (let term = (snd (List.find (fun (variable, _) -> String.compare variable e1 == 0) tyEnv)) in term, nextuvar, [])
    with _ -> raise (UndeclaredVariable "Didn't found variable in context"))
  | Bop(t1,t2,t3) -> (
      (match t1 with
        | Eq | Neq | Leq | Less | Geq |Greater ->
            let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = collectTyEqs_rec tyEnv nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT3, TyInt)] in
            (TyBool, nextuvar3, List.concat [newconstr; constr2; constr3])
        | Or | And ->
            let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = collectTyEqs_rec tyEnv nextuvar2 t3 in
            let newconstr = [(tyT2, TyBool);(tyT3, TyBool)] in
            (TyBool, nextuvar3, List.concat [newconstr; constr2; constr3])
        | Sum | Diff | Mult | Div->
            let (tyT2,nextuvar2,constr2) = collectTyEqs_rec tyEnv nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = collectTyEqs_rec tyEnv nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT3, TyInt)] in
            (TyInt, nextuvar3, List.concat [newconstr; constr2; constr3])
        )
)
let collectTyEqs (tyEnvironment:tyenv) (expression:expr) = collectTyEqs_rec tyEnvironment uvargen expression
(**********************************************************)


(***** Unify *****)
exception UnifyFailed of string

(* Funções auxiliares *)
(* Substitui X por T no tipo S*)
let substitutionInType (tyX: string) (tyT: tipo) (tyS: tipo) : tipo =
  let rec subs tyS = match tyS with
    | TyList(tyS1) -> TyList(subs tyS1)
    | TyFn(tyS1, tyS2) -> TyFn(subs tyS1, subs tyS2)
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyId(s) -> (if s=tyX then tyT else TyId(s)) (* se for X, troca por T*)
  in subs tyS

(* Chama a substituição de tyX por tyT para cada equação do conjunto*)
let sustitutionInTyEquation (tyX: string) (tyT: tipo) (tyEquations: tyeqs) : tyeqs =
  List.map (fun (tyS1,tyS2) -> (substitutionInType tyX tyT tyS1, substitutionInType tyX tyT tyS2)) tyEquations

(* Verifica se o tipo X ocorre em T*)
let occurCheck (tyX: string) (tyT: tipo) : bool =
  let rec occur tyT = match tyT with
    | TyList(tyT1) -> occur tyT1
    | TyFn(tyT1,tyT2) -> occur tyT1 || occur tyT2
    | TyInt -> false
    | TyBool -> false
    | TyId(s) -> (s=tyX) (* define se X ocorre ou não em T*)
  in occur tyT

(* Função de Unify *)
(* Recebe as equações de tipo em tyEquations e retorna as substituições de tipo*)
(* let tySubstitutions = unify tyEquations *)
let unify (tyEquations: tyeqs) : tyeqs =
  let rec unify_rec tyEquations = match tyEquations with
    | [] -> []
    | (TyInt,TyInt) :: tail -> unify_rec tail (* Caso 1 *)
    | (TyBool,TyBool) :: tail -> unify_rec tail (* Caso 2 *)
    | (TyId(tyX),tyT) :: tail -> (* Caso 4 *)
        if tyT = TyId(tyX) then unify_rec tail (* Caso 3 *)
        else if occurCheck tyX tyT then (* Se X ocorre em T, não é uma equação válida*)
          raise (UnifyFailed "occurCheck didn't pass: circular type")
        else (* Se não, faz a substituição de X por T no resto das equações e chama o Unify novamente. Ainda, adiciona na lista de substituições (X,T)*)
          List.append (unify_rec (sustitutionInTyEquation tyX tyT tail)) [(TyId(tyX),tyT)]
    | (tyT,TyId(tyX)) :: tail -> (* Caso 5 *)
        if tyT = TyId(tyX) then unify_rec tail (* Caso 3 *)
        else if occurCheck tyX tyT then (* Se X ocorre em T, não é uma equação válida*)
          raise (UnifyFailed "occurCheck didn't pass: circular type")
        else (* Se não, faz a substituição de X por T no resto das equações e chama o Unify novamente. Ainda, adiciona na lista de substituições (X,T)*)
          List.append (unify_rec (sustitutionInTyEquation tyX tyT tail)) [(TyId(tyX),tyT)]
    | (TyFn(tyT1,tyT2),TyFn(tyT3,tyT4)) :: tail -> unify_rec ((tyT1,tyT3) :: (tyT2,tyT4) :: tail) (* Caso 6 *)
    | (TyList(tyT1),TyList(tyT2)) :: tail -> unify_rec ((tyT1,tyT2) :: tail) (* Caso 7 *)
    | (tyS,tyT)::tail -> raise (UnifyFailed "Not possible to solve type equations")
  in unify_rec tyEquations


(*** ApplySubs ***)
(* Aplica as substituições obtidas no Unify no tipo obtido pelo collectTyEqs *)
(* List.fold_left f a [b1; ...; bn] is f (... (f (f a b1) b2) ...) bn *)
let applySubs (tySubstitutions: tyeqs) (tyT: tipo) : tipo =
  List.fold_left (fun tyS (TyId(tyX),tyC2) -> substitutionInType tyX tyC2 tyS) tyT (List.rev tySubstitutions)


(*** TypeInfer ***)
let typeInfer (tyEnvironment: tyenv) (expression: expr) : tipo =
  let tyT, nextuvar, tyEquations = collectTyEqs tyEnvironment expression in
    let  tySubstitutions = unify tyEquations in
      applySubs tySubstitutions tyT

(* Segue um exemplo de como o programa L1 abaixo pode ser representado internamente *)

(* let rec fat: int -> int = (fn x: int => if (x == 0) then 1 else x * (fat (x - 1)))
   in fat (5)
   end
*)

(* Testes que devem retornar um tipo *)
let e1 = (Lrec("fat", TyInt, TyInt, "x", TyInt,
    If(Bop(Eq, Var("x"), Num(0)),
    Num(1),
    Bop(Mult, Var("x"), App(Var("fat"), Bop(Diff, Var("x"), Num(1))))),
    App(Var("fat"), Num(5))))

let e2 = Cons(Bop(Sum,Num(5),Num(2)),(Cons(Num(1),Nil)))

let e3 = If(IsEmpty(Nil),Bool(true),Bool(false))

let e4 = If(IsEmpty((Cons (Num(5), Nil))),Bool(true),Bool(false))

let e5 = Cons(Num(5), (Cons (Num(5), Nil)))

let e6 = Let("myVar", TyInt, Num(5), Bop(Sum,Var("myVar"), Num(5)))

let e7 = Bop(Sum,Num(5),Num(10))

let e8 = (LrecI("fat", "x",
    If(Bop(Eq, Var("x"), Num(0)),
    Num(1),
    Bop(Mult, Var("x"), App(Var("fat"), Bop(Diff, Var("x"), Num(1))))),
    App(Var("fat"), Num(5))))

let e9 = LetI("myVar", Num(5), Bop(Sum,Var("myVar"), Num(5)))

let e10 = Lam("myVar", TyInt, If(Bop(Eq, Var("myVar"), Num(5)), Num(5), Num(5)))

let e11 = LamI("myVar", If(Bop(Eq, Var("myVar"), Num(5)), Num(5), Num(5)))

let e12 = Hd(Cons(Num(5), (Cons (Num(5), Nil))))

let e13 = Tl(Cons(Num(5), (Cons (Num(5), Nil))))

let e14 = TryWith(Raise, Bop(Sum,Num(5),Num(10)))

let e15 = TryWith(Bop(Sum,Num(7),Num(10)), Bop(Sum,Num(5),Num(10)))

let e16 = Raise

let e17 = Cons(Bop(Sum, Num(7), Raise), Nil)

(* Testes que NÂO devem retornar um tipo *)
let ne1 = Bop(Sum,Num(5),Bool(true))

let ne2 = Bop(Sum, Num(5), Nil)

let ne3 = (Lrec("fat", TyBool, TyInt, "x", TyInt,
    If(Bop(Eq, Var("x"), Num(0)),
    Num(1),
    Bop(Mult, Var("x"), App(Var("fat"), Bop(Diff, Var("x"), Num(1))))),
    App(Var("fat"), Num(5))))

let ne4 = Cons(Bop(Sum,Num(5),Num(2)),(Cons(Bool(true),Nil)))

let ne5 = If(IsEmpty(Nil),Num(5),Bool(false))

let ne6 = If(IsEmpty((Cons (Num(5), Nil))),Bool(true),Num(5))

let ne7 = Cons(Bool(true), (Cons (Num(5), Nil)))

let ne8 = Let("myVar", TyBool, Num(5), Bop(Sum,Var("myVar"), Num(5)))

let ne9 = (LrecI("fat", "x",
    If(Bop(Eq, Var("x"), Num(0)),
    Num(1),
    Bop(Mult, Var("x"), App(Var("fat"), Bop(Diff, Var("x"), Num(1))))),
    App(Var("fat"), Bool(true))))

let ne10 = LetI("myVar", Num(5), Bop(Sum,Var("myVar"), Bool(true)))

let ne11 = Lam("myVar", TyBool, If(Bop(Eq, Var("myVar"), Num(5)), Num(5), Num(5)))

let ne12 = LamI("myVar", If(Bop(Eq, Var("myVar"), Bool(true)), Num(5), Num(5)))

let ne13 = Hd(Cons(Bool(true), (Cons (Num(5), Nil))))

let ne14 = Tl(Cons(Num(5), (Cons (Bool(true), Nil))))

let ne15 = TryWith(Bool(true), Bop(Sum,Num(5),Num(10)))


let allEs = [e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15;e16;e17];;

let rec runAll e = match e with
  | (hd::tl) ->
    (match hd with
      | head -> let (teste, nextuvar, constr) = collectTyEqs [] hd in
        print_endline "=== NEXT TEST ===";
        listToString constr;
        print_endline "==";
        print_endline (tipoToString teste);
        print_endline "==";
        (let tySubstitutions = unify constr in listToString tySubstitutions;
        (let tip = applySubs tySubstitutions teste in
        print_endline "==";
        print_endline (tipoToString tip);
        runAll tl)))
| [] -> ();;

let rec runAllTests e = match e with
  | (hd::tl) ->
    (match hd with
      | head ->
        let tyT = typeInfer [] hd in
        print_endline "=== NEXT TEST ===";
        print_endline (tipoToString tyT);
        runAllTests tl)
  | [] -> ();;

let testing = runAllTests allEs
