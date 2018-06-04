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
  | Raise -> "raise"
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

let rec listToString (lista: (tipo * tipo) list) =  match lista with
    | (head::tail) ->
        (match head with
          | t1, t2 -> print_endline ("(" ^ (tipoToString t1) ^ " --- " ^ (tipoToString t2) ^ ")"))
        ;
        listToString tail;
    | [] -> ();;


(* Only god knows *)
let rec _recon (ctx:env) nextuvar (t:expr) = match t with
  | App(t1,t2) ->
    let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
    let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar1 t2 in
    let NextUVar(tyX,nextuvar') = nextuvar2() in
    let newconstr = [(tyT1,TyFn(tyT2,TyId(tyX)))] in
    ((TyId(tyX)), nextuvar',
    List.concat [newconstr; constr1; constr2])
  | Num(t) -> (TyInt, nextuvar, [])
  | Bool(t) -> (TyBool, nextuvar, [])
  | If(t1,t2,t3) ->
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar1 t2 in
      let (tyT3,nextuvar3,constr3) = _recon ctx nextuvar2 t3 in
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
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
        ((TyId(tyX)), nextuvar',
        List.concat [newconstr; constr1])
  | TryWith(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar1 t2 in
      let newconstr = [(tyT1,tyT2)] in
      (tyT2, nextuvar2,
      List.concat [newconstr; constr1; constr2])
  | Hd(t1) ->
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr1])
  | Tl(t1) ->
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
      let NextUVar(tyX,nextuvar') = nextuvar1() in
      let newconstr = [(tyT1,TyList(TyId(tyX)))] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr1])
  | Cons(t1,t2) ->
      let (tyT1,nextuvar1,constr1) = _recon ctx nextuvar t1 in
      let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar1 t2 in
      let newconstr = [(TyList tyT1,tyT2)] in
      (tyT2, nextuvar2,
      List.concat [newconstr; constr1; constr2])
  | Let(var1,t2,expr1,expr2) ->
      let (tyT3,nextuvar3,constr3) = _recon ctx nextuvar expr1 in
      let newtipo = _eval ctx expr1 in
      let newctx = [(var1,newtipo)] in
      let (tyT4,nextuvar4,constr4) = _recon (List.concat [newctx;ctx]) nextuvar3 expr2 in
      let newconstr = [(t2, tyT3)] in
      (tyT4, nextuvar4,
      List.concat [newconstr; constr3; constr4])
  | Lrec(var1,t1,t2,var2,t3,expr1,expr2) ->
      let firstctx = [(var1, Vrclos(var1,var2,expr1, ctx))] in
      let secondctx = [(var2, Vclos(var2,expr1, (List.concat [firstctx;ctx])))] in
      let (tyT6,nextuvar6,constr6) = _recon (List.concat [secondctx;firstctx;ctx]) nextuvar expr1 in
      let (tyT7,nextuvar7,constr7) = _recon (List.concat [firstctx;ctx]) nextuvar6 expr2 in
      let newconstr = [(t3, tyT6)] in
      (tyT7, nextuvar7,
      List.concat [newconstr; constr6; constr7])
  | LetI(var1,expr1,expr2) ->
      let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar expr1 in
      let newtipo = _eval ctx expr1 in
      let newctx = [(var1,newtipo)] in
      let (tyT3,nextuvar3,constr3) = _recon (List.concat [newctx;ctx]) nextuvar2 expr2 in
      let NextUVar(tyX,nextuvar') = nextuvar3() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr2; constr3])
  | LrecI(var1,var2,expr1,expr2) ->
      let firstctx = [(var1, Vrclos(var1,var2,expr1, ctx))] in
      let secondctx = [(var2, Vclos(var2,expr1, (List.concat [firstctx;ctx])))] in
      let (tyT3,nextuvar3,constr3) = _recon (List.concat [secondctx;firstctx;ctx]) nextuvar expr1 in
      let (tyT4,nextuvar4,constr4) = _recon (List.concat [firstctx;ctx]) nextuvar3 expr2 in
      let NextUVar(tyX,nextuvar') = nextuvar4() in
      let newconstr = [(TyId(tyX), tyT3)] in
      ((TyId(tyX)), nextuvar',
      List.concat [newconstr; constr3; constr4])
  | Lam(v1,t1,e1) ->
      let newvalue = _eval ctx e1 in
      let newctx = [(v1,newvalue)] in
      let (tyT1,nextuvar1,constr1) = _recon (List.concat [newctx;ctx]) nextuvar e1 in
      (tyT1, nextuvar1,
      List.concat [constr1])
  | LamI(v1,e1) ->
      let newvalue = _eval ctx e1 in
      let newctx = [(v1,newvalue)] in
      let (tyT1,nextuvar1,constr1) = _recon (List.concat [newctx;ctx]) nextuvar e1 in
      (tyT1, nextuvar1,
      List.concat [constr1])
  | Var(e1) ->
    (try (let term = (snd (List.find (fun (variable, _) -> String.compare variable e1 == 0) ctx)) in
    (match term with
     | (t1) -> (valueToTipo t1 , nextuvar, []))) (* NÃO TENHO IDEIA DE QUAL É A REGRA PARA VAR *)
   with _ -> (TyId("Nao achou no contexto"), nextuvar, []))
  | Bop(t1,t2,t3) -> (
      (match t1 with
        | Sum ->
            let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = _recon ctx nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT3, TyInt)] in
            (tyT3, nextuvar3,
            List.concat [newconstr; constr2; constr3])
        | _  ->
            let (tyT2,nextuvar2,constr2) = _recon ctx nextuvar t2 in
            let (tyT3,nextuvar3,constr3) = _recon ctx nextuvar2 t3 in
            let newconstr = [(tyT2, TyInt);(tyT2, TyInt)] in
            (tyT3, nextuvar3,
            List.concat [newconstr; constr2; constr3]))
        )

let recon ctx e = _recon ctx uvargen e
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

let e3 = If(IsEmpty(Nil),Bool(true),Bool(false))

let e4 = Cons(Num(5), (Cons (Num(5), Nil)))

let e5 = Let("myVar", TyInt, Num(5), Bop(Sum,Var("myVar"), Num(5)))

let e6 = Bop(Sum,Num(5),Bool(true))

let e7 = Bop(Sum,Num(5),Num(10))

let e8 = Bop(Sum, Num(5), Nil)

let allEs = [e1;e2;e3;e4;e5;e6;e7;e8];;


let rec runAll e = match e with
  | (hd::tl) ->
    (match hd with
      | head -> let (teste, nextuvar, constr) = recon [] hd in
        print_endline "=== NEXT TEST ===";
        listToString constr;
        runAll tl)
  | [] -> ();;

(*let teste = eval(e2);;
let teste1 = print_endline(exprToString e1);;
let (teste2, nextuvar, constr) = recon [] e5;;
let teste3 = (listToString constr);;*)
let testing = runAll allEs;;
