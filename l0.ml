(* Gramatica : t ::= true | false | if ( t1 , t2 , t3 ) | 0 | succ ( t ) | pred ( t ) | iszero ( t ) *)
type term =
    TmTrue
    | TmFalse
    | TmIf of term * term * term
    | TmZero
    | TmSucc of term
    | TmPred of term
    | TmIsZero of term

type types = 
    TyNat
    | TyBool

(* Excecao a ser ativada quando termo for uma FORMA NORMAL *)
exception NoRuleApplies

(* Funcao auxiliar para determinar se um termo e um VALOR NUMERICO *)
let rec isnumericval t = match t with
    TmZero -> true
    | TmSucc ( t1 ) -> isnumericval t1
    | _ -> false

(* Implementacao da funcao STEP de avaliacao em um passo *)
let rec step t = match t with

    (* CASO IF ( t1 , t2 , t3 ) *)
    TmIf ( TmTrue , t2 , t3 ) -> (* regra E−IfTrue *)
        t2
    | TmIf ( TmFalse , t2 , t3 ) -> (* regra E−False *)
        t3
    | TmIf ( t1 , t2 , t3 ) -> (* regra E−If *)
        let t1' = step t1 in
        TmIf ( t1', t2 , t3 )

    (* CASO SUCC ( t1 ) *)
    | TmSucc ( t1 ) -> (* regra E−Succ *)
        let t1' = step t1 in
        TmSucc ( t1')

    (* CASO PRED ( t1 ) *)
    | TmPred ( TmZero ) -> (* regra E−PredZero *)
        TmZero
    | TmPred ( TmSucc ( nv1 )) when ( isnumericval nv1 ) -> (* regra E−PredSucc *)
        nv1
    | TmPred ( t1 ) -> (* regra E−Pred *)
        let t1' = step t1 in
        TmPred ( t1')

    (* CASO ISZERO ( t1 ) *)
    | TmIsZero ( TmZero ) -> (* regra E−IsZeroZero *)
        TmTrue
    | TmIsZero ( TmSucc ( nv1 )) when ( isnumericval nv1 ) -> (* regra E−IsZeroSucc *)
        TmFalse
    | TmIsZero ( t1 ) -> (* regra E−IsZero *)
        let t1' = step t1 in
        TmIsZero(t1')

    (* CASO Nenhuma regra se aplique ao termo *)
    | _ ->
        raise NoRuleApplies

    (* Implementacao de EVAL *)
    let rec eval t =
        try let t' = step t
            in eval t'
        with NoRuleApplies -> t

    let rec typeInfer t = match t with
        TmZero -> TyNat
        | TmTrue -> TyBool
        | TmFalse -> TyBool
        | TmIsZero( t1 ) when typeInfer( t1 ) == TyNat ->
            TyBool
        | TmSucc( t1 ) when typeInfer( t1 ) == TyNat ->
            TyNat
        | TmPred( t1 ) when typeInfer( t1 ) == TyNat ->
            TyNat
        | TmIf( t1, t2, t3 ) when typeInfer( t1 ) == TyBool && typeInfer( t2 ) == typeInfer( t3 ) ->
            typeInfer( t2 )
        | _ ->
            raise NoRuleApplies

    (* ASTs para teste *)
    let t1 = TmIsZero ( TmZero )
    let t2 = TmZero
    let t3 = TmSucc ( TmZero )
    let tif = TmIf ( t1 , t2 , t3 )
    let t4 = TmIsZero ( TmSucc ( TmZero ))
    let t5 = TmIsZero ( TmFalse )


