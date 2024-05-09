       (** Part 1: Parsing *)
let parse_exp_tests : (string * exp option) list = [
  ("", None);
  ("2 - 1", (Some (PrimBop (ConstI 2, Minus, ConstI 1))));
  ("-1", (Some (PrimUop (Negate, ConstI 1))));
  ("2 < 3",(Some (PrimBop (ConstI 2, LessThan, ConstI 3))));
  ("x y", (Some (Apply (Var "x", Var "y"))));
  
]

let rec exp_parser i =
  let open Parser in
  let identifier, keyword =
    let keywords = ["true"; "false"; "let"; "in"; "end"; "if"; "then"; "else"; "fn"; "rec"] in
    identifier_except keywords, keyword_among keywords
  in
  let atomic_exp_parser = 
    first_of
      [ 
        const_map (ConstB true) (keyword "true"); 
        const_map (ConstB false) (keyword "false"); 
        int_digits |*> (fun x -> (of_value (ConstI x))); 
        identifier |*> (fun x -> 
            (of_value (Var x)));
        between (symbol "(") (symbol ")") exp_parser
      ] 
  in 
  let applicative_exp_parser = 
    left_assoc_op (symbol "") atomic_exp_parser (fun t1 () t2 -> Apply (t1, t2))
  in 
  let negatable_exp_parser =
    first_of [
      (keyword "let") |>>
      symbol "(" |>>
      identifier |*> (fun iden1 -> 
          spaces |>>
          symbol "," |>>
          identifier |*> (fun iden2 ->
              spaces |>>
              symbol ")" |>>
              symbol "=" |>>
              exp_parser |*> (fun exp1 ->
                  spaces |>>
                  (keyword "in") |>>
                  exp_parser |*> (fun exp2 ->
                      spaces |>>
                      (keyword "end") |>>
                      of_value (LetComma (iden1,iden2,exp1,exp2))))));
      keyword "let" |>>
      spaces |>>
      identifier |*> (fun iden ->
          spaces |>>
          symbol "=" |>>
          spaces |>>
          exp_parser |*> (fun exp1 ->
              spaces |>>
              keyword "in" |>>
              spaces |>>
              exp_parser |*> (fun exp2 ->
                  spaces |>>
                  keyword "end" |>> 
                  of_value (Let (iden,exp1,exp2)))));
      keyword "if" |>>
      spaces |>>
      exp_parser |*> (fun exp1 ->
          spaces |>>
          keyword "then" |>>
          spaces |>>
          exp_parser |*> (fun exp2 ->
              spaces |>>
              keyword "else" |>>
              spaces |>>
              exp_parser |*> (fun exp3 ->
                  of_value (If (exp1,exp2,exp3)))));
      keyword "fn" |>> 
      identifier |*> (fun iden ->
          spaces |>>
          symbol ":" |>> 
          typ_parser |*> (fun typ -> 
              symbol "=>" |>>
              exp_parser |*> (fun exp ->
                  of_value (Fn (iden,Some typ,exp)))));
      keyword "fn" |>>
      identifier |*> (fun iden ->
          spaces |>>
          symbol "=>" |>>
          exp_parser |*> (fun exp ->
              of_value (Fn (iden,None,exp))));
      keyword "rec" |>>
      identifier |*> (fun iden ->
          spaces |>>
          symbol ":" |>>
          typ_parser |*> (fun typ ->
              symbol "=>" |>>
              exp_parser |*> (fun exp ->
                  of_value (Rec (iden,Some typ,exp))))); 
      keyword "rec" |>>
      identifier |*> (fun iden ->
          spaces |>>
          symbol "=>" |>>
          exp_parser |*> (fun exp ->
              of_value (Rec (iden,None,exp)))); 
      applicative_exp_parser
    ]
  in 
  let negation_exp_parser =
    first_of_2
      (symbol "-" |>>
       negatable_exp_parser |*> (fun x ->
           of_value (PrimUop (Negate,x))))
      (negatable_exp_parser)
  in 
  let multiplicative_exp_parser =
    left_assoc_op (symbol "*") negation_exp_parser (fun t1 () t2 -> PrimBop (t1,Times,t2))
  in 
  let additive_exp_parser =
    left_assoc_op (first_of_2 (symbol "+" |> const_map Plus) (symbol "-" |> const_map Minus)) 
      multiplicative_exp_parser 
      (fun t1 sep t2 -> PrimBop (t1,sep,t2)) 
  in
  let comparative_exp_parser =
    non_assoc_op (first_of_2 (symbol "=" |> const_map Equals) (symbol "<" |> const_map LessThan)) 
      additive_exp_parser 
      (fun t1 sep t2 -> PrimBop (t1,sep,t2))
  in
  let exp_parser_impl =
    non_assoc_op (symbol ",") comparative_exp_parser (fun t1 () t2 -> Comma (t1, t2))
  in
  exp_parser_impl i


let parse_exp : string -> exp option =
  let open Parser in
  run (between spaces eof exp_parser)

(** Part 2: Type Inference *)
let typ_infer_test_helper_tests : ((Context.t * exp) * typ option) list = [
  ((Context.empty, ConstB true), Some Bool);
  
]

let rec typ_infer (ctx : Context.t) (e : exp) : typ =
  match e with
  | ConstI _ -> Int
  | PrimBop (e1, bop, e2) ->
      let ((t1, t2), t3) = bop_type bop in
      if typ_infer ctx e1 = t1 && typ_infer ctx e2 = t2
      then t3
      else raise TypeInferenceError
  | PrimUop (uop, e') ->
      let (t1, t2) = uop_type uop in
      if typ_infer ctx e' = t1
      then t2
      else raise TypeInferenceError

  | ConstB _ -> Bool
  | If (e', e1, e2) -> let t = typ_infer ctx e1 in
      let t' = typ_infer ctx e2 in
      if typ_infer ctx e' = Bool && t = t' 
      then t
      else raise TypeInferenceError

  | Comma (e1, e2) -> Pair (typ_infer ctx e1, typ_infer ctx e2)
  | LetComma (x, y, e1, e2) -> (match typ_infer ctx e1 with
      |Pair (taux, tauy) ->
          let ctxx = Context.extend ctx (x, taux) in 
          let ctxy = Context.extend ctxx (y, tauy) in
          typ_infer ctxy e2
      | _ -> raise TypeInferenceError)
      

  | Fn (x, Some t, e') -> 
      (let tau1 = t in
       let ctx' = Context.extend ctx (x, tau1) in
       let tau2 = (typ_infer ctx' e') in
       Arrow (tau1, tau2))
  | Apply (e1, e2) -> (match typ_infer ctx e1 with
      |Arrow (input, output) -> let t = typ_infer ctx e2 in
          if t = input then output else raise TypeInferenceError
      | _ -> raise TypeInferenceError) 
             

  | Rec (f, Some t, e') -> let ctx' = Context.extend ctx (f, t) in
      if typ_infer ctx' e' = t then t
      else raise TypeInferenceError

  | Let (x, e1, e2) -> let tau1 = typ_infer ctx e1 in
      let ctx' = Context.extend ctx (x, tau1) in
      typ_infer ctx' e2
  | Var x ->
      begin
        match Context.lookup ctx x with
        | Some t -> t
        | None -> raise TypeInferenceError
      end


  | Fn (_, None, _) -> raise IgnoredInPart2
  | Rec (_, None, _) -> raise IgnoredInPart2


let typ_infer_test_helper ctx e =
  try
    Some (typ_infer ctx e)
  with
  | TypeInferenceError -> None

(** Part 3: Substitution & Evaluation *)
let free_vars_test_helper_tests : (exp * ident list) list = [
  (ConstI 5, []);
  (Var "x", ["x"])
]

let rec free_vars (e : exp) : IdentSet.t =
  match e with
  | ConstI _ -> IdentSet.empty
  | PrimBop (e1, _, e2) -> IdentSet.union (free_vars e1) (free_vars e2)
  | PrimUop (_, e') -> free_vars e'

  | ConstB _ -> IdentSet.empty
  | If (e', e1, e2) -> IdentSet.union (free_vars e') (IdentSet.union (free_vars e1) (free_vars e2))

  | Comma (e1, e2) -> IdentSet.union (free_vars e1) (free_vars e2)
  | LetComma (x, y, e1, e2) -> IdentSet.union (free_vars e1) (IdentSet.remove y (IdentSet.remove x (free_vars e2)))

  | Fn (x, tOpt, e') -> IdentSet.remove x (free_vars e')
  | Apply (e1, e2) -> IdentSet.union (free_vars e1) (free_vars e2)

  | Rec (f, tOpt, e') -> IdentSet.remove f (free_vars e')

  | Let (x, e1, e2) -> IdentSet.union (free_vars e1) (IdentSet.remove x (free_vars e2))
  | Var x -> IdentSet.singleton x


let free_vars_test_helper e = IdentSet.elements (free_vars e)

let subst_tests : (((exp * ident) * exp) * exp) list = [
  (((ConstI 5, "x"), PrimBop (ConstI 2, Plus, Var "x")), PrimBop (ConstI 2, Plus, ConstI 5))
]

let rec subst ((d, z) : exp * ident) (e : exp) : exp =
  (** [rename (x, e)] replace [x] appears in [e] with a fresh identifier
      and returns the fresh identifier and updated expression *)
  let rename ((x, e) : ident * exp) : ident * exp =
    let x' = fresh_ident x in
    (x', subst (Var x', x) e)
  in
  match e with
  | ConstI _ -> e
  | PrimBop (e1, bop, e2) -> PrimBop (subst (d, z) e1, bop, subst (d, z) e2)
  | PrimUop (uop, e') -> PrimUop (uop, subst (d, z) e')

  | ConstB _ -> e
  | If (e', e1, e2) -> If (subst (d,z) e', subst (d,z) e1, subst (d,z) e2)

  | Comma (e1, e2) -> Comma (subst (d, z) e1, subst (d, z) e2)
  | LetComma (x, y, e1, e2) -> if x = z || y = z then
        LetComma (x, y, subst (d, z) e1, e2) 
      else if IdentSet.mem x (free_vars d) then
        let (x', e1') = rename (x, e1) in
        if IdentSet.mem x (free_vars e2) then
          LetComma (x',y, e1', subst (d, z) (subst (Var x', x) e2))
        else LetComma (x', y, e1', subst (d, z) e2)
      else if IdentSet.mem y (free_vars d) then
        let (y', e1') = rename (y, e1) in
        if IdentSet.mem y (free_vars e2) then
          LetComma (x,y', e1', subst (d, z) (subst (Var y', y) e2))
        else LetComma (x, y', e1', subst (d, z) e2)
      else
        LetComma (x,y, subst (d, z) e1, subst (d, z) e2)

  | Fn (x, tOpt, e') -> if x = z then
        Fn (x, tOpt, e')
      else
        let (x', e') = rename (x, e') in
        Fn (x', tOpt, subst (d, z) e') 
          
  | Apply (e1, e2) -> Apply (subst (d,z) e1, subst (d,z) e2)

  | Rec (f, tOpt, e') -> if f = z then
        Rec (f, tOpt, e')
      else
        let (f', e') = rename (f, e') in
        Rec (f', tOpt, subst (d, z) e') 

  | Let (x, e1, e2) -> if x = z then
        Let (x, subst (d, z) e1, e2)
      else if IdentSet.mem x (free_vars d) then
        let (x', e1') = rename (x, e1) in
        if IdentSet.mem x (free_vars e2) then
          Let (x', e1', subst (d, z) (subst (Var x', x) e2))
        else Let (x', e1', subst (d, z) e2)
      else
        Let (x, subst (d, z) e1, subst (d, z) e2) 
      
  | Var x ->
      if x = z
      then d
      else e

let eval_test_helper_tests : (exp * exp option) list = [
  (Var "x", None);
  (ConstI 5, Some (ConstI 5));
  (PrimBop (ConstI 5, Minus, ConstI 5), Some (ConstI 0))
]

let rec eval (e : exp) : exp =
  match e with
  | ConstI _ -> e
  | PrimBop (e1, bop, e2) ->
      begin
        match eval e1, eval e2 with
        | ConstI n1, ConstI n2 ->
            begin
              match bop with
              | Equals -> ConstB (n1 = n2)
              | LessThan -> ConstB (n1 < n2)
              | Plus -> ConstI (n1 + n2)
              | Minus -> ConstI (n1 - n2)
              | Times -> ConstI (n1 * n2)
            end
        | _ -> raise EvaluationStuck
      end
  | PrimUop (_, e) ->
      begin
        match eval e with
        | ConstI n -> ConstI (- n)
        | _ -> raise EvaluationStuck
      end

  | ConstB _ -> e
  | If (e', e1, e2) -> begin match eval e' with
      |ConstB b -> if b then eval e1 else eval e2
      |_ -> raise EvaluationStuck
    end

  | Comma (e1, e2) -> Comma (eval e1, eval e2)
  | LetComma (x, y, e1, e2) -> begin match eval e1 with 
      |Comma (x', y') -> eval (subst (y',y) (subst (x', x) e2))
      |_ -> raise EvaluationStuck
    end

  | Fn (x, tOpt, e') -> Fn (x, tOpt, e')
  | Apply (e1, e2) -> begin match eval e1 with 
      |Fn (x, tOpt, e') -> let v2 = eval e2 in
          eval (subst (v2, x) e') 
      |_ -> raise EvaluationStuck
    end

  | Rec (f, tOpt, e') -> eval (subst (Rec (f, tOpt, e'), f) e')

  | Let (x, e1, e2) -> eval (subst (eval e1, x) e2)
  | Var _ -> raise EvaluationStuck


let eval_test_helper e =
  try
    Some (eval e)
  with
  | EvaluationStuck -> None

(** Part 4: Unification & Advanced Type Inference *)
let unify_test_case1 () =
  let x = new_tvar () in
  let y = new_tvar () in
  y := Some Int;
  (TVar x, TVar y)

let unify_test_case2 () =
  let x = new_tvar () in
  (TVar x, Arrow (TVar x, TVar x))

let unify_test_helper_tests : ((unit -> typ * typ) * bool) list = [
  ((fun () -> (Int, Int)), true);
  ((fun () -> (Int, Bool)), false);
  (unify_test_case1, true);
  (unify_test_case2, false)
]

let rec unify : typ -> typ -> unit =
  let rec occurs_check (x : typ option ref) (t : typ) : bool =
    let t = rec_follow_tvar t in
    match t with
    | Int -> false
    | Bool -> false
    | Pair (t1, t2) -> occurs_check x t1 || occurs_check x t2
    | Arrow (t1, t2) -> occurs_check x t1 || occurs_check x t2
    | TVar y -> is_same_tvar x y
  in
  fun ta tb ->
    let ta = rec_follow_tvar ta in
    let tb = rec_follow_tvar tb in
    match ta, tb with
    | Int, Int -> ()
    | Bool, Bool -> ()
    | Pair (ta1, ta2), Pair (tb1, tb2) -> unify ta1 tb1; unify ta2 tb2
    | Arrow (ta1, ta2), Arrow (tb1, tb2) -> unify ta1 tb1; unify ta2 tb2
    | TVar xa, TVar xb when is_same_tvar xa xb -> ()
    | TVar xa, _ -> 
        if occurs_check xa tb then raise OccursCheckFailure
        else xa := Some tb
    | _, TVar xb -> unify tb ta
    | _, _ -> raise UnificationFailure


let unify_test_helper f =
  let ta, tb = f () in
  try
    unify ta tb; true
  with
  | UnificationFailure -> false
  | OccursCheckFailure -> false

let adv_typ_infer_test_case1 =
  let x = new_tvar () in
  ((Context.empty, Fn ("y", None, Var "y")), Some (Arrow (TVar x, TVar x)))

let adv_typ_infer_test_helper_tests : ((Context.t * exp) * typ option) list = [
  adv_typ_infer_test_case1
]


let rec adv_typ_infer ctx e = match e with
  | ConstI _ -> Int
  | PrimBop (e1, bop, e2) ->
      let ((t1, t2), t3) = bop_type bop in
      unify (adv_typ_infer ctx e1) t1; unify (adv_typ_infer ctx e2) t2;
      t3
  
  | PrimUop (uop, e') -> 
      let (t1, t2) = uop_type uop in
      unify (adv_typ_infer ctx e') t1;
      t2
      
  | ConstB b -> Bool
  | If (e', e1, e2) -> 
      let t = adv_typ_infer ctx e1 in
      let t' = adv_typ_infer ctx e2 in
      unify (adv_typ_infer ctx e') Bool; unify t t'; 
      t 

  | Comma (e1, e2) -> Pair (adv_typ_infer ctx e1, adv_typ_infer ctx e2)
  | LetComma (x, y, e1, e2) -> 
      let x' = new_tvar () in
      let y' = new_tvar () in
      unify (adv_typ_infer ctx e1) (Pair (TVar x', TVar y')); 
      let ctxx = Context.extend ctx (x, TVar x') in 
      let ctxy = Context.extend ctxx (y, TVar y') in
      adv_typ_infer ctxy e2
        

  | Fn (x, Some t, e') -> 
      (let tau1 = t in
       let ctx' = Context.extend ctx (x, tau1) in
       let tau2 = (adv_typ_infer ctx' e') in
       Arrow (tau1, tau2))
      
  | Fn (x, None, e') -> 
      let tau1 = new_tvar () in 
      let ctx' = Context.extend ctx (x, TVar tau1) in
      let tau2 = (adv_typ_infer ctx' e') in
      (Arrow (TVar tau1, tau2))
      
                          
  | Apply (e1, e2) -> 
      let alpha = new_tvar () in
      let tau1 = adv_typ_infer ctx e1 in
      let tau2 = adv_typ_infer ctx e2 in 
      unify (tau1) (Arrow (tau2, TVar alpha ));
      TVar alpha
      

  | Rec (f, Some t, e') -> 
      (let ctx' = Context.extend ctx (f, t) in
       unify (adv_typ_infer ctx' e') t; t)
      
  | Rec (f, None, e') -> 
      (let tau1 = new_tvar () in 
       let ctx' = Context.extend ctx (f, TVar tau1) in
       let tau2 = (adv_typ_infer ctx' e') in
       unify (TVar tau1) tau2; tau2)

  | Let (x, e1, e2) -> let tau1 = adv_typ_infer ctx e1 in
      let ctx' = Context.extend ctx (x, tau1) in
      adv_typ_infer ctx' e2
  | Var x -> begin
      match Context.lookup ctx x with
      | Some t -> t
      | None -> raise TypeInferenceError
    end


let adv_typ_infer_test_helper ctx e =
  try
    Some (adv_typ_infer ctx e)
  with
  | UnificationFailure -> None
  | OccursCheckFailure -> None
  | TypeInferenceError -> None



(**
 **************************************
 No Modifying Anything After This Line
 **************************************

*)
let infer_main exp_str =
  match parse_exp exp_str with
  | None -> raise ParserFailure
  | Some e ->
      print_string "input expression       : "; print_exp e; print_newline ();
      let t = typ_infer Context.empty e in
      print_string "type of the expression : "; print_typ t; print_newline ();
      print_string "evaluation result      : "; print_exp (eval e); print_newline ()

let adv_infer_main exp_str =
  match parse_exp exp_str with
  | None -> raise ParserFailure
  | Some e ->
      print_string "input expression       : "; print_exp e; print_newline ();
      let t = adv_typ_infer Context.empty e in
      print_string "type of the expression : "; print_typ t; print_newline ();
      print_string "evaluation result      : "; print_exp (eval e); print_newline ()
