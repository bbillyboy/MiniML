exception NotImplemented
exception ParserFailure

(** MiniCAML Language Definition *)
(* Types in MiniCAML *)
type typ =
  | Int                (* int *)
  | Bool               (* bool *)
  | Pair of typ * typ  (* t1 * t2 *)
  | Arrow of typ * typ (* t1 -> t2 *)
  | TVar of typ option ref

(* Used for identifiers of variables *)
type ident = string

(* The binary operations available in MiniCAML *)
type bop =
  | Equals   (* e1 = e2 *)
  | LessThan (* e1 < e2 *)
  | Plus     (* e1 + e2 *)
  | Minus    (* e1 - e2 *)
  | Times    (* e1 * e2 *)

(* The unary operations available in MiniCAML *)
type uop =
  | Negate   (* - e *)

(* Expressions in MiniCAML *)
type exp =
  | ConstI of int                         (* ... | -2 | -1 | 0 | 1 | 2 | ... *)
  | PrimBop of exp * bop * exp            (* e1 <op> e2 *)
  | PrimUop of uop * exp                  (* <op> e *)

  | ConstB of bool                        (* true | false *)
  | If of exp * exp * exp                 (* if e then e1 else e2 *)

  | Comma of exp * exp                    (* e1, e2 *)
  | LetComma of ident * ident * exp * exp (* let (x, y) = e1 in e2 end *)

  | Fn of ident * typ option * exp        (* fn x : t => e or fn x => e *)
  | Apply of exp * exp                    (* e1 e2 *)

  | Rec of ident * typ option * exp       (* rec f : t => e or rec f => e *)

  | Let of ident * exp * exp              (* let x = e1 in e2 end *)
  | Var of ident                          (* x *)

(* Charater Stream *)
module CStream : sig
  type t

  val of_string : string -> t
  val is_done : t -> bool
  val uncons : t -> (char * t) option
  val take : int -> t -> (string * t) option
  val take_while : (char -> bool) -> t -> string * t
end = struct
  type t = { input : string; len : int; index : int }

  let of_string s = { input = s; len = String.length s; index = 0 }

  let is_done cs = cs.len = cs.index

  let uncons cs =
    if is_done cs
    then None
    else Some (cs.input.[cs.index], { cs with index = cs.index + 1 })

  let take l cs =
    let index = cs.index + l in
    if index <= cs.len
    then Some (String.sub cs.input cs.index l, { cs with index })
    else None

  let take_while p cs =
    let rec find_index i =
      if i >= cs.len || not (p cs.input.[i])
      then i
      else find_index (i + 1)
    in
    let index = find_index cs.index in
    (String.sub cs.input cs.index (index - cs.index), { cs with index })
end

(* Parser Primitives/Utilities *)
module Parser : sig
  type input
  type 'a output
  type 'a t = input -> 'a output
  exception InvalidKeyword

  val run : 'a t -> string -> 'a option

  val of_value : 'a -> 'a t
  (** read this as "and then" *)
  val ( |*> ) : 'a t -> ('a -> 'b t) -> 'b t
  (** read this as "before" *)
  val ( |>> ) : 'a t -> 'b t -> 'b t
  val fail : 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val map3 : ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
  val const_map : 'b -> 'a t -> 'b t
  val first_of_2 : 'a t -> 'a t -> 'a t
  val first_of : 'a t list -> 'a t
  val many : 'a t -> 'a list t
  val some : 'a t -> 'a list t
  val sep_by : 'a t -> 'b t -> 'a list t
  val sep_by_1 : 'a t -> 'b t -> 'a list t
  val optional : 'a t -> 'a option t
  val skip : 'a t -> unit t
  val no : 'a t -> unit t
  val between : unit t -> unit t -> 'a t -> 'a t

  val satisfy : (char -> bool) -> char t
  val satisfy_many : (char -> bool) -> string t
  val accept_char : char -> char t
  val accept_string : string -> string t

  val eof : unit t
  val spaces : unit t
  val lexeme : 'a t -> 'a t
  val symbol : string -> unit t
  val keyword_among : string list -> string -> unit t
  (** [identifier_except] takes a list of keywords and fails if the current identifier is one of the keywords *)
  val identifier_except : string list -> string t
  (** [digits] only allows "0" or a number character sequence not starting with 0s *)
  val digits : string t
  val int_digits : int t

  val prefix_op : 'a t -> 'b t -> ('a -> 'b -> 'b) -> 'b t
  val right_assoc_op : 'a t -> 'b t -> ('b -> 'a -> 'b -> 'b) -> 'b t
  val left_assoc_op : 'a t -> 'b t -> ('b -> 'a -> 'b -> 'b) -> 'b t
  val non_assoc_op : 'a t -> 'b t -> ('b -> 'a -> 'b -> 'b) -> 'b t
end = struct
  let is_digit = function '0' .. '9' -> true | _ -> false
  let is_nonzero_digit = function '1' .. '9' -> true | _ -> false
  let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
  let is_alphanum c = is_alpha c || is_digit c
  let is_whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

  type input = CStream.t
  type 'a output = 'a option * CStream.t
  type 'a t = input -> 'a output
  exception InvalidKeyword

  let run p inp = CStream.of_string inp |> p |> fst

  let of_value x = fun is -> (Some x, is)

  let ( |*> ) p f = fun is0 ->
    match p is0 with
    | Some a, is1 -> f a is1
    | None, is1 -> (None, is1)

  let ( |>> ) p q = p |*> fun _ -> q

  let fail = fun is -> (None, is)

  let map f p = p |*> fun a -> of_value (f a)

  let map2 f p q = p |*> fun a -> map (f a) q

  let map3 f p q r = p |*> fun a -> map2 (f a) q r

  let const_map c p = map (fun _ -> c) p

  let first_of_2 p q = fun is ->
    match p is with
    | None, _ -> q is
    | result -> result

  let rec first_of ps =
    match ps with
    | [] -> fail
    | p :: ps -> first_of_2 p (first_of ps)

  let rec many p = first_of_2 (some p) (of_value [])
  and some p = p |*> fun x -> map (fun xs -> x :: xs) (many p)

  let sep_by_1 p sep = map2 (fun x xs -> x :: xs) p (many (sep |>> p))
  let sep_by p sep = first_of_2 (sep_by_1 p sep) (of_value [])

  let optional p = first_of_2 (map (fun a -> Some a) p) (of_value None)

  let skip p = map (fun _ -> ()) p

  let no p = fun is ->
    match p is with
    | Some a, _ -> (None, is)
    | None, _ -> (Some (), is)

  let between p1 p2 q = p1 |>> q |*> fun a -> const_map a p2

  let satisfy p = fun is0 ->
    match CStream.uncons is0 with
    | None -> (None, is0)
    | Some (c, is1) ->
       if p c
       then (Some c, is1)
       else (None, is0)

  let satisfy_many p =
    fun is ->
    let str, rest = CStream.take_while p is in
    (Some str, rest)

  let accept_char c = satisfy (fun c' -> c = c')

  let accept_string s =
    let len = String.length s in
    fun is0 ->
    match CStream.take len is0 with
    | None -> (None, is0)
    | Some (s', is1) ->
       if s = s'
       then (Some s, is1)
       else (None, is0)

  let eof = fun is ->
    if CStream.is_done is
    then (Some (), is)
    else (None, is)

  let spaces = skip (satisfy_many is_whitespace)

  (** [lexeme p] runs [p] and
      consumes all whitespaces after [p] if it succeeds.
      Otherwise, it backtracks. *)
  let lexeme p = first_of_2 p fail |*> fun a -> const_map a spaces

  let symbol s = lexeme (skip (accept_string s))

  let keyword_among keywords s =
    if List.mem s keywords
    then lexeme (accept_string s |>> no (satisfy is_alphanum))
    else raise InvalidKeyword

  let identifier_except keywords =
    lexeme
      (map2
         (fun c cs -> String.make 1 c ^ cs)
         (satisfy is_alpha)
         (satisfy_many is_alphanum)
       |*> fun s ->
           if List.mem s keywords
           then fail
           else of_value s)

  let digits =
    lexeme
      (first_of_2
         (const_map "0" (accept_char '0' |>> no (satisfy is_digit)))
         (map2
            (fun c cs -> String.make 1 c ^ cs)
            (satisfy is_nonzero_digit)
            (satisfy_many is_digit)))

  let int_digits = map (fun s -> int_of_string s) digits

  let prefix_op operatorp operandp con =
    map2
      (function
       | Some op -> con op
       | None -> fun a -> a)
      (optional operatorp)
      operandp

  let right_assoc_op operatorp operandp con =
    map2
      (fun a0 opbs -> List.fold_right (fun (op, b) f a -> con a op (f b)) opbs (fun a -> a) a0)
      operandp
      (many (map2 (fun op b -> (op, b)) operatorp operandp))

  let left_assoc_op operatorp operandp con =
    map2
      (List.fold_left (fun a (op, b) -> con a op b))
      operandp
      (many (map2 (fun op b -> (op, b)) operatorp operandp))

  let non_assoc_op operatorp operandp con =
    map2
      (fun a ->
        function
        | Some (op, b) -> con a op b
        | None -> a)
      operandp
      (optional (map2 (fun op b -> (op, b)) operatorp operandp))
end

(** Part1 : Parsing *)
let rec typ_parser =
  let open Parser in
  let keyword =
    let keywords = ["int"; "bool"] in
    keyword_among keywords
  in
  fun i ->
  let atom_typ_parser =
    first_of
      [ const_map Int (keyword "int");
        const_map Bool (keyword "bool");
        between (symbol "(") (symbol ")") typ_parser
      ]
  in
  let pair_typ_parser =
    non_assoc_op (symbol "*") atom_typ_parser (fun t1 () t2 -> Pair (t1, t2))
  in
  let typ_parser_impl = 
    right_assoc_op (symbol "->") pair_typ_parser (fun t1 () t2 -> Arrow (t1, t2))
  in
  typ_parser_impl i

(** Part2 : Type Inference *)
exception IgnoredInPart2
exception TypeInferenceError

module Context : sig
  type t

  (** Empty context *)
  val empty : t
  (** Looks up the variable in the context and return an optional type *)
  val lookup : t -> ident -> typ option
  (** Adds a new variable of type to the context *)
  val extend : t -> ident * typ -> t
  val of_list : (ident * typ) list -> t
end = struct
  module IdentMap = Map.Make(String)

  type t = typ IdentMap.t

  let empty = IdentMap.empty
  let lookup ctx x = IdentMap.find_opt x ctx
  let extend ctx (x, tau) = IdentMap.add x tau ctx
  let of_list = List.fold_left extend empty
end

(** Gives a pair of the input type pair and return type of a binary operator *)
let bop_type : bop -> (typ * typ) * typ =
  function
  | Equals -> ((Int, Int), Bool)
  | LessThan -> ((Int, Int), Bool)
  | Plus -> ((Int, Int), Int)
  | Minus -> ((Int, Int), Int)
  | Times -> ((Int, Int), Int)

(** Gives a pair of the input and return type of a unary operator *)
let uop_type : uop -> typ * typ =
  function
  | Negate -> (Int, Int)

(** Part3 : Substitution & Evaluation *)
exception EvaluationStuck

module IdentSet : sig
  type t

  val empty : t
  val mem : ident -> t -> bool
  val add : ident -> t -> t
  val singleton : ident -> t
  val remove : ident -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val exists : (ident -> bool) -> t -> bool
  val cardinal : t -> int
  val elements : t -> ident list
  val of_list : ident list -> t
end = struct
  include Set.Make(String)
end

(** Free identifier generator

    Note that generated identifiers are not valid external syntax,
    i.e. the parser should not accept them.
    These identifiers are only to make substitution on open expression works.
 *)
let (fresh_ident, reset_ctr) =
  let counter = ref 0 in
  ((fun x ->
    counter := !counter+1;
    string_of_int (!counter) ^ x),
   fun () ->
   counter := 0)

(** Part4 : Unification & Advanced Type Inference *)
exception UnificationFailure
exception OccursCheckFailure

let new_tvar () : typ option ref = ref None

let is_same_tvar (x : typ option ref) (y : typ option ref) : bool = x == y

let rec_follow_tvar : typ -> typ =
  let rec helper ys t =
    match t with
    | TVar x ->
       if List.exists (is_same_tvar x) ys
       then raise OccursCheckFailure
       else
         begin
           match !x with
           | None -> t
           | Some t' ->
              let t'' = helper (x :: ys) t' in
              let _ = x := Some t'' in
              t''
         end
    | _ -> t
  in
  helper []

(** Helper Functions *)
let string_of_cond_paren c s = if c then "(" ^ s ^ ")" else s

let string_of_typ, reset_print_typ =
  let counter = ref 0 in
  let fresh_tvar_string () = incr counter; "@a" ^ string_of_int !counter in
  let tvar_assoc = ref [] in
  let rec helper prec t =
    match t with
    | Int -> "int"
    | Bool -> "bool"
    | Pair (t1, t2) ->
       helper 2 t1 ^ " * " ^ helper 2 t2
       |> string_of_cond_paren (prec > 1)
    | Arrow (t1, t2) ->
       helper 1 t1 ^ " -> " ^ helper 0 t2
       |> string_of_cond_paren (prec > 0)
    | TVar x ->
       match !x with
       | None ->
          begin
            match List.assq_opt x !tvar_assoc with
            | None ->
               let a = fresh_tvar_string () in
               tvar_assoc := (x, a) :: !tvar_assoc;
               a
            | Some a -> a
          end
       | Some t -> helper prec t
  in
  helper 0, (fun () -> counter := 0; tvar_assoc := [])

let print_typ t = print_string (string_of_typ t)

let string_of_bop =
  function
  | Equals -> "="
  | LessThan -> "<"
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"

let string_of_uop =
  function
  | Negate -> "-"

let string_of_exp =
  let prec_of_bop =
    function
    | Equals -> (1, 2, 2)
    | LessThan -> (1, 2, 2)
    | Plus -> (2, 2, 3)
    | Minus -> (2, 2, 3)
    | Times -> (3, 3, 4)
  in
  let prec_of_uop =
    function
    | Negate -> (4, 5)
  in
  let rec helper prec =
    function
    | ConstI i -> string_of_int i
    | PrimBop (e1, bop, e2) ->
       let (parenp, p1, p2) = prec_of_bop bop in
       helper p1 e1 ^ " " ^ string_of_bop bop ^ " " ^ helper p2 e2
       |> string_of_cond_paren (prec > parenp)
    | PrimUop (uop, e') ->
       let (parenp, p') = prec_of_uop uop in
       string_of_uop uop ^ " " ^ helper p' e'
       |> string_of_cond_paren (prec > parenp)

    | ConstB b -> string_of_bool b
    | If (e, e1, e2) ->
       "if " ^ helper 0 e ^ " then " ^ helper 0 e1 ^ " else " ^ helper 0 e2
       |> string_of_cond_paren (prec > 0)

    | Comma (e1, e2) ->
       helper 1 e1 ^ ", " ^ helper 1 e2
       |> string_of_cond_paren (prec > 0)
    | LetComma (x, y, e1, e2) ->
       "let (" ^ x ^ ", " ^ y ^ ") = " ^ helper 0 e1 ^ " in " ^ helper 0 e2 ^ " end"
       |> string_of_cond_paren (prec > 5)

    | Fn (x, Some t, e) ->
       "fn " ^ x ^ " : " ^ string_of_typ t ^ " => " ^ helper 0 e
       |> string_of_cond_paren (prec > 0)
    | Fn (x, None, e) ->
       "fn " ^ x ^ " => " ^ helper 0 e
       |> string_of_cond_paren (prec > 0)
    | Apply (e1, e2) ->
       helper 6 e1 ^ " " ^ helper 7 e2
       |> string_of_cond_paren (prec > 6)

    | Rec (f, Some t, e) ->
       "rec " ^ f ^ " : " ^ string_of_typ t ^ " => " ^ helper 0 e
       |> string_of_cond_paren (prec > 0)
    | Rec (f, None, e) ->
       "rec " ^ f ^ " => " ^ helper 0 e
       |> string_of_cond_paren (prec > 0)

    | Let (x, e1, e2) ->
       "let " ^ x ^ " = " ^ helper 0 e1 ^ " in " ^ helper 0 e2 ^ " end"
       |> string_of_cond_paren (prec > 5)
    | Var x -> x
  in
  helper 0
let print_exp e = print_string (string_of_exp e)

(** Some Example Programs in MiniCAML *)
(* Programs Working Wihtout Advanced Type Inference *)
let ex1_string = "fn t : int * int => let (x, y) = t in x * x + (y * y) end"
let ex1 = Fn ("t", Some (Pair (Int, Int)), LetComma ("x", "y", Var "t", 
                                                     PrimBop (PrimBop (Var "x", Times, Var "x"),
                                                              Plus, 
                                                              PrimBop (Var "y", Times, Var "y"))))

let ex2_string = "fn x : int => true"
let ex2 = Fn ("x", Some Int, ConstB true)

let ex3_string = "let f = fn t : int * int => let (x, y) = t in x * x + (y * y) end in f (3, 4) end"
let ex3 =
  Let ("f", ex1, 
       Apply (Var "f", Comma (ConstI 3, ConstI 4)))

let ex4_string = "let g = (fn x : int => true) in g 0 end"
let ex4 =
  Let ("g", ex2,
       Apply (Var "g", ConstI 0))

let ex5_string = "let f = fn t : int * int => let (x, y) = t in x * x + (y * y) end in f 3 end"
let ex5 =
  Let ("f", ex1,
       Apply (Var "f", ConstI 3))

let ex6_string = "let f = (fn x : int => (fn y : int => x * x + (y * y))) in (f 3) 4 end"
let ex6 =
  Let ("f",
       Fn ("x",
           Some Int,
           Fn ("y",
               Some Int,
               PrimBop (PrimBop (Var "x", Times, Var "x"),
                        Plus,
                        PrimBop (Var "y", Times, Var "y")))),
       Apply (Apply (Var "f", ConstI 3),
              ConstI 4))

let ex7_string = "let fib = let helper = rec h : int * int -> int -> int => fn ab : int * int => let (a, b) = ab in fn steps : int => if steps < 1 then a else h (b, a + b) (steps - 1) end in helper (0, 1) end in fib 9 end"
let ex7 =
  Let ("fib",
       Let ("helper",
            Rec ("h",
                 Some (Arrow (Pair (Int, Int), Arrow (Int, Int))),
                 Fn ("ab",
                     Some (Pair (Int, Int)),
                     LetComma ("a", "b",
                               Var "ab",
                               Fn ("steps",
                                   Some Int,
                                   If (PrimBop (Var "steps", LessThan, ConstI 1),
                                       Var "a",
                                       Apply (Apply (Var "h",
                                                     Comma (Var "b", PrimBop (Var "a", Plus, Var "b"))),
                                              PrimBop (Var "steps", Minus, ConstI 1))))))),
            Apply (Var "helper", Comma (ConstI 0, ConstI 1))),
       Apply (Var "fib", ConstI 9))

(* Programs Working Only With Advanced Type Inference *)
let adv_ex1_string = "fn t => let (x, y) = t in x * x + (y * y) end"
let adv_ex1 = Fn ("t", None, LetComma ("x", "y", Var "t", 
                                       PrimBop (PrimBop (Var "x", Times, Var "x"),
                                                Plus, 
                                                PrimBop (Var "y", Times, Var "y"))))

let adv_ex2_string = "fn x => true"
let adv_ex2 = Fn ("x", None, ConstB true)

let adv_ex3_string = "let f = fn t => let (x, y) = t in x * x + (y * y) end in f (3, 4) end"
let adv_ex3 =
  Let ("f", ex1, 
       Apply (Var "f", Comma (ConstI 3, ConstI 4)))

let adv_ex4_string = "let g = (fn x => true) in g 0 end"
let adv_ex4 =
  Let ("g", ex2,
       Apply (Var "g", ConstI 0))

let adv_ex5_string = "let f = fn t => let (x, y) = t in x * x + (y * y) end in f 3 end"
let adv_ex5 =
  Let ("f", ex1,
       Apply (Var "f", ConstI 3))

let adv_ex6_string = "let f = (fn x => (fn y => x * x + (y * y))) in (f 3) 4 end"
let adv_ex6 =
  Let ("f",
       Fn ("x",
           None,
           Fn ("y",
               None,
               PrimBop (PrimBop (Var "x", Times, Var "x"),
                        Plus,
                        PrimBop (Var "y", Times, Var "y")))),
       Apply (Apply (Var "f", ConstI 3),
              ConstI 4))

(* Ill-typed Programs *)

(* Note: this expression is syntactically valid, but ill-typed! *)
let ill_ex1_string = "let f = (fn x : int => (fn y : bool => x * x + (y * y))) in f (3, 4) end"
let ill_ex1 =
  Let ("f",
       Fn ("x",
           Some Int,
           Fn ("y",
               Some Bool,
               PrimBop (PrimBop (Var "x", Times, Var "x"),
                        Plus,
                        PrimBop (Var "y", Times, Var "y")))),
       (Apply (Var "f", Comma (ConstI 3, ConstI 4))))

