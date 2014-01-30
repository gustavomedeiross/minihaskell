open Positions
open Name
open XAST
open Types
open ElaborationExceptions

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
  name_methods : lname list;
  let_bounds   : name list;
}

let empty = { values = []; types = []; classes = []; labels = [];
name_methods = []; let_bounds = []}

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let rec bind_scheme pos x ts ty env =
  let env = add_name x pos env in 
  { env with values = (ts, (x, ty)) :: env.values}

and add_name (Name s) pos env =
  if List.mem (LName s) env.name_methods then
  raise(OverloadedSymbolCannotBeBound (pos,Name s))
  else  {env with let_bounds = (Name s) :: env.let_bounds}

let bind_simple pos x ty env =
  bind_scheme  pos x [] ty env

let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)

let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let rec is_superclass pos k1 k2 env =
  let scl = lookup_superclasses pos k1 env in
  List.exists (fun k -> k = k2 || is_superclass pos k k2 env) scl

(* Class definition constraints
 * Unchecked (?)
 * - The row must not contain free variables other than the class parameter
 * - Unique class definition *)

(* Independence constraint (for all i,j: not(Ki < Kj))
 * Also checks that the superclasses are already defined. *)
let unrelated pos env k1 k2 =
  if is_superclass pos k1 k2 env ||
     is_superclass pos k2 k1 env
  then raise (TheseTwoClassesMustNotBeInTheSameContext (pos, k1, k2))

let assert_independent pos sc env =
  ignore (List.fold_left
    (fun acc k -> List.iter (unrelated pos env k) acc;  k::acc) [] sc)

let rec assert_unique_members = function
  | [] -> ()
  | (pos, l, _) :: t ->
    if List.exists (fun (_, m, _) -> l = m) t
      then raise (InvalidOverloading pos)
      else assert_unique_members t

(* Not previously declared as an overloaded symbol *)
(*let assert_not_overloaded c env =
  List.iter
    (fun (pos, x, _) ->
      if not(
           List.for_all
             (fun c -> not (List.exists (fun (_, a, _) -> x = a)
                                         c.class_members))
             (List.map snd env.classes))
        then raise (InvalidOverloading pos))
    c.class_members
*)
let assert_not_overloaded c env =
  List.iter 
  	(fun (pos,s,_) ->if List.mem s env.name_methods
		       then raise(InvalidOverloading pos)
	) 
      c.class_members

let name_of_lname = function 
  | LName s -> Name s

(* Not previously declared as a value *)
(*let assert_not_bound c env =
  List.iter
    (fun (pos, x, _) ->
      let x = name_of_lname x in
      if List.exists (fun a -> x = fst (snd a)) env.values
        then raise (OverloadedSymbolCannotBeBound (pos, x)))
    c.class_members
*)

let assert_not_bound c env =
  List.iter
	(fun (pos, x, _) ->
	 let x = name_of_lname x in
	 if List.mem x env.let_bounds then raise
	 (OverloadedSymbolCannotBeBound (pos,x)))
	c.class_members 


let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    assert_independent c.class_position c.superclasses env;
    assert_unique_members c.class_members;
    assert_not_overloaded c env;
    assert_not_bound c env;
    { env with classes = (k, c) :: env.classes }

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]

