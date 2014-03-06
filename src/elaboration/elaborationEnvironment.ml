open Positions
open Name
open XAST
open Types
open ElaborationExceptions

module StringSet = Misc.StringSet

type t = {
  values        : (tnames * class_predicates * binding) list;
  types         : (tname * (Types.kind * type_definition)) list;
  classes       : (cname * class_definition) list;
  labels        : (lname * (tnames * Types.t * tname)) list;
  instances     : (tname * (instance_definition * name) list) list;
  subdicts      : ((cname * cname) * lname) list;
  method_names  : StringSet.t;
  names         : StringSet.t;
}

let empty =
  { values        = []              ;
    types         = []              ;
    classes       = []              ;
    labels        = []              ;
    instances     = []              ;
    subdicts      = []              ;
    method_names  = StringSet.empty ;
    names         = StringSet.empty }

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, _, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme pos x ts pred ty env =
  { env with values = (ts, pred, (x, ty)) :: env.values}

let bind_simple pos x ty env =
  bind_scheme pos x [] [] ty env

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

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let labels_of rtcon env =
  let p (_, (_, _, rtcon')) = rtcon = rtcon' in
  List.(fst (split (filter p env.labels)))

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found -> raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left
    (fun env (t, k) -> bind_type t k (primitive_type t k) env)
    empty
    PreludeTypes.types


(* Type classes *)

let lookup_class pos k env =
  try
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))


let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let rec is_superclass pos k1 k2 env =
  let scl = lookup_superclasses pos k1 env in
  List.exists (fun k -> k = k2 || is_superclass pos k k2 env) scl

(* Independence constraint (for all i,j: not (Ki < Kj))
 * Also checks that the superclasses are already defined. *)
let unrelated pos env k1 k2 =
  if is_superclass pos k1 k2 env ||
     is_superclass pos k2 k1 env
  then raise (TheseTwoClassesMustNotBeInTheSameContext (pos, k1, k2))

let check_independent pos sc env =
  ignore (List.fold_left
            (fun acc k -> List.iter (unrelated pos env k) acc; k :: acc) [] sc)

(* Parameter is the only free variable in types of class members *)
let rec check_free_variables name parameter (pos, _, t) =
  match parameter with
  | TName s ->
    let freeT = free t in
    if not (TS.mem parameter freeT) then
      raise (AmbiguousTypeclass (pos, name));
    begin
      try
        let tv = TS.choose (TS.remove parameter freeT) in
        raise (UnboundTypeVariable (pos, tv))
      with Not_found -> ()
    end
  | _ -> assert false

(** [add_methods p env member] registers [member] as a method of the class
 *  of name [k], where [p = ClassPredicate (k, _)],
 *  making [member] both visible like a variable (with constraint p)
 *  and excluding it from being let-bound *)
let add_methods (ClassPredicate (k, tv) as p) env (pos, m, ty) = match m with
  | MName s ->
    let name = Name s in
    if StringSet.mem s env.method_names then raise (MultipleMethods (pos, m));
    if StringSet.mem s env.names then raise (VariableIsAMethodName (pos, name));
    let m_binding = [tv], [p], (name, ty) in
    { env with method_names = StringSet.add s env.method_names;
               values       = m_binding :: env.values }
  | _ -> assert false

let bind_class k c env =
  let { class_position  = pos ;
        class_parameter = tv  ;
        superclasses    = sks ;
        class_name      = k   ;
        class_members   = ms  } = c in
  try
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    check_independent pos sks env;
    List.iter (check_free_variables k tv) ms;
    let env = List.fold_left (add_methods (ClassPredicate (k, tv))) env ms in
    { env with classes = (k, c) :: env.classes }

(* Instances *)

let bind_instance env (t, num) =
  try
    let listinstance = List.assoc t.instance_index env.instances in
    if List.exists
        (fun (x, _) -> x.instance_class_name = t.instance_class_name)
        listinstance
    then raise (OverlappingInstances (t.instance_position,
                                      t.instance_class_name));
    let instances = List.remove_assoc t.instance_index env.instances in
    { env with instances = (t.instance_index, (t,num) :: listinstance)
                           :: instances }
  with Not_found -> { env with instances = (t.instance_index, [t,num])
                                           :: env.instances}

let lookup_instances env c =
  try
    List.assoc c env.instances
  with Not_found -> []

let add_predicates ps env =
  { env with instances = ps @ env.instances }

let new_subdict_names assocs env =
  { env with subdicts = assocs @ env.subdicts }

(* Will not fail *)
let get_subdict_name env k1 k2 = List.assoc (k1, k2) env.subdicts

let add_name (pos, name) env = match name with
  | Name s ->
    if StringSet.mem s env.method_names
    then raise (VariableIsAMethodName (pos, name))
    else { env with names = StringSet.add s env.names }
  (* An AST output by the parser does not contain any *Name' constructor,
   *  but not failing extends the domain of the typechecker
   *  so that it is the identity on elaborated AST's *)
  | Name' _
  | IName' _ -> env

let as_method x env = match x with
  | Name s ->
    let m = MName s in
    if StringSet.mem s env.method_names
    then Some m
    else None
  | _ -> None

