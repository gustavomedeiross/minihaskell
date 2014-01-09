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
}

let empty = { values = []; types = []; classes = []; labels = [] }

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

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

let deuz (a,b,c)=b 

let preums (a,b,c)=a

let rec is_double e l n = 
  match l with
  | [] -> ()  
  | (a,b,c)::q ->  
    if e=b then
           (if n>=1 then raise(InvalidOverloading(a)) 
                    else is_double e q (n+1))
           else is_double e q n 

let string_of_lname = function 
  | LName s -> s

let string_of_name = function
  | Name s ->s

let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    List.iter (fun x-> is_double (deuz x) c.class_members 0) c.class_members;
    List.iter (fun x-> if not(
                         List.for_all 
                         (fun y -> not(List.exists (fun a->deuz x= deuz a)
                                                   y.class_members ) )
                         (List.map snd env.classes))
                       then raise(InvalidOverloading(preums x))
              )
               c.class_members; 
    List.iter (fun x->
                  if List.exists 
                    (fun a -> 
                     string_of_name (fst (snd a)) =string_of_lname (deuz x)
                    )
                    env.values  
                  then raise(InvalidOverloading(preums x) ))
              c.class_members ;                 
    { env with classes = (k, c) :: env.classes }



let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let is_superclass pos k1 k2 env =
  (* Student! This is your job! *)
  true

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

