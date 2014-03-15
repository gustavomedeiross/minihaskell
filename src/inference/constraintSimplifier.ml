open InferenceExceptions
open InferenceTypes 
open MultiEquation
open Name

type typing_context = (cname * variable) list

(** [Unsat (k, t)] is raised if a canonical constraint C ≡ false. *)
exception Unsat of cname * tname

(** [OverlappingInstances] is raised if two rules of kind (E) overlap. *)
exception SOverlappingInstances

(** [MultipleClassDefinitions] is raised if two rules of kind (I)
    share the same goal. *)
exception SMultipleClassDefinitions

(** [UnboundClass k] is raised if the type class [k] occurs in a
    constraint while it is undefined. *)
exception SUnboundClass of cname

(** [equivalences] contains a map for the (E) rules.
    [(k, t), [l_1 ; ... ; l_n]] is a binding in [equivalences] iff
    there is an instance of class [k] for the type [(b_1, ..., b_n) t]
    in the typing context which consists of [(k_i_j b_i)], for all [j] and [i],
    where [[k_i_1 ; ... k_i_m] = l_i] *)
let equivalences : (cname * tname, cname list list) Hashtbl.t =
  Hashtbl.create 222

(** [implications] contains the (E') rules.
    [(k, [k_1 ; ... ; k_n])] is a binding in [implications] iff
    [k_i] are superclasses of [k]. *)
let implications : (cname, cname list) Hashtbl.t = Hashtbl.create 111

let existing_class k =
  if not (Hashtbl.mem implications k)
  then raise (SUnboundClass k)

(** [equivalent [b1 ; ... ; bN] k tc [(k_1,t_1) ; ... ; (k_N,t_N)]] registers
    a rule of the form (E). Where [tc] is the type constructor in
    [t = (b1, ..., bN) tc] *)
let equivalent ts k t ps =
  if Hashtbl.mem equivalences (k, t) then raise SOverlappingInstances;
  let rec factor ps = function
    | [] -> assert (ps = []); []
    | b :: bs -> Types.(
        let p1, p2 = List.partition (fun (ClassPredicate (_, b')) -> b = b') ps
        in
        List.map (fun (ClassPredicate (k,_)) -> k) p1 :: factor p2 bs)
  in
  Hashtbl.add equivalences (k, t) (factor ps ts)

(** [add_implication k [k_1;...;k_N]] registers a rule of the form (E'). *)
let add_implication k l =
  (* Ensures that the superclass order is acyclic *)
  if Hashtbl.mem implications k then raise SMultipleClassDefinitions;
  List.iter existing_class l;
  Hashtbl.add implications k l

(** [contains k k'] iff k => k', in other words: k' is a superclass of k *)
let rec contains =
  (** If [((k, k'), b)] is a binding then [b] <=> [contains k k']
   * (i.e. k' is a superclass of k) *)
  let superclass : (cname * cname, bool) Hashtbl.t = Hashtbl.create 333 in
  fun k k' ->
    try
      Hashtbl.find superclass (k, k')
    with Not_found ->
      let b =
        List.exists
          (fun k -> k = k' || contains k k')
          (Hashtbl.find implications k) in
      Hashtbl.add superclass (k, k') b;
      b

(** [entails pos C1 C2] checks that the canonical constraint [C1] implies
    the canonical constraint [C2].
    Exceptions:
      - InferenceExceptions.IrreduciblePredicate if that's not the case
      - SUnboundClass *)
let entails pos c1 c2 =
  List.iter
    (fun (k', v') ->
       if not (List.exists
                 (fun (k, v) ->
                    try
                      UnionFind.equivalent v v' && (k = k' || contains k k')
                    with Not_found -> raise (SUnboundClass k))
                 c1)
       then raise (IrreduciblePredicate (pos, c1, k', v')))
    c2

(* Canonicalize try to apply rules, to transform the constraint on one type to
 * a constraint on variables. To apply a (E) rule is equivalent to delete
 * exactly one type constructor i.e k_1 t_1 , ... k_n t_n => k (C t) give
 * for example :e k(C sometype) become k_1 sometype , .... k_n sometype.
 *  And we recursively try to destruct sometype, to expand k_i. *)

(** [simplify pos c] where [c = [(k_1,t_1);...;(k_N,t_N)]] decomposes
    [c] into an equivalent constraint [c' = [(k'_1,v_1);...;(k'_M,v_M)]] made
    only of variables.
    It raises [Unsat] if the given constraint is equivalent to [false].
    (i.e. when no instance of a class exists for some type constructor) *)
(* We explicitly deconstruct types, hence we don't use a [pool] argument *)
let simplify pos k =
  let rec simplify' k x =
    let rec aux x acc =
      match variable_structure x with
      | Some (App (a, b)) -> aux a (b :: acc)
      | Some (Var a)      -> aux a acc
      | None              ->
        match variable_kind x with
        | Constant ->
          let tycon = match variable_name x with
            | Some n -> n
            | None -> assert false in
          let equi =
            try
              Hashtbl.find equivalences (k, tycon)
            with Not_found -> raise (Unsat (k, tycon)) in
          let simple =
            List.map2
              (fun ks y ->
                 List.(flatten (map (fun k -> simplify' k y) ks)))
              equi
              acc
          in
          List.(flatten simple)
        | Flexible
        | Rigid -> assert (acc = []); [k, x]
    in aux x []
  in
  List.(flatten (map (fun (k, x) -> simplify' k x) k))

