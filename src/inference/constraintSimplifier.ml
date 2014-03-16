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

let equivalent_to k t =
  try
    Hashtbl.find equivalences (k, t)
  with Not_found -> raise (Unsat (k, t))

let implication_of k = Hashtbl.find implications k

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
          (implication_of k) in
      Hashtbl.add superclass (k, k') b;
      b

(** [entails pos C1 C2] returns [None] if the canonical constraint [C1] implies
    the canonical constraint [C2], or a sub-constraint of [C2] which isn't
    implied by [C1].
    Exception: SUnboundClass *)
let entails c1 c2 =
  try
    Some (List.find
            (fun (k', v') ->
               not (List.exists
                      (fun (k, v) ->
                         are_equivalent v v' && (k = k' || contains k k'))
                      c1))
            c2)
  with Not_found -> None

  (* TODO: This comment... *)
(* Canonicalize try to apply rules, to transform the constraint on one type to
 * a constraint on variables. To apply a (E) rule is equivalent to delete
 * exactly one type constructor i.e k_1 t_1 , ... k_n t_n => k (C t) give
 * for example :e k(C sometype) become k_1 sometype , .... k_n sometype.
 *  And we recursively try to destruct sometype, to expand k_i. *)

(** [canonicalize pos c] where [c = [(k_1,t_1);...;(k_N,t_N)]] decomposes
    [c] into an equivalent canonical constraint
    [c' = [(k'_1,v_1);...;(k'_M,v_M)]] made only of variables.
    It raises [Unsat] if the given constraint is equivalent to [false].
    (i.e. when it requires an inexistent instance of a class
    for some type constructor) *)

(* We explicitly deconstruct types, hence we don't use a [pool] argument *)
let canonicalize pos k =
  let memo : (cname * variable) list ref = ref [] in
  let visit k v =
    memo := (k, v) :: !memo in
  let visited k v =
    List.exists (fun (k', v') -> k = k' && are_equivalent v v') !memo in

  let ps : typing_context ref = ref [] in
  let add k v =
    let filter =
      List.filter
        (fun (k', v') ->
           not (contains k k' && are_equivalent v v')) in
    if not (List.exists
              (fun (k', v') ->
                 (k = k' || contains k' k) && are_equivalent v v')
              !ps)
    then ps := (k, v) :: filter !ps in

  let rec canonicalize' k v =
    let rec aux v acc =
      match variable_structure v with
      | Some (App (a, b)) -> aux a (b :: acc)
      | Some (Var a)      -> aux a acc
      | None              ->
        match variable_kind v with
        | Constant ->
          let tycon = match variable_name v with
            | Some n -> n
            | None -> assert false in
          let equi = equivalent_to k tycon in
          List.iter2
            (fun ks y ->
               List.iter (fun k -> canonicalize' k y) ks)
            equi
            acc
        | Flexible
        | Rigid -> assert (acc = []); add k v
    in
    if not (visited k v)
    then begin
      visit k v;
      aux v []
    end
  in
  List.map (fun (k, v) -> canonicalize' k v) k;
  !ps

