(** This module implements reasoning about canonical constraints of the form:

    K_1 T_1 /\ ... K_N T_N

    using rules of the form:

    - forall b_1 ... b_N, k t ≡ k_1 t_1 /\ ... k_N t_N   (E)
    - forall b, k b => k_1 b /\ ... k_N b                (E')
*)

open Positions
open Name
open MultiEquation

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

(** [equivalent [b1 ; ... ; bN] k t [(k_1,t_1) ; ... ; (k_N,t_N)]] registers
    a rule of the form (E). *)
val equivalent
  : tname list -> cname -> tname -> Types.class_predicate list -> unit

(** [add_implication k [k_1;...;k_N]] registers a rule of the form (E'). *)
val add_implication
  : cname -> cname list -> unit

      (*TODO: Description*)
(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
val entails
  : Positions.position -> (cname * variable) list -> (cname * variable) list
  -> unit

(** [contains k k'] iff k' is a superclass of k *)
val contains
  : cname -> cname -> bool

(** [simplify pos c] where [c = [(k_1,t_1);...;(k_N,t_N)]] decomposes
    [c] into an equivalent constraint [c' = [(k'_1,v_1);...;(k'_M,v_M)]] made
    only of variables.
    It raises [Unsat] if the given constraint is equivalent to [false].
    (i.e. when no instance of a class exists for some type constructor) *)
val simplify
  : position -> typing_context -> typing_context

