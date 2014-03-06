(** Name scopes. *)

(** Program identifiers. *)
type name =
  | Name of string (* Regular variable name *)
  | Name' of string
  | IName' of string * int (* (class name, id) -> "i_$CLASS_$ID" *)

(** Data constructor identifiers. *)
type dname = DName of string

(** Label identifiers. *)
type lname =
  | LName of string (* Regular field name *)
  | MName of string (* Method name *)
  | LName' of string
  | MName' of string
  | KName' of string * string * int (* Subdictionaries 
                                     * "s$ID_$SUPERCLASS_$CLASS" *)

(** Type identifiers. *)
type tname =
  | TName of string (* Regular type name (type/type variable) *)
  | TName' of string (* "t_$TYPE" *)
  | QName' of string (* Dictionary type -> "c_$CLASS" *)

type cname =
  | CName of string

val reset : unit -> unit
val fresh_iname : cname -> name
val fresh_kname : cname -> cname -> lname

val mk_cname : cname -> tname
val elab_tname : tname -> tname

val of_name  :  name -> string
val of_dname : dname -> string
val of_lname : lname -> string
val of_tname : tname -> string
val of_cname : cname -> string

