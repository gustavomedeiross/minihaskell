(** Name scopes. *)

(* We chose a different organization for names. In the elaboration,
 * we create new identifiers and it is important to avoid conflicts with older
 * identifiers. Essentially, to avoid conflicts, we tag differently different
 * objects. This tag is used to prefix, during the printing, the names with
 * some distinguishing stuff. *)

(* Constructors prefixed with a single quote [_Name']
 * are called "elaborated constructors", and are those used
 * for the output program.
 * The prettyPrinter was modified accordingly, it doesn't rely directly on the
 * definitions of these types, but uses the of__name functions below to
 * carry out the conversion to strings. *)

(** Program identifiers. *)
type name =
  | Name of string (* Regular variable name *)
  | Name' of string
  | IName' of string * int (* (class name, id) -> "i_$CLASS_$ID" *)
  (* Identifiers of variables whose types are elaborated dictionaries *)

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

(* Class names. *)
(* We do not see a reason why the input AST wouldn't
 * distinguish between types and classes. *)
type cname =
  | CName of string

val reset : unit -> unit

(* Used in `src/elaborate/` *)
val fresh_iname : cname -> name
val fresh_kname : cname -> cname -> lname

val elab_name  :  name -> name
val elab_dname : dname -> dname (* Identity for now *)
val elab_lname : lname -> lname
val elab_tname : tname -> tname
val mk_cname : cname -> tname

(* Used in prettyPrint *)
val of_name  :  name -> string
val of_dname : dname -> string
val of_lname : lname -> string
val of_tname : tname -> string
val of_cname : cname -> string

