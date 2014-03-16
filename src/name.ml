(** Name scopes. *)

(* We chose a different organization for names. In the elaboration,
 * we create new identifiers and it is important to avoid conflicts with older
 * identifiers. Essentially, to avoid conflicts, we tag differently different
 * objects. This tag is used to prefix, during the printing, the names with
 * some distinguishing stuff. *)

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

let f = ref (-1)
let g = ref (-1)

let fresh =
  (fun () -> incr f; !f)

let reset () =
  f := 0;
  g := 0

let fresh_iname (CName s) =
  incr f;
  IName' (s, !f)

let fresh_kname (CName s) (CName k) =
  incr g;
  KName' (s, k, !g)

let builtin_type = ["->"; "int"; "char"; "unit"]

let is_builtin_type s = List.mem s builtin_type

(* Name elaboration *)
let elab_name = function
  | Name s -> Name' s
  | Name' _ | IName' _ as name -> name

let elab_dname = fun x -> x

let elab_lname = function
  | LName l -> LName' l
  | MName m -> MName' m
  | LName' _ | MName' _ | KName' _ as lname -> lname

let elab_tname = function
  | TName s as t when s.[0] = '\'' || is_builtin_type s -> t
  | TName s -> TName' s
  | t -> t

let mk_cname = function
  | CName a -> QName' a

let of_name = function
  | Name s        -> s
  | Name' s       -> "v_" ^ s
  | IName' (k, id) -> "i_" ^ string_of_int id ^ "_" ^ k

let of_dname = function
  | DName s -> s

let of_lname = function
  | LName l
  | MName l           -> l
  | LName' l          -> "l_" ^ l
  | MName' m          -> "m_" ^ m
  | KName' (k, k', i) -> ("k" ^ string_of_int i ^ "_" ^ k ^ k')

let of_tname = function
  | TName s -> s
  | TName' s -> "t_" ^ s
  | QName' s -> "c_" ^ s

let of_cname = function
  | CName s -> s
