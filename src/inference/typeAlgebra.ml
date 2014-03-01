(**************************************************************************)
(*  Adaptated from:                                                       *)
(*  Mini, a type inference engine based on constraint solving.            *)
(*  Copyright (C) 2006. François Pottier, Yann Régis-Gianas               *)
(*  and Didier Rémy.                                                      *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; version 2 of the License.               *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful, but   *)
(*  WITHOUT ANY WARRANTY; without even the implied warranty of            *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU     *)
(*  General Public License for more details.                              *)
(*                                                                        *)
(*  You should have received a copy of the GNU General Public License     *)
(*  along with this program; if not, write to the Free Software           *)
(*  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA         *)
(*  02110-1301 USA                                                        *)
(*                                                                        *)
(**************************************************************************)

open MultiEquation
open InferenceTypes
open Positions
open Name
open Types
open IAST

type symbol = int

type associativity =
  | AssocLeft
  | NonAssoc
  | AssocRight
  | EnclosedBy of string * string

type builtin_dataconstructor = dname * tname list * Types.t

let builtin_env =
  [|
    TName "->" , (true, AssocRight, 0,
                  KArrow (KStar, KArrow (KStar, KStar)),
                  []);

    TName "int" , (false, NonAssoc, 2, KStar, []);
    TName "char", (false, NonAssoc, 2, KStar, []);
    TName "unit", (false, NonAssoc, 3, KStar,
                   [ (DName "_Unit", [],
                      TyApp (undefined_position, TName "unit", []))])
  |]

let get_infix (i, _, _, _, _) =
  i

let get_assoc (_, a, _, _, _) =
  a

let get_priority (_, _, p, _, _) =
  p

let as_symbol name =
  Misc.just_try (fun () -> Misc.array_associ name builtin_env)

let init_builtin_env variable =
  Array.fold_left
    (fun acu (o, (_, _, _, arity, ds)) ->
       (o, (arity,
            TVariable (variable ?name:(Some o) ()),
            ds
           )
       ) :: acu)
    [] builtin_env

let infix op =
  try
    get_infix (snd builtin_env.(op))
  with Invalid_argument "index out of bounds" -> false

let priority op =
  try
    get_priority (snd builtin_env.(op))
  with Invalid_argument "index out of bounds" -> max_int

let associativity op =
  try
    get_assoc (snd builtin_env.(op))
  with Invalid_argument "index out of bounds" -> NonAssoc

type 'a environment = tname -> 'a arterm

let symbol tenv (i : tname) =
  tenv i

let type_of_primitive tenv = function
  | PIntegerConstant _ -> symbol tenv (TName "int")
  | PUnit -> symbol tenv (TName "unit")
  | PCharConstant _ -> symbol tenv (TName "char")

let mkunit tenv =
  symbol tenv (TName "unit")

let arrow tenv t u =
  let v = symbol tenv (TName "->") in
  TTerm (App (TTerm (App (v, t)), u))

let n_arrows tenv =
  List.fold_left (fun acu x -> arrow tenv acu x)

let result_type tenv =
  let a = symbol tenv (TName "->") in
  let rec result_type = function
    | TTerm (App (TTerm (App (v, t)), u)) when v = a -> result_type u
    | u -> u
  in
  result_type

let arg_types tenv =
  let a = symbol tenv (TName "->") in
  let rec arg_types = function
    | TTerm (App (TTerm (App (v, t)), u)) when v = a -> t :: arg_types u
    | x -> []
  in
  arg_types

let tycon_args t =
  let rec chop acu = function
    | TTerm (App (t, u)) -> chop (u :: acu) t
    | _ -> acu
  in
  chop [] t

let rec tycon_name = function
  | TTerm (App (u, _)) -> tycon_name u
  | TVariable v as t -> t
  | _ -> assert false
