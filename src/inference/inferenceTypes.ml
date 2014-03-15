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

open Misc
open Positions
open Name

(** This module implements the internal representation of terms. *)

type 'a term =
  | App of 'a * 'a
  | Var of 'a

(** Terms whose parameters are either leaves of type ['a], or terms.
    [arterm] stands for ``abstract recursive term''. *)
type 'a arterm =
  | TVariable of 'a
  | TTerm of 'a arterm * 'a arterm


let rec iter f = function
  | App (l, r) ->
    f l; f r
  | Var v ->
    f v

let rec map f = function
  | App (l, r) ->
    App (f l, f r)
  | Var v ->
    Var (f v)

let rec fold f term accu =
  match term with
  | App (l, r) ->
    f r (f l accu)
  | Var v ->
    f v accu

let rec fold2 f term term' accu =
  match term, term' with
  | App (l, r), App (l', r') ->
    f r r' (f l l' accu)
  | Var v, Var v' ->
    f v v' accu
  | _ -> failwith "fold2"

let app t args =
  List.fold_left (fun acu x -> TTerm (acu, x)) t args

exception InvalidSymbolString of string

exception InvalidSymbolUse of string * int

let rec change_arterm f =
  function
  | TTerm (u, v) -> TTerm (change_arterm f u, change_arterm f v)
  | TVariable x -> f x

let var_from_assoc c = fun x ->
  TVariable (
    try
      List.assq x c
    with Not_found -> x
  )

let from_assoc c = fun x ->
  try
    List.assq x c
  with Not_found -> TVariable x

let change_arterm_vars c =
  change_arterm (var_from_assoc c)

let gen_change_arterm_vars c = change_arterm (from_assoc c)

