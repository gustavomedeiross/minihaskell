open Name

let f = ref 0

let fresh =
  (fun () -> incr f; !f)

let reset () = f := 0

let fresh_iname = function
  | TName s -> IName (s, fresh ())
  | CName _ -> assert false

let mk_kname = function
  | TName a, TName b -> KName (a, b)
  | _ -> assert false

let mk_cname = function
  | TName a -> CName a
  | _ -> assert false

