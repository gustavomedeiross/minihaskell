val f : int ref
val fresh : unit -> int
val reset : unit -> unit
val fresh_iname : Name.tname -> Name.name
val mk_kname : Name.tname * Name.tname -> Name.lname
val mk_cname : Name.tname -> Name.tname
