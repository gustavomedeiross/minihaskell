open InferenceTypes 
open MultiEquation
open Name


module Glob = Map.Make(struct type t = cname let compare = compare end )
module Globeq = Map.Make(struct type t = cname*variable let compare = compare end)

(** [environnement] contains a map from [tname] to [tname list]:
    the (E') rules *)
let environnement = ref Glob.empty

(** [environnement_equi] contains a map for the (E) rules*)

let environnement_equi = ref Globeq.empty

(** [Unsat] is raised if a canonical constraint C ≡ false. *)
exception Unsat
exception Poney


(** [OverlappingInstances] is raised if two rules of kind (E) overlap. *)
exception OverlappingInstances of tname * variable

(** [MultipleClassDefinitions k] is raised if two rules of kind (I)
    share the same goal. *)
exception MultipleClassDefinitions of tname

(** [UnboundClass k] is raised if the type class [k] occurs in a
    constraint while it is undefined. *)
exception UnboundClass of tname



(** Student! This is your job! You must implement the following functions: *)

(** [equivalent [b1;..;bN] k t [(k_1,t_1);...;(k_N,t_N)]] registers
    a rule of the form (E). *)
let equivalent l k t lc = 
  environnement_equi := Globeq.add (k,t) (l,lc) (!environnement_equi) 

(** [canonicalize pos pool c] where [c = [(k_1,t_1);...;(k_N,t_N)]]
    decomposes [c] into an equivalent constraint [c' =
    [(k'_1,v_1);...;(k'_M,v_M)]], introducing the variables
    [v_1;...;v_M] in [pool]. It raises [Unsat] if the given constraint
    is equivalent to [false]. *)
(*TODO raise Unsat *)

let unbuilt x = match x.structure with
  | None            -> raise Poney  
  | Some (App(a,b)) -> (a,b)  
  | Some (Var(a))   -> raise Poney

let canonicalize pos pool k =
  let rec nup final = function
    | [] -> final
    | t::q -> if List.mem t final 
      then nup final q 
      else nup (t::final) q in

  let refine_on_variables constr_on_var =   
    let rec refine_on_one_variable l =
      let l = nup [] l in (*Eliminate duplicates*)
      let rec delete_superclasses final = function
        | [] -> final
        | ((cl,var) :: q) as l -> if List.exists (fun (k,v)-> let super = try Glob.find
                                                                                k
                                                                                (!environnement) with
                                                   _->raise Poney in
                                                   List.mem cl super
                                                 ) l 
          then 
            delete_superclasses final q
          else
            delete_superclasses ((cl,var)::final) q
      in
      delete_superclasses [] l in 
    let rec refine_constraints = function
      | [] -> []   
      | ((k_1,v_1) :: q ) as l-> 
        let (class_on_this_variable,list_recursivecall) = 
          List.partition 
            (fun (k,v) -> v = v_1)  
            l        
        in  
        (refine_on_one_variable class_on_this_variable)
        @(refine_constraints list_recursivecall)
    in
    refine_constraints constr_on_var in

  let rec adapt_constraints l1 l2 = match l1,l2 with 
    | [],[] -> []
    | ((cn,types) :: q), t::r  -> (cn, t) :: (adapt_constraints q r)  
    | _,_ -> assert(false)
  in

  let expand k =
    let nb_appli = ref 0 in
    let l =  List.map 
        (fun (cn,x) ->
           try 
             let (cstruc,sometype) = unbuilt (UnionFind.find x) in
             (*TODO : Need to replace variable by sometype in a*)
             (*With sometype and UnionFind.fresh *) 
             let i_args =  assert(false) in
             (*Extract i-th type in n-uplet of sometype*)
             incr nb_appli;
             let (v,a) = Globeq.find (cn,cstruc) (!environnement_equi) 
             in
             adapt_constraints a i_args
           with Poney -> [(cn,x)]
              | Not_found -> raise(UnboundClass(TName("Pipo"))) (*TODO : good
                                                                  error*) 
        )
        k in (!nb_appli,l) in
  let rec expand_all k = match expand k with
    | (0,l)->List.flatten l
    | _,l -> expand_all (List.flatten l) in 
  let on_var = expand_all k in 
  let var = nup [] (List.flatten (List.map 
                                    (fun x-> fst(Globeq.find x
                                                   (!environnement_equi)))
                                    on_var))
  in 
  List.iter (fun x->register pool x) var; 
  refine_on_variables on_var




(** [add_implication k [k_1;...;k_N]] registers a rule of the form
    (E'). *)
let add_implication  k l = 
  environnement := Glob.add k l (!environnement) 

(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
let entails c1 c2 = 
  List.for_all (fun (name2,var2) -> let super = try Glob.find name2 (!environnement)
                 with _-> raise Poney               
                 in
                 List.exists (fun (nameincl1,var1) -> List.mem nameincl1 super) c1
               ) c2

(** [contains k1 k2] *)
let contains k1 k2 =
  let v = variable Rigid () in
  entails [(k2, v)] [(k1, v)]

