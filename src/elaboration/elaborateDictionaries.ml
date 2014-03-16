open String
open Misc
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))

let rec program p = handle_error List.(fun () ->
    flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p)))

and block env = function
  | BTypeDefinitions ts ->
    let ts, env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let names = names_vb [] d in
    let env = List.fold_right add_name names env in
    let d, env = value_binding env d in
    ([BDefinition d], env)

  (* We transform class definition into type definition. Next, we call block
     recursively. *)

  | BClassDefinition c ->
    let env    = bind_class c.class_name c env in
    let env, single_record = elaborate_class c env in
    block env (BTypeDefinitions single_record)

  (* Instance elaboration cannot be simply reduced to elaboration of terms,
   * as opposed to class definitions. The reason is that contrary to a
   * regular record, methods may be elaborated in different contexts
   * depending on whether they are lambda abstractions or not. *)
  | BInstanceDefinitions is ->
    let env = List.fold_right add_name (names_is is) env in
    let dict, env = elaborate_instances env is in
    ([BDefinition dict], env)

(* Return an expression whose value is the dictionary of type (K ty).
 * Exception: NotAnInstance *)
and elaborate_dictionary pos env k ty =

  let rec elaborate_dictionary' env k' = function
    | TyVar (pos, v) ->
      let is = lookup_instances env v in
      try_d_proj env StringSet.empty k' v is
    | TyApp (pos, c, ts) ->
      let is = lookup_instances env c in
      let i, name =
        try
          List.find (fun (i, _) -> i.instance_class_name = k') is
        with Not_found -> raise (NotAnInstance (pos, k, ty, k', Left c)) in
      d_ovar_inst env i name ts

  (* Rule D-OVAR-INST *)
  and d_ovar_inst env i name ts =
    let t_inst = List.combine i.instance_parameters ts in
    (* Substitute predicates by instanciated types *)
    let predicates =
      List.map
        (fun (ClassPredicate (k, ty)) -> k, List.assoc ty t_inst)
        i.instance_typing_context in
    let f_dict = EVar (undefined_position, name, ts) in
    List.fold_left (dict_application env) f_dict predicates

  (* Apply a dictionary abstraction (f_dict : k 'a -> (...)) to (k ty) dictionary
   * [dict_application env f_dict (k, ty)] = 'f_dict (k ty)' *)
  and dict_application env f_dict (k, ty) =
    let dict = elaborate_dictionary' env k ty in
    EApp (undefined_position, f_dict, dict)

  (* Rule D-PROJ/D-VAR, seeking to obtain (k v) by sub-dictionary projections
   * (when v is a type variable) starting from one of the instances in the
   * list argument. The accumulator [visited] ensures every class is tried at
   * most once *)
  and try_d_proj env visited k' v = function
    | [] -> raise (NotAnInstance (pos, k, ty, k', Right v))
    | (i, name) :: is ->
      match
        d_proj
          env
          visited
          (EVar (undefined_position, name, []))
          k'
          i.instance_class_name
      with
      | _, Some q -> q
      | visited, None -> try_d_proj env visited k' v is

  (* Given a dictionary term q of type (_ k'), use projections to obtain
   * a dictionary of type (_ k) *)
  and d_proj env visited q k (CName s as k') =
    if k = k'
    then visited, Some q
    else if StringSet.mem s visited
    then visited, None (* This class has already been visited before *)
    else
      let visited = StringSet.add s visited in
      let ks = (lookup_class undefined_position k' env).superclasses in
      try_proj_superclass env visited q k k' ks

  (* Try projecting successively on every superclass of k' *)
  and try_proj_superclass env visited q k k' = function
    | [] -> visited, None
    | k'' :: ks ->
      match
        let kname = get_subdict_name env k'' k' in
        let q = ERecordAccess (undefined_position, q, kname) in
        d_proj env visited q k k''
      with
      | visited, None -> try_proj_superclass env visited q k k' ks
      | found -> found
  in
  elaborate_dictionary' env k ty

(* Instance elaboration
 *
 *   instance L 'a => K ('a cons) { ... }
 *
 * becomes
 *
 *   let (fresh_name_K : 'b _l -> 'a cons _k) =
 *     fun (fresh_name_L : 'b _l) -> { ... }
 * *)

and elaborate_instances env is =
  let is = (* Associate a fresh name to every instance *)
    List.map
      (fun ({ instance_class_name = k } as i) -> (i, fresh_iname k))
      is in
  let env' = List.fold_left bind_instance env is in (* Full context *)
  let defs, _ = List.fold_left (instance_definition env') ([], env) is in
  BindRecValue (undefined_position, defs), env'

(* env': full context, where all instances mutually recursive with the
 *       current instance are in scope
 *       (Gamma_h',h,h'' in [1,sujet.pdf])
 * env: "current" context, contains only instances declared earlier
 *      (Gamma_h' in [1])
 * def: list of all previously elaborated instances
 * i: current instance
 *    (h in [1])
 * *)
and instance_definition env' (defs, env) (i, name) =
  let { instance_position       = pos ;
        instance_parameters     = ts  ;
        instance_typing_context = ps  } = i in

  (* The constraints are elaborated into a lambda abstraction,
   * this creates one dictionary variable per constraint *)
  let ps', local_dict_variables = dict_variables pos env ps in
  (* i defines the instance (K itype) where K = c.class_name *)
  let c = lookup_class pos i.instance_class_name env in
  let cname = mk_cname i.instance_class_name in
  let itype = cons_type i.instance_index ts in
  let itype' = cons_type (elab_tname i.instance_index) ts in

  (* Add the local context *)
  let add_local_context env =
    let env = introduce_type_parameters env ts in
    add_predicates ps' env in
  let env'_ = add_local_context env' in
  let env_ = add_local_context env in

  (* Elaborate record definition *)
  (* Sub-dictionaries are elaborated in the "full" context,
   * contrary to original requirements:
   * an instance of the superclass should have been declared somewhere
   * so a direct sub-dictionary should be available *)
  let sub_dict = sub_dictionaries pos env'_ c itype in
  let methods = elaborate_methods env'_ env_ c i itype in
  let record = ERecordCon (pos, name, [itype'], sub_dict @ methods) in

  let env = bind_instance env (i, name) in
  let inst_body, inst_type =
    List.fold_right abstract local_dict_variables
      (record, TyApp (undefined_position, cname, [itype'])) in
  let inst_body = EForall (pos, ts, inst_body) in
  let def =
    ValueDef (pos, ts, [], (name, inst_type), inst_body) in
  def :: defs, env

(* Declare a new dictionary variable
 * [dict_variable {K 'a}] = (instance K 'a, fresh_name_K) *)
and dict_variables pos env ps =
  let qs = List.map dict_variable ps in
  collect_by_variable pos env [] qs,
  List.map (fun (_, name, ty) -> (name, ty)) qs

and collect_by_variable pos env map = function
  | [] -> map
  | ({ instance_class_name = k;
       instance_index      = v; } as i, name, _) :: qs ->
    let is = try List.assoc v map
      with Not_found -> [] in
    if List.exists
        (fun ({ instance_class_name = k' }, _) ->
           k = k' ||
           is_superclass pos k k' env ||
           is_superclass pos k' k env)
        is
    then raise (NotCanonicalConstraint pos);
    let map = map_add v (i, name) map in
    collect_by_variable pos env map qs

and map_add key v = function
  | [] -> [key, [v]]
  | (key', vs) :: map ->
    if key = key'
    then (key, v :: vs) :: map
    else (key', vs) :: map_add key v map

and dict_variable (ClassPredicate (k, v)) =
  let i =
    { instance_position = undefined_position ;
      instance_parameters     = []           ;
      instance_typing_context = []           ;
      instance_class_name     = k            ;
      instance_index          = v            ; (* here a variable *)
      instance_members        = []           } in
  let name = fresh_iname k in
  (i, name, cons_type (mk_cname k) [v])

(* Make a lambda abstraction
 * [abstract {x : t} {e : ty}] = (\(x : t) . e) : t -> ty *)
and abstract (x, t) (e, ty) =
  ELambda (undefined_position, (x, t), e),
  TyApp (undefined_position, TName "->", [t; ty])

and sub_dictionaries pos env c itype =
  let mk_record_binding k' =
    RecordBinding (
      get_subdict_name env k' c.class_name,
      elaborate_dictionary pos env k' itype) in
  List.map mk_record_binding c.superclasses

and elaborate_methods env' env c i ity =
  let { instance_position   = pos ;
        instance_class_name = k   ;
        instance_members    = ms  } = i in

  let elaborate_method (_, m, ty) =
    try
      let RecordBinding (_, e) =
        List.find (fun (RecordBinding (m', _)) -> m' = m) ms in
      let ty = substitute [c.class_parameter, ity] ty in
      let env = if is_abstraction e then env' else env in
      let e = eforall pos [] e in
      let e, ty' = expression env e in
      check_equal_types pos ty ty';
      let m' = elab_lname m in
      RecordBinding (m', e)
    with Not_found -> raise (LackingMethod (pos, k, m)) in

  (* Make sure all methods are present once exactly
   * and no inexistent method has been introduced *)
  if List.length c.class_members <> List.length ms
  then raise (TooManyMethods (pos, k));
  let members = List.map elaborate_method c.class_members in
  members

and is_abstraction = function
  | ELambda _ -> true
  | _ -> false

(* Type well-formedness is taken care of by type-checking the elaborated
 * dictionary type declaration. In particular, it will catch unbound type
 * variables (a type class definition only binds one variable) *)
and elaborate_class c env =
  let { class_name     = CName name as k ;
        superclasses   = scs             ;
        class_position = pos             } = c in
  let subdicts =
    List.map
      (fun sk ->
         ignore (lookup_class pos sk env);
         let kname = fresh_kname sk k in
         (pos,
          kname,
          TyApp (pos,
                 mk_cname sk,
                 [TyVar (pos, c.class_parameter)])))
      scs
  in
  let env =
    let assocs =
      List.map2 (fun sk (_, kname, _) -> ((sk, k), kname)) scs subdicts in
    new_subdict_names assocs env
  in
  (* member names (MName _) will be elaborated to (MName' _)
   * during elaboration of types *)
  env,
  TypeDefs
    (pos,
     [TypeDef
        (pos,
         KArrow (KStar, KStar),
         QName' name,
         DRecordType ([c.class_parameter],
                      c.class_members @ subdicts))])

and type_definitions env (TypeDefs (pos, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  let tdefs, env = List.fold_left type_definition ([], env) tdefs in
  TypeDefs (pos, tdefs), env

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition (tdefs, env) = function
  | TypeDef (pos, ts, t, dt) ->
    let t' = elab_tname t in
    let dt', env = datatype_definition t env dt in
    TypeDef (pos, ts, t', dt') :: tdefs, env
  | ExternalType (p, ts, t, os) ->
    ExternalType (p, ts, elab_tname t, os) :: tdefs, env

and datatype_definition t env = function
  | DAlgebraic ds ->
    let ds', env = List.fold_left algebraic_dataconstructor ([], env) ds in
    DAlgebraic (List.rev ds'), env

  | DRecordType (ts, ltys) ->
    let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
    let ltys', env = List.fold_left (label_type ts env' t) ([], env) ltys in
    DRecordType (ts, List.rev ltys'), env

and label_type ts env' rtcon (ltys, env) (pos, l, ty) =
  let l' = elab_lname l in
  let ty' = elab_wf_type env' KStar ty in
  (pos, l', ty') :: ltys, bind_label pos l ts ty rtcon env

and algebraic_dataconstructor (ds, env) (pos, (DName k as d), ts, kty) =
  let kty' = elab_wf_scheme env ts kty pos in
  let d' = elab_dname d in
  (pos, d', ts, kty') :: ds, bind_scheme pos (Name k) ts [] kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and elab_wf_scheme env ts ty pos =
  elab_wf_type (introduce_type_parameters env ts) KStar ty

(** [elab_wf_type env xkind ty] checks that [ty] is well-formed (in [env]) with
 * type [xkind], and converts all identifiers to their elaborated version *)
and elab_wf_type env xkind = function
  | TyVar (pos, t) as ty ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind;
    ty

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    let t' = elab_tname t in
    let tys' = check_type_constructor_application pos env kt tys in
    TyApp (pos, t', tys');

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> []

  | ty :: tys, KArrow (k, ks) ->
    let ty' = elab_wf_type env k ty in
    let tys' = check_type_constructor_application pos env ks tys in
    ty' :: tys'

  | _ -> raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
  | KStar, KStar -> ()

  | KArrow (k1, k2), KArrow (k1', k2') ->
    check_equivalent_kind pos k1 k1';
    check_equivalent_kind pos k2 k2'

  | _ -> raise (IncompatibleKinds (pos, k1, k2))

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2)
  then raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  let tys' = List.map (elab_wf_type env KStar) tys in
  let ts, ps, (_, ty) = lookup pos x env in
  try
    let assoc = List.combine ts tys in
    let elab (ClassPredicate (k, var)) =
      let t = List.assoc var assoc in
      elaborate_dictionary pos env k t in
    let qs = List.map elab ps in
    let ty = substitute assoc ty in
    tys', qs, ty
  with Invalid_argument _ -> raise (InvalidTypeApplication pos)

(** [expression env e] returns a pair [e', ty] of the result of elaboration
 * on [e] and the type of [e] (in [env]) *)
and expression env = function
  | EVar (pos, x, tys) -> eVar pos env x tys

  | ELambda (pos, (x, aty), e') ->
    let x' = elab_name x in
    let aty' = elab_wf_type env KStar aty in
    let env = bind_simple pos x aty env in
    let e, ty = expression env e' in
    (ELambda (pos, (x', aty'), e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env a in
    let b, b_ty = expression env b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  (*If we have constraints, value_binding behaves differently*)
  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, _, _) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables are useless. *)
    expression env e

  | EDCon (pos, (DName x as d), tys, es) ->
    let tys', qs, ty = type_application pos env (Name x) tys in
    assert (qs = []); (* Type constructors cannot have class predicates *)
    let itys, oty = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let d' = elab_dname d in
      let es =
        List.map2 (fun e xty ->
            let e, ty = expression env e in
            check_equal_types pos ty xty;
            e
          ) es itys
      in
      (EDCon (pos, d', tys', es), oty)

  | EMatch (pos, s, bs) ->
    let s, sty = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs, tys = List.split bstys in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
    let ts, lty, rtcon = lookup_label pos l env in
    let ty =
      match ty with
      | TyApp (_, r, args) ->
        if rtcon <> r then
          raise (LabelDoesNotBelong (pos, l, r, rtcon))
        else
          begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
          end
      | _ ->
        raise (RecordExpected (pos, ty))
    in
    let l' = elab_lname l in
    (ERecordAccess (pos, e, l'), ty)

  | ERecordCon (pos, n, i, rbs) -> eRecordCon env pos n i rbs

  | EPrimitive (pos, p) as e ->
    (e, primitive pos p)

and eVar pos env x tys =
 (*Elaboration of identifiers, different cases depending on
  if the symbol is a method, or a name of function ...*)

 let tys', qs, ty = type_application pos env x tys in
  (* If an identifier is a method or overloaded we elaborate *)
  match as_method x env with
  | None -> (* x is not a method *)
    let x' = elab_name x in
    let e' =
      List.fold_left (fun a b -> EApp (pos, a, b)) (EVar (pos, x', tys')) qs
    in
    (e', ty)
  | Some m -> (* x is a method *)
    (* its lname was already elaborated by as_method *)
    match qs with
    | [q] ->
      (ERecordAccess (pos, q, m), ty)
    | _ -> assert false (* Methods have exactly one constraint*)

and eRecordCon env pos n i rbs =
  (** We syntactically forbid empty records. *)
  assert (rbs <> []);
  let i' = List.map (elab_wf_type env KStar) i in
  let rec check others rty = function
    | [] ->
      begin match rty with
        | Some (_, TyApp (_, rtcon, _)) ->
          let labels = labels_of rtcon env in
          if List.(length labels <> length others) then
            raise (InvalidRecordConstruction pos)
        | _ -> assert false (** Because we forbid empty record. *)
      end;
      List.rev others, rty
    | RecordBinding(l, _) as rb :: ls ->
      let RecordBinding (l', _) as rb', ty = record_binding env rb in

      if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
        raise (MultipleLabels (pos, l));

      let ts, lty, rtcon = lookup_label pos l env in
      let s, rty =
        match rty with
        | None ->
          let rty = TyApp (pos, rtcon, i') in
          let s =
            try
              List.combine ts i
            with Invalid_argument _ -> raise (InvalidRecordInstantiation pos)
          in
          (s, rty)
        | Some (s, rty) ->
          (s, rty)
      in
      check_equal_types pos ty (Types.substitute s lty);
      check (rb' :: others) (Some (s, rty)) ls
  in
  let ls, rty =
    match check [] None rbs with
    | _, None           -> assert false
    | ls, Some (_, rty) -> ls, rty
  in
  (ERecordCon (pos, n, i, ls), rty)

and primitive pos = function
  | PIntegerConstant _ -> TyApp (pos, TName "int",  [])
  | PUnit              -> TyApp (pos, TName "unit", [])
  | PCharConstant _    -> TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let p, denv = pattern env sty p in
  let env = concat pos env denv in
  let e, ty = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, _, (x, ty)) -> bind_simple pos x ty env)
    env1 (values env2)

and linear_bind pos env (ts, ps, (x, ty)) =
  (** Because patterns only bind monomorphic values. *)
  assert (ts = [] && ps = []);
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple pos x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, _, (x, ty)) ->
      assert (ts = []); (** Because patterns only bind monomorphic values. *)
      try
        let _, _, (_, ty') = lookup pos x denv2 in
        check_equal_types pos ty ty'
      with _ ->
        raise (PatternsMustBindSameVariables pos))
    (values denv1)

and pattern env xty = function
  | PVar (pos, name) ->
    let p = PVar (pos, elab_name name) in
    let denv = bind_simple pos name xty ElaborationEnvironment.empty in
    (p, denv)

  | PWildcard pos ->
    (PWildcard pos, ElaborationEnvironment.empty)

  | PAlias (pos, name, p) ->
    let p, env = pattern env xty p in
    (p, linear_bind pos env ([], [],  (name, xty)))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, prim) as p ->
    check_equal_types pos (primitive pos prim) xty;
    (p, ElaborationEnvironment.empty)

  | PData (pos, (DName x as d), tys, ps) ->
    let tys', qs, kty = type_application pos env (Name x) tys in
    assert (qs = []); (* Type constructors cannot have class predicates *)
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos);
    let psdenvs = List.map2 (pattern env) itys ps in
    let ps, denvs = List.split psdenvs in
    check_equal_types pos oty xty;
    let d' = elab_dname d in
    let p = PData (pos, d', tys', ps) in
    let denv = List.fold_left (join pos) ElaborationEnvironment.empty denvs in
    (p, denv)

  | PAnd (pos, ps) ->
    let psdenvs = List.map (pattern env xty) ps in
    let ps, denvs = List.split psdenvs in
    let denv = List.fold_left (join pos) ElaborationEnvironment.empty denvs in
    (PAnd (pos, ps), denv)

  | POr (pos, ps) ->
    let psdenvs = List.map (pattern env xty) ps in
    let ps, denvs = List.split psdenvs in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    (POr (pos, ps), denv)

(* [record_binding] elaborates the lname [l] and the expression [e],
 * also returning the type [ty] of [e] *)
and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  let l' = elab_lname l in
  (RecordBinding (l', e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let vs, env = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let vs, env = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, (x, ty), os) ->
    let ty' = elab_wf_type env KStar ty in
    let env = bind_scheme pos x ts [] ty env in
    let x' = elab_name x in
    (ExternalValue (pos, ts, (x', ty'), os), env)

and eforall pos ts e =
  match ts, e with
  | ts, EForall (pos, [], ((EForall _) as e)) ->
    eforall pos ts e

  | [], EForall (pos, [], e) ->
    e

  | [], EForall (pos, _, _) ->
    raise (InvalidNumberOfTypeAbstraction pos)

  | [], e ->
    e

  | x :: xs, EForall (pos, t :: ts, e) ->
    if x <> t then
      raise (SameNameInTypeAbstractionAndScheme pos);
    eforall pos xs (EForall (pos, ts, e))

  | _, _ ->
    raise (InvalidNumberOfTypeAbstraction pos)

and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  List.iter
    (fun (ClassPredicate (_, v)) ->
       if not (TS.mem v (free xty) && (* Unreachable constraint *)
               List.mem v ts) then (* Variable must have just been bound *)
         raise (InvalidOverloading pos))
    ps;

  let ps', local_dict_variables = dict_variables pos env ps in
  let env' = introduce_type_parameters env ts in
  let env' = add_predicates ps' env' in

  let x' = elab_name x in
  let xty' = elab_wf_type env' KStar xty in

  if is_value_form e then begin
    let e = eforall pos ts e in
    let e, ty = expression env' e in
    check_equal_types pos xty ty;
    let e, ty' = List.fold_right abstract local_dict_variables (e, xty') in
    let b = (x', ty') in
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme pos x ts ps ty env)

  end else begin
    if ts <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' e in
      check_equal_types pos xty ty;
      let b = (x', xty') in
      (ValueDef (pos, [], [], b, e), bind_simple pos x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  bind_scheme pos x ts ps ty env

and names_is is = List.fold_left names_i [] is

and names_i acc i = List.fold_left vn_recordbinding acc i.instance_members

and names_vb acc = function
  | BindValue (_, vs)
  | BindRecValue (_, vs)              ->
    List.fold_left names_vdef acc vs

  | ExternalValue (pos, _, (x, _), _) ->
    (pos, x) :: acc

and names_vdef acc (ValueDef (pos, _, _, (x, _), e)) =
  names_e ((pos, x) :: acc) e

and vn_recordbinding acc (RecordBinding (_, e)) =
  names_e acc e

and names_e acc = function
  | EVar _
  | EPrimitive _              ->
    acc

  | ELambda (pos, (x, _), e)  ->
    names_e ((pos, x) :: acc) e

  | EBinding (_, b, e)        ->
    let acc = names_vb acc b in
    names_e acc e

  | EApp (_, a, b)            ->
    let acc = names_e acc b in
    names_e acc a

  | ETypeConstraint (_, e, _)
  | EForall (_, _, e)
  | EExists (_, _, e)
  | ERecordAccess (_, e, _)   ->
    names_e acc e

  | EDCon (_, _, _, es)       ->
    List.fold_left names_e acc es

  | EMatch (_, s, bs)         ->
    let acc = names_e acc s in
    let vn_branch acc (Branch (pos, p, e)) =
      let acc = names_pattern acc p in
      names_e acc e
    in List.fold_left vn_branch acc bs

  | ERecordCon (_, _, _, rbs) ->
    List.fold_left vn_recordbinding acc rbs

and names_pattern acc = function
  | PVar (pos, x)             -> (pos, x) :: acc
  | PWildcard _
  | PPrimitive _              -> acc
  | PAlias (pos, x, p)        -> names_pattern ((pos, x) :: acc) p
  | PTypeConstraint (_, p, _) -> names_pattern acc p
  | PData (_, _, _, ps)
  | PAnd (_, ps)
  | POr (_, ps)               -> List.fold_left names_pattern acc ps
