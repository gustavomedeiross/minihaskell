open String
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))

let fresh = 
  let a = ref 0 in
  (fun () -> incr a;
    !a)

let rec program p = handle_error List.(fun () ->
    flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p)))

and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let names = names_vb [] d in
    let env = List.fold_left add_name env names in
    let d, env = value_binding env d in
    ([BDefinition d], env)

  (* We transform class definition into type definition. Next, we call block
     recursively. *)

  | BClassDefinition c ->
    let env    = bind_class c.class_name c env in
    let single_record = elaborate_class c env in   
    block env (BTypeDefinitions single_record)

  (* Idem *)

  | BInstanceDefinitions is ->
    let is' = List.map (function
        | { instance_class_name = TName s } as i ->
          (i, IName (s, fresh ()))
        | _ -> assert false)
        is in   
    let env = List.fold_left bind_instance env is' in
    check_instance_definitions env is;
    let dictionaries = elaborate_instance env is' in
    block env (BDefinition dictionaries)

(* (K 'a => ... => L 'b => ty) to
 * ('a k -> ... -> 'b l -> ty) *)
and arrow_of_predicates ps ty =
  let type_of_predicate = function
    | ClassPredicate (TName k, tvar) ->
      TyApp (undefined_position, CName k, [TyVar (undefined_position, tvar)])
    | ClassPredicate (CName _, _) -> assert false in
  ntyarrow undefined_position (List.map type_of_predicate ps) ty

and lambda_of_predicates ps e =
  let lop e = function
    | ClassPredicate (TName k, tvar) -> assert false
    | ClassPredicate (CName _, _) -> assert false in
  List.fold_left lop e ps

and elaborate_instance env is =
  let to_value (i, name) =
    let cname = match i.instance_class_name with
      | CName s -> assert false
      | TName s -> CName s in 
    let itype =
      if i.instance_parameters = [] then 
        TyVar (undefined_position, i.instance_index)
      else
        TyApp (
          undefined_position,
          i.instance_index,
          List.map (fun tn -> TyVar (undefined_position, tn))
            i.instance_parameters) in
    let binding =
      (name,
       arrow_of_predicates
         i.instance_typing_context
         (TyApp (undefined_position, cname, [itype]))) in
    let fs = i.instance_members in
    let record = ERecordCon (
        i.instance_position,
        name, (* WTF ? *)
        [itype],
        fs) in
    let e = lambda_of_predicates i.instance_typing_context record in
    ValueDef (
      i.instance_position,
      i.instance_parameters,
      [], (* Elaboration eliminates class predicates *)
      binding,
      e) in 
  BindRecValue (undefined_position, List.map to_value is)

(* TODO: Superclasses are not dealt with correctly *)
and elaborate_class c env =
  match c.class_name with 
  | TName name ->
    TypeDefs
      (c.class_position, 
       [TypeDef
          (c.class_position,
           KArrow (KStar,KStar),
           CName name,
           DRecordType ([c.class_parameter],
                        c.class_members))]) 
  | CName name -> assert false (*By construction*)

and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds

  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (pos, DName k, ts, kty) =
  check_wf_scheme env ts kty pos;
  bind_scheme pos (Name k) ts [] kty env

and introduce_type_parameters env ts ps pos =
  List.iter
    (fun (ClassPredicate(a,b)) ->
       if not (List.mem b ts) then raise (InvalidOverloading pos))
    ps; 
  let env = List.fold_left (fun env t -> bind_type_variable t env) env ts in
  let env = add_predicates ps env pos in     
  let env = add_unconstrained_tv ts env ps in
  env

and check_wf_scheme env ts ty pos =
  check_wf_type (introduce_type_parameters env ts [] pos) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()

  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys

  | _ -> raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
  | KStar, KStar -> ()

  | KArrow (k1, k2), KArrow (k1', k2') ->
    check_equivalent_kind pos k1 k1';
    check_equivalent_kind pos k2 k2'

  | _ -> raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env = function
  | BindValue (_, vs)
  | BindRecValue (_, vs) ->
    List.fold_left
      (fun env (ValueDef (pos, ts, pred, (x, ty), _)) ->
         bind_scheme pos x ts pred ty env)
      env vs

  | ExternalValue (pos, ts, (x, ty), _) ->
    bind_scheme pos x ts [] ty env

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2)
  then raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, ps, (_, ty)) = lookup pos x env in
  let assoc =
    try
      List.combine ts tys
    with _ -> raise (InvalidTypeApplication pos) in
  List.iter
    (fun (ClassPredicate (k, t)) ->
       is_instance_of pos (List.assoc t assoc) k env)
    ps;
  substitute assoc ty

and expression env = function
  | EVar (pos, x, tys) ->
    (EVar (pos, x, tys), type_application pos env x tys)

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple pos x aty env in
    let (e, ty) = expression env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

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

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables are useless. *)
    expression env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
            let (e, ty) = expression env e in
            check_equal_types pos ty xty;
            e
          ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
    let (ts, lty, rtcon) = lookup_label pos l env in
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
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
          | None ->
            let rty = TyApp (pos, rtcon, i) in
            let s =
              try
                List.combine ts i
              with _ -> raise (InvalidRecordInstantiation pos)
            in
            (s, rty)
          | Some (s, rty) ->
            (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ -> TyApp (pos, TName "int",  [])
  | PUnit              -> TyApp (pos, TName "unit", [])
  | PCharConstant _    -> TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, _, (x, ty)) -> bind_simple pos x ty env)
    env1 (values env2)

and linear_bind pos env (ts, _, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
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
        let (_, _, (_, ty')) = lookup pos x denv2 in
        check_equal_types pos ty ty'
      with _ ->
        raise (PatternsMustBindSameVariables pos))
    (values denv1)

and pattern env xty = function
  | PVar (pos, name) ->
    bind_simple pos name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], [],  (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme pos x ts [] ty env in
    (ExternalValue (pos, ts, b, os), env)

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
  let env' = introduce_type_parameters env ts ps pos in  (*TODO : WHY ?*)
  check_wf_type env' KStar xty;
  List.iter
    (fun (ClassPredicate (c, v)) -> 
       if not (TS.mem v (free xty)) then
         raise (InvalidOverloading pos)) 
    ps;
  if is_value_form e then begin
    let e = eforall pos ts e in
    let e, ty = expression env' e in
    let b = (x, ty) in
    check_equal_types pos xty ty;
    (*
<<<<<<< HEAD
    (ValueDef (pos, ts, ps, b, EForall (pos, ts, e)),
     bind_scheme pos x ts ps ty env)
  end
  else if ts <> [] then
    raise (ValueRestriction pos)
  else begin
    let e = eforall pos [] e in
    let e, ty = expression env e in
    let b = (x, ty) in
    if ps <> [] then raise (InvalidOverloading pos);
    check_equal_types pos xty ty;
    (ValueDef (pos, [], [], b, e), bind_simple pos x ty env)
=======*)
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme pos x ts ps ty env)
  end else begin
    if ts <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple pos x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  bind_scheme pos x ts ps ty env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _              ->
    true

  | EDCon (_, _, _, es)       ->
    List.for_all is_value_form es

  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs

  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t)         ->
    is_value_form t

  | _                         ->
    false

(*
 * - "7.2.1 RESTRICTIONS The restriction to types of the form K a in typing
 * contexts and class declarations, and to types of the form K (G a) in
 * instances are for simplicity. Generalizations are possible and discussed
 * later (7.4)"
*)

and check_method env pos ts ps s k (RecordBinding (l, e)) = match l with
  | KName _ -> assert false
  | LName l -> 
    let xty = lookup_method pos k (LName l) in
    let xty = substitute [k.class_parameter, s] xty in 
    ignore (value_definition env (ValueDef (pos, [], [], (Name l, xty), e)))

and check_instance_definitions env = function
  | [] -> ()
  | { instance_position       = pos;
      instance_parameters     = ts;
      instance_typing_context = ps; } as i :: t ->
    let env = introduce_type_parameters env ts ps pos in  (*TODO : WHY ?*)
    List.iter 
      (check_method env pos ts ps
         (cons_type i.instance_index ts)
         (lookup_class pos i.instance_class_name env))
      i.instance_members

and cons_type hd vars =
  TyApp (undefined_position,
         hd,
         List.map (fun x -> TyVar (undefined_position, x)) vars)

and names_vb acc = function
  | BindValue (_, vs)
  | BindRecValue (_, vs)              ->
    List.fold_left names_vdef acc vs

  | ExternalValue (pos, _, (x, _), _) ->
    (pos, x) :: acc

and names_vdef acc (ValueDef (pos, _, _, (x, _), e)) =
  names_e ((pos, x) :: acc) e

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
    let vn_recordbinding acc (RecordBinding (_, e)) = names_e acc e in
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
