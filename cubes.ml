(* ABCFHL cartesian cubical type theory, more or less *)

type name = string
type lvl = int and idx = int

module AST = struct
  type ty = exp
  and exp =
    (* Basics: x, e : t, let x = e₁; e₂, comp z. A [i-j] [α ↦ e] b *)
    | Var of name
    | Annot of exp * ty
    | Let of name * exp * exp
    | Comp of { z: name
              ; s: dim; t: dim
              ; ty: ty
              ; partial: partial
              ; cap: exp }
    (* Pi types: Πx:A. B(x), λx. e(x), e₁e₂ *)
    | Pi of name * ty * ty
    | Lam of name * exp
    | App of exp * exp
    (* Sigma types: Σx:A. B(x), (e₁, e₂), fst(e), snd(e) *)
    | Sigma of name * ty * ty
    | Pair of exp * exp
    | Fst of exp
    | Snd of exp
    (* Paths: Path A x y, <i> e, e @ i *)
    | PathTy of ty * exp * exp
    | PathTm of name * exp
    | DimApp of exp * dim
    (* Universes: U_i, Glue B [α ↦ T,e], glue [α ↦ t] b, unglue B [α ↦ T,e] x *)
    | U of int
    | GlueType of { b: ty; t_e: partial }
    | GlueTerm of { a: partial; b: exp }
    | Unglue of { b: ty; t_e: partial; x: exp }
  and partial = (dim * dim * exp) list
  and dim = Zero | DimVar of name | One
end

module Core = struct
  (* Just comments *)
  type 'a binds_one = 'a
  type 'a binds_a_dim = 'a

  type dim = Zero | DimVar of idx | One
  and ty = tm
  and tm =
    (* Basics: x, let x = e₁; e₂, comp z. A [i-j] [ α ↦ e ] b *)
    | Var of idx
    | Let of tm * tm binds_one
    | Comp of { ty: ty binds_a_dim
              ; s: dim; t: dim
              ; partial: tm binds_a_dim partial
              ; cap: tm }
    | Abort
    (* Pi types *)
    | Pi of name * ty * ty binds_one
    | Lam of name * tm binds_one
    | App of tm * tm
    (* Sigma types *)
    | Sigma of name * ty * ty binds_one
    | Pair of tm * tm
    | Fst of tm | Snd of tm
    (* Paths *)
    | PathTy of ty * tm * tm
    | DimAbs of name * tm binds_a_dim
    | DimApp of tm * dim
    (* Universes *)
    | U of int
    | GlueType of { b: ty; t_e: tm partial }
    | GlueTerm of { a: tm partial; b: tm }
    | Unglue of { t_e: tm partial; x: tm }
  and 'a partial = (dim * dim * 'a) list
end

module Domain = struct
  (*
  ATTEMPT 0: standard NbE semantic domain, as used in dependent typecheckers,
  with dimension variables and term variables both using de Bruijn levels.
  Problem: hard to evaluate "cube rules" like
    α ⊢ Glue [α ↦ T,e] B ≡ T
  which are not stable under context extension by cofibrations!

  ATTEMPT 1: that plus a "Depends" constructor: the semantic domain is now
  (lazily-evaluated) *decision trees* matching on whether certain equations
  hold. Now the rest of the code is able to decide which branch to take
  depending on the current context, which only it has access to.
  Problem: comp z. A [i-j] [α ↦ t] needs to pattern match on 'z. A' through the
  dimension binder. Can't do that when it's represented as a function dim -> d!

  ATTEMPT 2: Switch dimension binders to de Bruijn indices. Typecheckers usually
  get by with the semantic domain in PSh(ℂ) where ℂ is the category of contexts
  and context extensions, which is awesome since de Bruijn levels are stable
  under context extensions. But evaluation under binders requires to extend to
  the category of contexts and arbitrary context renamings (like used in NbE
  proofs), so we get something like "A categorical reconstruction of a
  reduction-free normalization proof":
    type idx n = Fin n (* finite sets of free variables *)
    type ren n m = idx n -> idx m
    data d n =
      | DFun (∀ m. ren n m -> d m -> d m)  (* the Kripke function space *)
      | DDimAbs (d (n+1))
      | ...

    (* renaming functions that apply substitutions *)
    (* these witness that d, dne are presheaves on the category of renamings *)
    val ren : ren n m -> d n -> d m
    val ren_ne : ren n m -> dne n -> dne m
  Problem: dimension application p @ i needs to substitute arbitrary dim's, not
  just rename them!

  ATTEMPT 3: Extend the renamings to functions idx -> dim, or, with more types:
    type dim n = Zero | DimVar (idx n) | One
    type ren n m = idx n -> dim m
  And woah! dim is the +2 monad on FinSet, and ren n m are its Kleisli arrows,
  so this makes d, dne exactly presheaves on the Cartesian cube category!

  *)

  type dim (*n*) = Zero | DimVar of idx (*n*) | One
  type eqn = dim * dim
  type 'a partial = (dim * dim * 'a) list

  (* Renamings of the dimension context -- it's the Cartesian cube category! *)
  module Ren : sig
    type ren (* n m *)

    val id : ren (* n n *)
    val compose : ren (* m l *) -> ren (* n m *) -> ren (* n l *)

    val shift_up : ren (* n (n+1) *)
    val app : dim (* n *) -> ren (* (n+1) n *)
    val extend : ren (* n n *) -> ren (* (n+1) (n+1) *)

    val ren_dim : ren (* n m *) -> dim (* n *) -> dim (* m *)
  end = struct
    (* future TODO: defunctionalize to get a more performant implementation
       (I expect it to be crucial for performance!) *)
    type ren = idx -> dim
    let id x = DimVar x
    let compose r' r x = match r x with
      | Zero -> Zero
      | One  -> One
      | DimVar i -> r' i

    let shift_up x = DimVar (x+1)
    let app dim i = if i = 0 then dim else DimVar (i-1)
    let extend r i =
      if i = 0 then DimVar 0 else
      match r (i - 1) with
        | Zero -> Zero
        | One  -> One
        | DimVar i' -> DimVar (1 + i')

    let ren_dim r = function
      | Zero -> Zero
      | One  -> One
      | DimVar i -> r i
  end
  open Ren

  (* an annotation for documentation purposes *)
  type 'a binds_a_dim = 'a

  (* the semantic domain (?) *)
  type dl = d Lazy.t
  and d =
    (* Basics: neutrals, things that depend on intervals *)
    | Depends of { eqn: eqn; yes: dl; no: dl }
    | DNe of dne
    (* Pi types *)
    | DPi of name * dl * (ren -> dl -> d)
    | DLam of name * (ren -> dl -> d)
    (* Sigma types *)
    | DSigma of name * dl * (ren -> dl -> d)
    | DPair of dl * dl
    (* Paths *)
    | DPathTy of dl * dl * dl
    | DDimAbs of name * dl binds_a_dim
    (* Universes *)
    | DU of int
    | DGlueType of { b: dl; t_e: dl partial }
    | DGlueTerm of { a: dl partial; b: dl }
  and dne =
    (* Basics *)
    | DVar of lvl
    | DComp of { z: name
               ; s: dim; t: dim
               ; ty: dne binds_a_dim
               ; partial: dl binds_a_dim partial
               ; cap: dl }
    (* Pi *)
    | DApp of dne * dl
    (* Sigma *)
    | DFst of dne
    | DSnd of dne
    (* Path *)
    | DDimApp of dne * dim
    (* Universes *)
    | DUnglue of dl partial * dne

  (* CHECK: ren id = id
            ren f ∘ ren g = ren (f ∘ g)
   *)
  let ren_dim = Ren.ren_dim
  let rec ren (r : ren) (tm : dl): d = match Lazy.force tm with
    | Depends { eqn = i, j; yes; no } ->
        Depends { eqn = ren_dim r i, ren_dim r j
                ; yes = lazy (ren r yes)
                ; no  = lazy (ren r no) }
    | DNe ne ->
        DNe (ren_ne r ne)
    | DPi(name, a, b) ->
        DPi(name, lazy (ren r a), fun s x -> b (compose s r) x)
    | DLam(name, f) ->
        DLam(name, fun s x -> f (compose s r) x)
    | DSigma(name, a, b) ->
        DSigma(name, lazy (ren r a), fun s x -> b (compose s r) x)
    | DPair(a, b) ->
        DPair(lazy (ren r a), lazy (ren r b))
    | DPathTy(a, lhs, rhs) ->
        DPathTy(lazy (ren r a), lazy (ren r lhs), lazy (ren r rhs))
    | DDimAbs(name, p) ->
        DDimAbs(name, lazy (ren (extend r) p))
    | DU i ->
        DU i
    | DGlueType { b; t_e } ->
        let b = lazy (ren r b) in
        let t_e = List.map (fun (i, j, t) ->
          (ren_dim r i, ren_dim r j, lazy (ren r t))) t_e in
        DGlueType { b; t_e }
    | DGlueTerm { a; b } ->
        let a = List.map (fun (i, j, t) ->
          (ren_dim r i, ren_dim r j, lazy (ren r t))) a in
        let b = lazy (ren r b) in
        DGlueTerm { a; b }

  and ren_ne r = function
    | DVar l -> DVar l
    | DComp { z; s; t; ty; partial; cap } ->
        let r' = extend r in
        let ren_partial_elem (i, j, t) =
          (ren_dim r i, ren_dim r j, lazy (ren r' t)) in
        DComp { z = z
              ; s = ren_dim r s; t = ren_dim r t
              ; ty = ren_ne r' ty
              ; partial = List.map ren_partial_elem partial
              ; cap = lazy (ren r cap) }
    | DApp(f, x) ->
        DApp(ren_ne r f, lazy (ren r x))
    | DFst x ->
        DFst (ren_ne r x)
    | DSnd x ->
        DSnd (ren_ne r x)
    | DDimApp(p, d) ->
        DDimApp(ren_ne r p, ren_dim r d)
    | DUnglue(t_e, g) ->
        let t_e = List.map (fun (i, j, t) ->
          (ren_dim r i, ren_dim r j, lazy (ren r t))) t_e in
        let g = ren_ne r g in
        DUnglue(t_e, g)

  type env =
    | ENil                (* ENil : env n *)
    | EVal of env * dl    (* EVal : env n -> d n -> env n *)
    | EDim of env * dim   (* EDim : env n -> dim n -> env n *)
    | ERen of env * ren   (* ERen : ∀ m. env m -> ren m n -> ren n *)

end


module Eval : sig
  open Domain

  (* Push computations inside Depends *)
  val force : dl -> (d -> d) -> d
  val (let*) : dl -> (d -> d) -> d

  val app : dl -> dl -> d
  val fst : dl -> d
  val snd : dl -> d
  val dim_app : dl -> dim -> d
  val glue_type : dl -> dl partial -> d
  val glue_term : dl partial -> dl -> d
  val unglue : dl partial -> dl -> d

  val reify : dl -> dne -> d

  val eval : env -> Core.tm -> d
end = struct
  open Domain

  (* Push computations inside Depends *)
  let rec force x f = match Lazy.force x with
    | Depends { eqn; yes; no } ->
        Depends { eqn; yes = lazy (force yes f); no = lazy (force no f) }
    | x -> f x
  let (let*) = force

  let app f x = force f (function
    (* β rule: (λ x. f(x)) x ≡ f(x) *)
    | DLam(_, fn) -> fn Ren.id x
    | _ -> failwith "unreachable: internal type error")

  let fst x = force x (function
    (* β rule: fst (a, b) ≡ a *)
    | DPair(a, _) -> Lazy.force a
    | _ -> failwith "unreachable: internal type error")
  let snd x = force x (function
    (* β rule: snd (a, b) ≡ b *)
    | DPair(_, b) -> Lazy.force b
    | _ -> failwith "unreachable: internal type error")

  let dim_app p d = force p (function
    (* β rule: (<i> f(i)) @ i ≡ f(i) *)
    | DDimAbs(_, p) -> ren (Ren.app d) p
    | _ -> failwith "unreachable: internal type error")

  let rec glue_type b t_e = match t_e with
    (* Cube rule: α ⊢ Glue B [α ↦ T,e] ≡ T *)
    | (i,j,t_e)::rest ->
        Depends { eqn = i, j
                ; yes = lazy (fst t_e)
                ; no  = lazy (glue_type b rest) }
    | [] -> DGlueType { b; t_e }

  let rec glue_term a b = match a with
    (* Cube rule: α ⊢ glue [α ↦ t] b ≡ a *)
    | (i,j,t)::rest ->
        Depends { eqn = i, j
                ; yes = t
                ; no = lazy (glue_term rest b) }
    | [] -> DGlueTerm { a; b }

  let rec unglue t_e x = match t_e with
    (* Cube rule: α ⊢ unglue [α ↦ T,(f,pf)] x ≡ f(x) *)
    | (i,j,t_f_pf)::rest ->
        let f = lazy (fst (lazy (snd t_f_pf))) in
        Depends { eqn = i, j
                ; yes = lazy (app f x)
                ; no  = lazy (unglue rest x) }
    | [] -> force x (function
      (* β rule: unglue (glue [α ↦ a] (b)) ≡ b *)
      | DGlueTerm { a = _; b } -> Lazy.force b
      | _ -> failwith "unreachable: internal type error")

  (* Type-directed reification *)
  let rec reify (ty: dl) (tm: dne) = match Lazy.force ty with
    | Depends { eqn; yes; no } ->
        Depends { eqn = eqn
                ; yes = lazy (reify yes tm)
                ; no  = lazy (reify no  tm) }
    | DNe _ -> DNe tm
    | DPi(name, a, b) ->
        (* η rule: f = λ x. f x *)
        let name = if name = "_" then "x" else name in
        DLam(name, fun r x -> reify (lazy (b r x)) (ren_ne r (DApp(tm, x))))
    | DSigma(name, a, b) ->
        (* η rule: p ≡ (fst(p), snd(p)) *)
        let fst = lazy (reify a (DFst tm)) in
        DPair(fst, lazy (reify (lazy (b Ren.id fst)) (DSnd tm)))
    | DPathTy(a, lhs, rhs) ->
        (* η rule: p ≡ <i> p @ i *)
        DDimAbs("i", lazy begin
          (* Cube rule: p @ i0 ≡ lhs; p @ i1 ≡ rhs *)
          (* NOTE: bug-prone stuff here! should double check! *)
          let dim = DimVar 0 in
          let a = lazy (ren Ren.shift_up a) in
          let lhs = lazy (ren Ren.shift_up lhs) in
          let rhs = lazy (ren Ren.shift_up rhs) in
          Depends
            { eqn = dim, Zero
            ; yes = lhs
            ; no  = lazy (Depends
                { eqn = dim, One
                ; yes = rhs
                ; no  = lazy (reify a (DDimApp(tm, dim))) }) }
        end)
    | DU _ -> DNe tm
    | DGlueType { b; t_e } ->
        (* η rule: g ≡ glue [α ↦ g] (unglue [α ↦ T,e] g) *)
        let partial_g = List.map (fun (i, j, t_e) ->
          (i, j, lazy (reify (lazy (fst t_e)) tm))) t_e in

        (* Cube rule: α ⊢ unglue [α ↦ T,(f,pf)] g ≡ f(g) *)
        let unglue_tm =
          List.fold_right2
            (fun (i, j, t_f_pf) (i', j', g) r ->
              assert (i = i' && j = j');
              let f = lazy (fst (lazy (snd t_f_pf))) in
              lazy (Depends
                { eqn = i, j
                ; yes = lazy (app f g)
                ; no  = r }))
            t_e partial_g (lazy (reify b (DUnglue(t_e, tm)))) in

        glue_term partial_g unglue_tm

    | DLam _ | DPair _ | DDimAbs _ | DGlueTerm _ ->
        (* Even though glue(...) could sometimes be a type from the cube rules,
           it gets evaluated to Depends(α, ty, DGlueTerm _), so DGlueTerm only
           shows up when α is false and it's for sure not a type. *)
        failwith "unreachable: not a type"

  let lookup_tm : idx -> env -> d =
    let rec go r i = function
      | ENil -> failwith "unreachable: internal scoping error"
      | EVal(_, x) when i = 0 -> ren r x
      | EVal(e, _) | EDim(e, _) -> go r (i-1) e
      | ERen(e, r') -> go (Ren.compose r r') i e
    in go Ren.id
  let lookup_dim : idx -> env -> dim =
    let rec go r i = function
      | ENil -> failwith "unreachable: internal scoping error"
      | EDim(_, d) when i = 0 -> Ren.ren_dim r d
      | EVal(e, _) | EDim(e, _) -> go r i e
      | ERen(e, r') -> go (Ren.compose r r') i e
    in go Ren.id

  let rec eval (env : env) (tm : Core.tm) = match tm with
    (* Basics *)
    | Var idx -> lookup_tm idx env
    | Let(x, body) ->
        eval (EVal(env, lazy (eval env x))) body
    | Comp { ty; s; t; partial; cap } ->
        let env' = EDim(ERen(env, Ren.shift_up), DimVar 0) in
        (* ty : d (n+1) *)
        let ty = lazy (eval env' ty) in
        let s, t = eval_dim env s, eval_dim env t in
        (* partial : (d (n+1)) partial *)
        let partial = List.map (fun (i, j, t) ->
          (eval_dim env i, eval_dim env j, lazy (eval env' t))) partial in
        let cap = lazy (eval env cap) in
        comp ty s t partial cap
    | Abort ->
        failwith "unreachable: abort"

    (* Pi types *)
    | Pi(n, a, b) ->
        DPi(n, lazy (eval env a), fun r x -> eval (EVal(ERen(env, r), x)) b)
    | Lam(n, body) ->
        DLam(n, fun r x -> eval (EVal(ERen(env, r), x)) body)
    | App(f, x) ->
        let f, x = lazy (eval env f), lazy (eval env x) in
        app f x

    (* Sigma types *)
    | Sigma(n, a, b) ->
        DSigma(n, lazy (eval env a), fun r x -> eval (EVal(ERen(env, r), x)) b)
    | Pair(x, y) ->
        DPair(lazy (eval env x), lazy (eval env y))
    | Fst x ->
        fst (lazy (eval env x))
    | Snd x ->
        snd (lazy (eval env x))

    (* Paths *)
    | PathTy(a, lhs, rhs) ->
        DPathTy(lazy (eval env a), lazy (eval env lhs), lazy (eval env rhs))
    | DimAbs(n, tm) ->
        (* No need to handle cube rules here; it's handled in reify *)
        let env' = EDim(ERen(env, Ren.shift_up), DimVar 0) in
        DDimAbs(n, lazy (eval env' tm))
    | DimApp(p, d) ->
        dim_app (lazy (eval env p)) (eval_dim env d)

    (* Universes *)
    | U i -> DU i
    | GlueType { b; t_e } ->
        let b = lazy (eval env b) in
        let t_e = eval_partial env t_e in
        glue_type b t_e
    | GlueTerm { a; b } ->
        let a = eval_partial env a in
        let b = lazy (eval env b) in
        glue_term a b
    | Unglue { t_e; x } ->
        let t_e = eval_partial env t_e in
        let x = lazy (eval env x) in
        unglue t_e x

  and eval_dim env (d : Core.dim) = match d with
    | Zero -> Zero
    | One  -> One
    | DimVar idx -> lookup_dim idx env

  and eval_partial env (partial : Core.tm Core.partial) =
    List.map (fun (i, j, tm) ->
      eval_dim env i, eval_dim env j, lazy (eval env tm)) partial

  (* comp : d (n+1) -> dim n -> dim n -> (d (n+1)) partial -> d n -> d n *)
  (* NOTE: this whole thing is really hairy! try not to mess up indices! *)
  and comp ty s t partial cap = match Lazy.force ty with
    | Depends { eqn = i, j; yes; no } when i = j ->
        comp yes s t partial cap
    | Depends { eqn = i, j; yes; no } -> begin
        if i = DimVar 0 || j = DimVar 0 then
          (* one of them's bound and they're not equal *)
          comp no s t partial cap
        else
          let shift_down =
            function Zero -> Zero | One -> One | DimVar x -> DimVar (x-1) in
          Depends { eqn = shift_down i, shift_down j
                  ; yes = lazy (comp yes s t partial cap)
                  ; no  = lazy (comp no  s t partial cap) }
        end
    | DNe ne ->
        (* Cube rule: s = t ⊢ comp z. A [s-t] [α ↦ a] (b) ≡ b *)
        (* Cube rule: α ⊢ comp z. A [s-t] [α ↦ a] (b) ≡ a[t/z] *)
        failwith "TODO"
    | DPi(name, a, b) ->
        let name = if name = "_" then "x" else name in
        DLam(name, fun r x ->
          (* fuckkkkk *)
          failwith "TODO")
    | DSigma(name, a, b) ->
        let first = lazy
          (comp a s t
                (List.map (fun (i, j, x) -> (i, j, lazy (fst x))) partial)
                (lazy (fst cap))) in
        let r, r' = Ren.shift_up, Ren.extend Ren.shift_up in
        let first_path (* : d (n+1) *) = lazy
          (fill (lazy (ren r' a)) (Ren.ren_dim r s) (DimVar 0)
                (List.map (fun (i, j, x) ->
                  ( Ren.ren_dim r i
                  , Ren.ren_dim r j
                  , lazy (ren r' (lazy (fst x))))) partial)
                (lazy (ren r (lazy (fst cap))))) in
        let second = lazy
          (comp (lazy (b Ren.id first_path)) s t
                (List.map (fun (i, j, x) -> (i, j, lazy (snd x))) partial)
                (lazy (snd cap))) in
        DPair(first, second)
    | DPathTy(a, lhs, rhs) ->
        failwith "TODO"
    | DU univ_idx -> (* oh no *)
        failwith "TODO"
    | DGlueType { b; t_e } -> (* oh no *)
        failwith "TODO"
    | DLam _ | DPair _ | DDimAbs _ | DGlueTerm _ ->
        failwith "unreachable: type error: not a type"

  (* hcomp : d n -> dim n -> dim n -> (d (n+1)) partial -> d n -> d n *)
  (* hcomp is composition at a constant type *)
  and hcomp ty s t partial cap =
    comp (lazy (ren Ren.shift_up ty)) s t partial cap

  (* using fill instead of comp implies that t is a fresh dimension variable *)
  and fill ty = comp ty

  (* coe : d (n+1) -> dim n -> dim n -> d n -> d n *)
  (* coercion is composition with no partial elements *)
  and coe ty s t cap = comp ty s t [] cap
end

module Ctx : sig
  open Domain

  exception NotInScope of name

  (* don't particularly like it but it's eh *)
  type 'ctx split_on_eqn_result =
    | Yes of 'ctx
    | No of 'ctx
    | Either of { yes: 'ctx; no: 'ctx }

  class type ctx =
    object
      method lvl : lvl
      method env : env
      method names : name list
      method lookup_var : name -> dl * dl
      method lookup_dim : name -> dim
      method with_var  : name -> dl -> dl * ctx
      method with_defn : name -> dl -> dl -> ctx
      method with_dim_var : name -> dim * ctx
      method with_eqn : eqn -> ctx option
      method split_on_eqn : eqn -> ctx split_on_eqn_result
      method entails : eqn -> bool
      method are_cofibs_equal : eqn list -> eqn list -> bool
    end

  val initial_ctx : ctx
end = struct
  (* TODO FIXME: this is wrong!
     It still treats dim vars as levels, not indices!
     Need to rethink how it works! *)
  open Domain

  exception NotInScope of name

  module IntMap = Map.Make (Int)
  type formula = int IntMap.t

  let find dim formula =
    let rec go i =
      let p = IntMap.find i formula in
      if p = i then i else go p in
    go (match dim with Zero -> 0 | One -> 1 | DimVar x -> 2 + x)
  let union d1 d2 formula =
    let a, b = find d1 formula, find d2 formula in
    IntMap.add (min a b) (max a b) formula
  let is_inconsistent formula diseq =
    List.exists (fun (a, b) -> find a formula = find b formula) diseq

  type 'ctx split_on_eqn_result =
    | Yes of 'ctx
    | No of 'ctx
    | Either of { yes: 'ctx; no: 'ctx }

  class ctx lvl names tys env formula diseq =
    object (self)
      method lvl : lvl = lvl
      method env : env = env
      method names : name list = names

      method lookup_var name =
        let rec go r ns ts es = match ns, ts, es with
          | _, _, ERen(es, r') -> go (Ren.compose r r') ns ts es
          | n::_, Some t::_, EVal(_, e) when n = name -> t, ren r e
          | _::ns, _::ts, (EVal(e, _) | EDim(e, _)) -> go r ns ts es
          | [], [], ENil -> raise (NotInScope name)
          | _ -> failwith "unreachable" in
        go Ren.id names tys env
      method lookup_dim name =
        let rec go r ns ts es = match ns, ts, es with
          | _, _, ERen(es, r') -> go (Ren.compose r r') ns ts es
          | n::_, Some t::_, EDim(_, d) when n = name -> t, ren_dim r d
          | _::ns, _::ts, (EVal(e, _) | EDim(e, _)) -> go r ns ts es
          | [], [], ENil -> raise (NotInScope name)
          | _ -> failwith "unreachable" in
        go Ren.id names tys env

      method with_defn name ty x =
        let ctx' = new ctx (lvl+1)
          (name::names) (Some ty::tys) (EVal(env, x))
          formula diseq in
        ctx'
      method with_var name ty =
        let x = lazy (Eval.reify ty (DVar lvl)) in
        x, self#with_defn name ty x
      method with_dim_var name =
        let x = DimVar lvl in
        let ctx' = new ctx (lvl+1)
          (name::names) (None::tys) (EDim(env, x))
          formula diseq in
        x, ctx'

      method with_eqn (x, y) =
        let formula' = union x y formula in
        if is_inconsistent formula diseq then
          None
        else
          Some (new ctx lvl names tys env formula' diseq)
      method split_on_eqn (x, y) =
        if find x formula = find y formula then
          Yes (self :> ctx)
        else
          let formula' = union x y formula in
          if is_inconsistent formula' diseq then
            No (self :> ctx)
          else
            Either { yes = new ctx lvl names tys env formula' diseq
                   ; no  = new ctx lvl names tys env formula ((x,y)::diseq) }

      method entails (x, y) =
        find x formula = find y formula

      method are_cofibs_equal xs ys =
        let implies a b =
          List.for_all (fun (x, y) ->
            is_inconsistent (union x y formula) b) a in
        implies xs ys && implies ys xs
    end

  let initial_ctx =
    new ctx 0 [] [] ENil IntMap.(add 0 0 (singleton 1 1)) [Zero, One]
end

module Pretty : sig
  open Domain

  (* Pretty-printing *)
  val show : Ctx.ctx -> dl -> dl -> string
end = struct
  open Domain

  (* TODO: pretty-printing *)
  let show (ctx : Ctx.ctx) ty tm =
    failwith "TODO"
end

module Conv : sig
  open Domain

  (* Conversion checking *)
  val eq : Ctx.ctx -> dl -> dl -> dl -> bool
end = struct
  open Domain

  exception NotEqual

  (* TODO: conversion checking *)
  let rec conv (ctx : Ctx.ctx) (ty : dl) (a : dl) (b : dl) =
    failwith "TODO"


  let eq ctx ty a b =
    match conv ctx ty a b with
      | () -> true
      | exception NotEqual -> false
end

module Tychk = struct
  (* open Core *)
  open Domain

  exception TypeError of string

  (* the main check/infer loop! *)
  let rec check (ctx: Ctx.ctx) (exp: AST.exp) (ty: dl) = match exp, ty with
    | _ -> failwith "TODO"

  and infer (ctx: Ctx.ctx) (exp: AST.exp) = match exp with
    | _ -> failwith "TODO"

end

(* Aaaaaaaaaaaa a annoying thing:
  Why are disjunctions in trivial cofibrations a thing anyways?
  What are they for?
  Why merge partial elements?
  Like, ok, in some context Ψ;φ;Γ,

  [ (i=0)∨(i=1) ↦   something with p @ i ]

  now there's just like, two completely different values being packed into one
  is there any time I couldn't just
    [ (i=0) ↦  something with p @ 0
    | (i=1) ↦  something with p @ 1 ] ?
  If not I really wanna straight up do away with all the disjunctions and have a
  cube formula of ONLY EQUATIONS (the joy!)
  Other things that would improve from a cube formula of ONLY EQUATIONS:
    - Maintain it as a union-find datastructure, use the functional Map module
    - Discover conflicts when they arise; no need to ask for consistency checks
      on every function
    - Really efficient cofibration entailment

  For this to work, need to check that none of the Kan operations introduce
  disjunctions in inconvenient places.
  In particular need to figure out how quantifier elimination works.


*)


(* Need type-directed conversion checking! Nasty.

new domain design, for cube rules: evaluate into a *decision tree* of values:

  type dl = d Lazy.t
  and d =
    | Depends of { eqn: dim * dim; yes: dl; no: dl }
    | Other Stuff

The evaluator doesn't even get access to the cube context; instead, when it
wants to know if a cube equation holds, it puts a Depends.
Applications/projections/other continuations distribute over Depends

Then the ctx gets a method

  type 'ctx split_on_eqn_result =
    | Yes of 'ctx
    | No of 'ctx
    | Either of { yes: 'ctx; no: 'ctx }

  class type ctx =
    object
      other stuff
      method split_on_eqn : eqn -> ctx split_on_eqn_result
    end

(Does only the conv_ctx get it, or does the elab_ctx need it too?
I think only the conv_ctx needs it; the elab_ctx instead just gets with_eqn)

 *)



(* AAaaaaaaaaaaaAAAAAAA how do I make sure arbitrary neutral forms like

    fst(f x) @ i0

evaluate to the right things????

Answer: *use the full reify machinery!*  Type-directed eta-elongation will make
it work.  Plus as a bonus it handles other eta stuffs



can't have disequalities in the elab_ctx:
during elab, take the 'no' branch when it's not necessarily true, but don't
enforce that it *stays* not true in every context extension
  - in elab, 'no' means 'not necessarily'
  - in conv, 'no' can safely be interpreted as 'necessarily not' (?) possibly?
→ both contexts should possibly use some other simpler context
→ WHAT ABOUT: how to do conv at a Depends type???


Gotta be *veeeeeeeeeeery careful* not to accidentally throw out information:
  need to be able to take the 'not necessarily' case but also take the 'yes'
  case some other time in the short future; being in the 'no' case *does not*
  grant the evaluator permission to assume it *stays* false
This seems like a reasonable restriction, but it's vague and I should pin down
exactly what it means: for how long is it allowed to assume it's false?

I wish there were a better way to do this


Need to check: can every cube rule be handled in this way?
(Can every new η rule be handled in this way too?)

Where the Cube Rules run (note: perfectly safe for β rules to take precedence):
  - Kan composition: in eval for comp at a neutral type
  - paths: in reification at path type
  - Glue type: in eval for Glue
  - glue term: in eval for glue
  - unglue term: in eval for unglue of a neutral term

*)



(* TODO: add ⊤/⊥ types, tt : ⊤, abort : ∀ A → ⊥ → A *)


