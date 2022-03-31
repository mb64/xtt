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

    (* renaming functions *)
    (* these witness that d, dne are presheaves on the category of renamings *)
    val ren : ren n m -> d n -> d m
    val ren_ne : ren n m -> dne n -> dne m
  Problem: dimension application p @ i needs to substitute arbitrary dim's, not
  just rename them!

  ATTEMPT 3: Extend the renamings to substitutions idx -> dim:
    type dim n = Zero | DimVar (idx n) | One
    type sub n m = idx n -> dim m
    data d n =
      | DFun (∀ m. sub n m -> d m -> d m)
      | ...
    val subst : sub n m -> d n -> d m
  And woah! dim is the +2 monad on FinSet, and sub n m are its Kleisli arrows,
  so this makes d, dne exactly presheaves on the Cartesian cube category!

  *)

  module TypeNats : sig
    (* Abstract types used to index things by the length of the context *)
    type z
    type 'a s
  end = struct type z = Z and 'a s = S end
  include TypeNats

  type 'n dim = Zero | DimVar of idx (*n*) | One
  type 'n eqn = 'n dim * 'n dim
  type ('a, 'n) partial = ('n dim * 'n dim * 'a) list

  (* Substitutions of the dimension context -- it's the Cartesian cube category!
   *)
  module Sub : sig
    type ('n, 'm) sub

    val id : ('n, 'n) sub
    val compose : ('m, 'l) sub -> ('n, 'm) sub -> ('n, 'l) sub

    val shift_up : ('n, 'n s) sub
    val app : 'n dim -> ('n s, 'n) sub
    val extend : ('n, 'm) sub -> ('n s, 'm s) sub

    val subst_dim : ('n, 'm) sub -> 'n dim -> 'm dim
  end = struct
    (* future TODO: defunctionalize to get a more performant implementation
       (I expect it to be crucial for performance!) *)
    type ('n, 'm) sub = idx -> 'm dim
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

    let subst_dim r = function
      | Zero -> Zero
      | One  -> One
      | DimVar i -> r i
  end
  open Sub

  (* the semantic domain (?) *)
  type 'n dl = 'n d lazy_t
  and 'n d =
    (* Basics: neutrals, things that depend on intervals *)
    | Depends of { eqn: 'n eqn; yes: 'n dl; no: 'n dl }
    | DNe of 'n dne
    (* Pi types *)
    | DPi of { name: name; a: 'n dl; b: 'm. ('n, 'm) sub -> 'm dl -> 'm d }
    | DLam of { name: name; f: 'm. ('n, 'm) sub -> 'm dl -> 'm d }
    (* Sigma types *)
    | DSigma of { name: name; a: 'n dl; b: 'm. ('n, 'm) sub -> 'm dl -> 'm d }
    | DPair of 'n dl * 'n dl
    (* Paths *)
    | DPathTy of 'n dl * 'n dl * 'n dl
    | DDimAbs of name * 'n s dl (* binds a dimension! *)
    (* Universes *)
    | DU of int
    | DGlueType of { b: 'n dl; t_e: ('n dl, 'n) partial }
    | DGlueTerm of { a: ('n dl, 'n) partial; b: 'n dl }
  and 'n dne =
    (* Basics *)
    (* Variables remember their type, to reconstruct types during conversion
       checking. Could look it up in the context instead but this is more
       convenient *)
    | DVar of lvl * 'n dl
    | DComp of { z: name
               ; s: 'n dim; t: 'n dim
               ; ty: 'n s dne (* binds a dimension! *)
               ; partial: ('n s dl, 'n) partial
               ; cap: 'n dl }
    (* Pi *)
    | DApp of 'n dne * 'n dl
    (* Sigma *)
    | DFst of 'n dne
    | DSnd of 'n dne
    (* Path *)
    | DDimApp of 'n dne * 'n dim
    (* Universes *)
    | DUnglue of ('n dl, 'n) partial * 'n dne

  (* CHECK: subst id = id
            subst f ∘ subst g = subst (f ∘ g)
   *)
  type ('n, 'm) sub = ('n, 'm) Sub.sub

  let subst_dim = Sub.subst_dim

  let rec subst : 'n 'm. ('n, 'm) sub -> 'n dl -> 'm d =
    fun r tm -> match Lazy.force tm with
    | Depends { eqn = i, j; yes; no } ->
        Depends { eqn = subst_dim r i, subst_dim r j
                ; yes = lazy (subst r yes)
                ; no  = lazy (subst r no) }
    | DNe ne ->
        DNe (subst_ne r ne)
    | DPi { name; a; b } ->
        DPi { name; a = lazy (subst r a); b = fun s x -> b (compose s r) x }
    | DLam { name; f } ->
        DLam { name; f = fun s x -> f (compose s r) x }
    | DSigma { name; a; b } ->
        DSigma { name; a = lazy (subst r a); b = fun s x -> b (compose s r) x }
    | DPair(a, b) ->
        DPair(lazy (subst r a), lazy (subst r b))
    | DPathTy(a, lhs, rhs) ->
        DPathTy(lazy (subst r a), lazy (subst r lhs), lazy (subst r rhs))
    | DDimAbs(name, p) ->
        DDimAbs(name, lazy (subst (extend r) p))
    | DU i ->
        DU i
    | DGlueType { b; t_e } ->
        let b = lazy (subst r b) in
        let t_e = List.map (fun (i, j, t) ->
          (subst_dim r i, subst_dim r j, lazy (subst r t))) t_e in
        DGlueType { b; t_e }
    | DGlueTerm { a; b } ->
        let a = List.map (fun (i, j, t) ->
          (subst_dim r i, subst_dim r j, lazy (subst r t))) a in
        let b = lazy (subst r b) in
        DGlueTerm { a; b }

  and subst_ne : 'n 'm. ('n, 'm) sub -> 'n dne -> 'm dne =
    fun r tm -> match tm with
    | DVar(l, ty) -> DVar(l, lazy (subst r ty))
    | DComp { z; s; t; ty; partial; cap } ->
        let r' = extend r in
        let subst_partial_elem (i, j, t) =
          (subst_dim r i, subst_dim r j, lazy (subst r' t)) in
        DComp { z = z
              ; s = subst_dim r s; t = subst_dim r t
              ; ty = subst_ne r' ty
              ; partial = List.map subst_partial_elem partial
              ; cap = lazy (subst r cap) }
    | DApp(f, x) ->
        DApp(subst_ne r f, lazy (subst r x))
    | DFst x ->
        DFst (subst_ne r x)
    | DSnd x ->
        DSnd (subst_ne r x)
    | DDimApp(p, d) ->
        DDimApp(subst_ne r p, subst_dim r d)
    | DUnglue(t_e, g) ->
        let t_e = List.map (fun (i, j, t) ->
          (subst_dim r i, subst_dim r j, lazy (subst r t))) t_e in
        let g = subst_ne r g in
        DUnglue(t_e, g)

  type 'n env =
    | ENil : 'n env
    | EVal : 'n env * 'n dl -> 'n env
    | EDim : 'n env * 'n dim -> 'n env
    | ESub : 'm env * ('m, 'n) sub -> 'n env

end


module Eval : sig
  open Domain

  (* Push computations inside Depends *)
  val force : 'n dl -> ('n d -> 'n d) -> 'n d

  val app : 'n dl -> 'n dl -> 'n d
  val fst : 'n dl -> 'n d
  val snd : 'n dl -> 'n d

  val un_dim_abs : 'n dl -> 'n s d
  val dim_app : 'n dl -> 'n dim -> 'n d

  val glue_type : 'n dl -> ('n dl, 'n) partial -> 'n d
  val glue_term : ('n dl, 'n) partial -> 'n dl -> 'n d
  val unglue : ('n dl, 'n) partial -> 'n dl -> 'n d

  val reify : 'n dl -> 'n dne -> 'n d

  val eval : 'n env -> Core.tm -> 'n d
end = struct
  open Domain

  (* Push computations inside Depends *)
  let rec force x f = match Lazy.force x with
    | Depends { eqn; yes; no } ->
        Depends { eqn; yes = lazy (force yes f); no = lazy (force no f) }
    | x -> f x

  let app f x = force f (function
    (* β rule: (λ x. f(x)) x ≡ f(x) *)
    | DLam { f } -> f Sub.id x
    | _ -> failwith "unreachable: internal type error")

  let fst x = force x (function
    (* β rule: fst (a, b) ≡ a *)
    | DPair(a, _) -> Lazy.force a
    | _ -> failwith "unreachable: internal type error")
  let snd x = force x (function
    (* β rule: snd (a, b) ≡ b *)
    | DPair(_, b) -> Lazy.force b
    | _ -> failwith "unreachable: internal type error")

  let rec un_dim_abs tm = match Lazy.force tm with
    | Depends { eqn = i, j; yes; no } ->
        let eqn' = subst_dim Sub.shift_up i, subst_dim Sub.shift_up j in
        Depends { eqn = eqn'
                ; yes = lazy (un_dim_abs yes)
                ; no  = lazy (un_dim_abs no) }
    | DDimAbs(_, p) -> Lazy.force p
    | _ -> failwith "unreachable: internal type error: should'a been a path"

  let dim_app p d = subst (Sub.app d) (lazy (un_dim_abs p))

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
  let rec reify : 'n. 'n dl -> 'n dne -> 'n d = fun ty tm ->
    match Lazy.force ty with
    | Depends { eqn; yes; no } ->
        Depends { eqn = eqn
                ; yes = lazy (reify yes tm)
                ; no  = lazy (reify no  tm) }
    | DNe _ -> DNe tm
    | DPi { name; a; b } ->
        (* η rule: f = λ x. f x *)
        let name = if name = "_" then "x" else name in
        DLam { name
             ; f = fun r x -> reify (lazy (b r x)) (DApp(subst_ne r tm, x)) }
    | DSigma { name; a; b } ->
        (* η rule: p ≡ (fst(p), snd(p)) *)
        let fst = lazy (reify a (DFst tm)) in
        DPair(fst, lazy (reify (lazy (b Sub.id fst)) (DSnd tm)))
    | DPathTy(a, lhs, rhs) ->
        (* η rule: p ≡ <i> p @ i *)
        DDimAbs("i", lazy begin
          (* Cube rule: p @ i0 ≡ lhs; p @ i1 ≡ rhs *)
          let dim = DimVar 0 in
          let a = lazy (subst Sub.shift_up a) in
          let lhs = lazy (subst Sub.shift_up lhs) in
          let rhs = lazy (subst Sub.shift_up rhs) in
          let tm = subst_ne Sub.shift_up tm in
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
        (* Even though glue(...) could sometimes be a type via the cube rules,
           it gets evaluated to Depends(α, ty, DGlueTerm _), so DGlueTerm only
           shows up when α is false and it's for sure not a type. *)
        failwith "unreachable: not a type"

  let lookup_tm : 'n. idx -> 'n env -> 'n d =
    let rec go : 'm. ('m, 'n) sub -> idx -> 'm env -> 'n d = fun r i e ->
      match e with
      | ENil -> failwith "unreachable: internal scoping error"
      | EVal(_, x) when i = 0 -> subst r x
      | EVal(e, _) | EDim(e, _) -> go r (i-1) e
      | ESub(e, r') -> go (Sub.compose r r') i e
    in fun i e -> go Sub.id i e
  let lookup_dim : 'n. idx -> 'n env -> 'n dim =
    let rec go : 'm. ('m, 'n) sub -> idx -> 'm env -> 'n dim = fun r i e ->
      match e with
      | ENil -> failwith "unreachable: internal scoping error"
      | EDim(_, d) when i = 0 -> subst_dim r d
      | EVal(e, _) | EDim(e, _) -> go r i e
      | ESub(e, r') -> go (Sub.compose r r') i e
    in fun i e -> go Sub.id i e

  let rec eval : 'n. 'n env -> Core.tm -> 'n d = fun env tm ->
    match tm with
    (* Basics *)
    | Var idx -> lookup_tm idx env
    | Let(x, body) ->
        eval (EVal(env, lazy (eval env x))) body
    | Comp { ty; s; t; partial; cap } ->
        let env' = EDim(ESub(env, Sub.shift_up), DimVar 0) in
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
    | Pi(name, a, b) ->
        DPi { name
            ; a = lazy (eval env a)
            ; b = fun r x -> eval (EVal(ESub(env, r), x)) b }
    | Lam(name, body) ->
        DLam { name; f = fun r x -> eval (EVal(ESub(env, r), x)) body }
    | App(f, x) ->
        let f, x = lazy (eval env f), lazy (eval env x) in
        app f x

    (* Sigma types *)
    | Sigma(name, a, b) ->
        DSigma { name
               ; a = lazy (eval env a)
               ; b = fun r x -> eval (EVal(ESub(env, r), x)) b }
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
        let env' = EDim(ESub(env, Sub.shift_up), DimVar 0) in
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

  and eval_dim : 'n. 'n env -> Core.dim -> 'n dim = fun env d ->
    match d with
    | Zero -> Zero
    | One  -> One
    | DimVar idx -> lookup_dim idx env

  and eval_partial
    : 'n. 'n env -> Core.tm Core.partial -> ('n dl, 'n) partial
    = fun env partial ->
      List.map (fun (i, j, tm) ->
        eval_dim env i, eval_dim env j, lazy (eval env tm)) partial

  and comp
    : 'n. 'n s dl -> 'n dim -> 'n dim -> ('n s dl, 'n) partial -> 'n dl -> 'n d
    = fun ty s t partial cap -> match Lazy.force ty with
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

    | DPi { name; a; b } ->
        let name = if name = "_" then "x" else name in
        DLam { name; f = fun (type m) r (x : m dl) ->
          (* do a buncha substituting *)
          let a: m s dl = lazy (subst (Sub.extend r) a) in
          let s, t = subst_dim r s, subst_dim r t in
          let cap: m dl = lazy (subst r cap) in

          let shift: (m, m s) sub = Sub.shift_up in
          let shift' = Sub.extend shift in
          let fill_x: m s dl = lazy
            (coe (lazy (subst shift' a)) (subst_dim shift s) (DimVar 0)
                 (lazy (subst shift x))) in
          let new_comp_ty = lazy (b (Sub.extend r) fill_x) in
          let new_partial = List.map (fun (i, j, v) ->
            let v: m s dl = lazy (subst (Sub.extend r) v) in
            (subst_dim r i, subst_dim r j, lazy (app v fill_x))) partial in
          let coe_x = lazy (coe a s t x) in
          let new_cap: m dl = lazy (app cap coe_x) in
          comp new_comp_ty s t new_partial new_cap }

    | DSigma { name; a; b } ->
        let first = lazy
          (comp a s t
                (List.map (fun (i, j, x) -> (i, j, lazy (fst x))) partial)
                (lazy (fst cap))) in
        let shift: ('n, 'n s) sub = Sub.shift_up in
        let shift' = Sub.extend shift in
        let first_path : 'n s dl = lazy
          (fill (lazy (subst shift' a)) (subst_dim shift s) (DimVar 0)
                (List.map (fun (i, j, x) ->
                  ( subst_dim shift i
                  , subst_dim shift j
                  , lazy (subst shift' (lazy (fst x))))) partial)
                (lazy (subst shift (lazy (fst cap))))) in
        let second = lazy
          (comp (lazy (b Sub.id first_path)) s t
                (List.map (fun (i, j, x) -> (i, j, lazy (snd x))) partial)
                (lazy (snd cap))) in
        DPair(first, second)

    | DPathTy(a, lhs, rhs) ->
        let shift: ('n, 'n s) sub = Sub.shift_up in
        let shift' = Sub.extend shift in
        let new_ty = lazy (subst shift' a) in

        (* currently: Ψ,i,z ⊢ partial *)
        (* want:      Ψ,z,i ⊢ partial *)
        (* [Ψ,i,z]
              ↓ extend (extend shift_up)
           [ψ,·,i,z]
              ↓ app (DimVar 1)
           [ψ,z,i]
         *)
        let swap: ('n s s, 'n s s) sub =
          Sub.(compose (app (DimVar 1)) (extend shift')) in
        let renamed_partial: ('n s s dl, 'n s) partial =
          List.map (fun (i, j, v) ->
            let v' = lazy (subst swap (lazy (un_dim_abs v))) in
            (subst_dim shift i, subst_dim shift j, v')) partial in
        let new_partial =
          (DimVar 0, Zero, lazy (subst shift' lhs)) ::
          (DimVar 0, One,  lazy (subst shift' rhs)) :: renamed_partial in

        let s, t = subst_dim shift s, subst_dim shift t in
        let new_cap: 'n s dl = lazy (un_dim_abs cap) in

        DDimAbs("i", lazy (comp new_ty s t new_partial new_cap))

    | DU univ_idx -> (* oh no *)
        failwith "TODO"
    | DGlueType { b; t_e } -> (* oh no *)
        failwith "TODO"
    | DLam _ | DPair _ | DDimAbs _ | DGlueTerm _ ->
        failwith "unreachable: type error: not a type"

  (* hcomp is composition at a constant type *)
  and hcomp
    : 'n. 'n dl -> 'n dim -> 'n dim -> ('n s dl, 'n) partial -> 'n dl -> 'n d
    = fun ty s t partial cap ->
    comp (lazy (subst Sub.shift_up ty)) s t partial cap

  (* using fill instead of comp implies that t is a fresh dimension variable *)
  and fill
    : 'n. 'n s dl -> 'n dim -> 'n dim -> ('n s dl, 'n) partial -> 'n dl -> 'n d
    = fun ty -> comp ty

  (* coercion is composition with no partial elements *)
  and coe
    : 'n. 'n s dl -> 'n dim -> 'n dim -> 'n dl -> 'n d
    = fun ty s t cap -> comp ty s t [] cap
end

module Ctx : sig
  open Domain

  exception NotInScope of name

  type 'n t

  val initial_ctx : z t

  val lvl : 'n t -> lvl
  val env : 'n t -> 'n env
  val names : 'n t -> name list
  val lookup_var : 'n t -> name -> idx * 'n dl
  val lookup_dim : 'n t -> name -> idx
  val with_defn : 'n t -> name -> 'n dl -> 'n dl -> 'n t
  val with_var : 'n t -> name -> 'n dl -> 'n dl * 'n t
  val with_dim_var : 'n t -> name -> 'n s dim * 'n s t
  val with_eqn : 'n t -> 'n eqn -> 'n t option
  val entails : 'n t -> 'n eqn -> bool
  val are_cofibs_equal : 'n t -> 'n eqn list -> 'n eqn list -> bool
end = struct
  open Domain

  exception NotInScope of name

  type 'n tys =
    | TNil : 'n tys
    | TVal : 'n tys * 'n dl * name -> 'n tys
    | TDim : 'n tys * name -> 'n tys
    | TSub : 'm tys * ('m, 'n) sub -> 'n tys

  module IntMap = Map.Make (Int)
  type formula = int IntMap.t

  type 'n t =
    { n_dim_vars : int
    ; lvl : lvl
    (* heck *)
    ; names : name list
    ; tys : 'n tys
    ; env : 'n env
    ; formula : formula }

  let find ctx dim =
    let rec go i =
      let p = IntMap.find i ctx.formula in
      if p = i then i else go p in
    go (match dim with
        | Zero -> 0
        | One  -> 1
        | DimVar i -> 1 + ctx.n_dim_vars - i)
  let union ctx d1 d2 =
    let a, b = find ctx d1, find ctx d2 in
    IntMap.add (min a b) (max a b) ctx.formula
  let is_inconsistent ctx =
    find ctx Zero = find ctx One


  let initial_ctx: z t =
    { n_dim_vars = 0
    ; lvl = 0
    ; names = []
    ; tys = TNil
    ; env = ENil
    ; formula = IntMap.empty }

  let lvl (ctx : 'n t) = ctx.lvl
  let env (ctx : 'n t) = ctx.env
  let names (ctx : 'n t) = ctx.names

  let lookup_var (ctx : 'n t) name = 
    let rec go : 'm. int -> ('m, 'n) sub -> 'm tys -> _ =
      fun i r t -> match t with
      | TSub(t, r') -> go i (Sub.compose r r') t
      | TVal(_, t, n) when n = name ->
          i, lazy (subst r t)
      | TVal(t, _, _) | TDim(t, _) -> go (i+1) r t
      | TNil -> raise (NotInScope name) in
    go 0 Sub.id ctx.tys

  let lookup_dim (ctx : 'n t) name =
    let rec go : 't. int -> 't tys -> _ =
      fun i t -> match t with
      | TSub(t, _) -> go i t
      | TDim(_, n) when n = name -> i
      | TDim(t, _) | TVal(t, _, _) -> go (i+1) t
      | TNil -> raise (NotInScope name) in
    go 0 ctx.tys

  let with_defn (ctx : 'n t) name ty x =
    { n_dim_vars = ctx.n_dim_vars
    ; lvl = ctx.lvl + 1
    ; names = name :: ctx.names
    ; tys = TVal(ctx.tys, ty, name)
    ; env = EVal(ctx.env, x)
    ; formula = ctx.formula }

  let with_var (ctx : 'n t) name ty =
    let x = lazy (Eval.reify ty (DVar ctx.lvl)) in
    x, with_defn ctx name ty x

  let with_dim_var (ctx : 'n t) name =
    let x = DimVar 0 in
    x,
    { n_dim_vars = ctx.n_dim_vars + 1
    ; lvl = ctx.lvl + 1
    ; names = name :: ctx.names
    ; tys = TDim(TSub(ctx.tys, Sub.shift_up), name)
    ; env = EDim(ESub(ctx.env, Sub.shift_up), x)
    ; formula = ctx.formula }

  let with_eqn (ctx : 'n t) (x, y) =
    let formula = union ctx x y in
    let ctx' = { ctx with formula } in
    if is_inconsistent ctx' then None else Some ctx'

  let entails (ctx : 'n t) (x, y) =
    find ctx x = find ctx y

  let are_cofibs_equal (ctx : 'n t) a b =
    (* TODO: make sure this does the right thing *)
    let implies x y =
      List.for_all (fun e ->
        match with_eqn ctx e with
        | None -> true
        | Some ctx' -> List.exists (entails ctx') y) x in
    implies a b && implies b a

end

module Pretty : sig
  open Domain

  (* Pretty-printing *)
  val show : 'n Ctx.t -> 'n dl -> 'n dl -> string
end = struct
  open Domain

  (* TODO: pretty-printing *)
  let show (ctx : 'n Ctx.t) ty tm =
    failwith "TODO"
end

module Conv : sig
  open Domain

  exception Mismatch of string * string

  (* Conversion checking *)
  val eq : 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> unit
end = struct
  open Domain

  exception NotEqual
  exception Mismatch of string * string

  (* TODO: conversion checking *)
  let rec conv : 'n. 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> unit =
    fun ctx ty a b ->
    failwith "TODO"


  let eq ctx ty a b =
    try conv ctx ty a b
    with NotEqual ->
      raise (Mismatch(Pretty.show ctx ty a, Pretty.show ctx ty b))
end

module Tychk = struct
  (* open Core *)
  open Domain

  exception TypeError of string

  (* the main check/infer loop! *)
  let rec check : 'n. 'n Ctx.t -> AST.exp -> 'n dl -> Core.tm =
    fun ctx exp ty -> match exp, ty with
    | _ -> failwith "TODO"

  and infer : 'n. 'n Ctx.t -> AST.exp -> 'n dl * Core.tm =
    fun ctx exp -> match exp with
    | _ -> failwith "TODO"

end

(* 
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

  Need to figure out how quantifier elimination works
*)


(* Need type-directed conversion checking! Nasty. *)

(*
Where the Cube Rules run (note: perfectly safe for β rules to take precedence):
  - Kan composition: in eval for comp at a neutral type
  - paths: in reification at path type
  - Glue type: in eval for Glue
  - glue term: in eval for glue
  - unglue term: in eval for unglue of a neutral term
*)

(* TODO: add ⊤/⊥ types, tt : ⊤, abort : ∀ A → ⊥ → A *)

(* Hmmmm, should I make path be pathp, or keep it as path? *)


