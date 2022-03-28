type name = string

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
  type lvl = int and idx = int

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
    (* TODO: how much type info is needed here exactly?
       I think only the function from the equivalence is needed
       But IDK it might be convenient to just throw the whole [α ↦ T,e] in *)
    | Unglue of { equiv_fun: tm partial; x: tm }
  and 'a partial = (dim * dim * 'a) list
end

module Domain = struct
  type lvl = int

  type dim = Zero | DimVar of lvl | One
  type eqn = dim * dim
  type 'a partial = (dim * dim * 'a) list

  (* the semantic domain (?) *)
  and dl = d Lazy.t
  and d =
    (* Basics: neutrals, things that depend on intervals *)
    | Depends of { eqn: eqn; yes: dl; no: dl }
    | DNe of dne
    (* Pi types *)
    | DPi of name * dl * (dl -> d)
    | DLam of name * (dl -> d)
    (* Sigma types *)
    | DSigma of name * dl * (dl -> d)
    | DPair of dl * dl
    (* Paths *)
    | DPathTy of dl * dl * dl
    | DDimAbs of name * (dim -> d)
    (* Universes *)
    | DU of int
    | DGlueType of { b: dl; t_e: dl partial }
    | DGlueTerm of { a: dl partial; b: dl }
  and dne =
    (* Basics *)
    | DVar of lvl
    (* | DComp of { ty: dne; TODO } *)
    (* Pi *)
    | DApp of dne * dl
    (* Sigma *)
    | DFst of dne
    | DSnd of dne
    (* Path *)
    | DDimApp of dne * dim
    (* Universes *)
    | DUnglue of dne (* TODO: how much more info is needed? *)

  type env_item = EVal of dl | EDim of dim
  type env = env_item list

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

  (* TODO: figure this out *)
  (* Should it take the whole equivalence as an arg? Just the function? *)
  (* val unglue : dl -> d *)

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

  let app f x =
    let* DLam(_, fn) = f in fn x
  let fst x =
    let* DPair(a, _) = x in Lazy.force a
  let snd x =
    let* DPair(_, b) = x in Lazy.force b
  let dim_app p d =
    let* DDimAbs(_, fn) = p in fn d
  let glue_type b t_e =
    failwith "TODO"
  let glue_term a b = failwith "TODO"
  let unglue x = failwith "TODO"

  (* Type-directed reification *)
  let rec reify (ty: dl) (tm: dne) = match Lazy.force ty with
    | Depends { eqn; yes; no } ->
        Depends { eqn = eqn
                ; yes = lazy (reify yes tm)
                ; no  = lazy (reify no  tm) }
    | DNe _ -> DNe tm
    | DPi(name, a, b) ->
        let name = if name = "_" then "x" else name in
        DLam(name, fun x -> reify (lazy (app ty x)) (DApp(tm, x)))
    | DSigma(name, a, b) ->
        let fst = lazy (reify a (DFst tm)) in
        DPair(fst, lazy (reify (lazy (b fst)) (DSnd tm)))
    | DPathTy(a, lhs, rhs) ->
        DDimAbs("i", fun dim ->
          Depends
            { eqn = dim, Zero
            ; yes = lhs
            ; no  = lazy (Depends
                { eqn = dim, One
                ; yes = rhs
                ; no  = lazy (reify a (DDimApp(tm, dim))) }) })
    | DU _ -> DNe tm
    | DGlueType { b; t_e } ->
        (* when ty = Glue b [α ↦ t], then tm should be
           glue [α ↦ reify t tm] (unglue g)
           Depends(α, reify (fst t) tm, Glue tm)
        TODO figure this out.
        Don't call GlueTerm directly, use the glue helper function (?)
         *)
        failwith "TODO"
    | DGlueTerm _ ->
        (* ty : Glue [α ↦ ...] ... is only a type when α holds *)
        (* when ty = glue [α ↦ t₁ | β ↦ t₂] (b), then tm should be
           Depends(α, reify t₁ tm,
           Depends(β, reify t₂ tm, lazy (failwith "unreachable: not a type"))
        *)
        failwith "TODO"
    | DLam _ | DPair _ | DDimAbs _ ->
        failwith "unreachable: not a type"

  let rec eval (env : env) (tm : Core.tm) = match tm with
    (* Basics *)
    | Var idx -> begin match List.nth env idx with
        | EVal v -> Lazy.force v
        | _ -> failwith "unreachable: internal scoping error"
      end
    | Let(x, body) ->
        eval (EVal (lazy (eval env x))::env) body
    | Comp { ty; s; t; partial; cap } ->
        let ty = eval env ty in
        let s, t = eval_dim env s, eval_dim env t in
        let partial = eval_partial env partial in
        let cap = lazy (eval env cap) in
        comp ty s t partial cap
    | Abort ->
        failwith "unreachable: abort"

    (* Pi types *)
    | Pi(n, a, b) ->
        DPi(n, lazy (eval env a), fun x -> eval (EVal x::env) b)
    | Lam(n, body) ->
        DLam(n, fun x -> eval (EVal x::env) body)
    | App(f, x) ->
        let f, x = lazy (eval env f), lazy (eval env x) in
        app f x

    (* Sigma types *)
    | Sigma(n, a, b) ->
        DSigma(n, lazy (eval env a), fun x -> eval (EVal x::env) b)
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
        DDimAbs(n, fun d -> eval (EDim d::env) tm)
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
    | Unglue { equiv_fun; x } ->
        let equiv_fun = eval_partial env equiv_fun in
        let x = lazy (eval env x) in
        failwith "TODO"

  and eval_dim env (d : Core.dim) = match d with
    | Zero -> Zero
    | One  -> One
    | DimVar idx -> match List.nth env idx with
        | EDim d -> d
        | _ -> failwith "unreachable: internal scoping error"

  and eval_partial env (partial : Core.tm Core.partial) =
    List.map (fun (i, j, tm) ->
      eval_dim env i, eval_dim env j, lazy (eval env tm)) partial

  and comp ty s t partial cap =
    (* match on ty *)
    failwith "TODO"
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
        let rec go ns ts es = match ns, ts, es with
          | n::_, Some t::_, EVal e::_ when n = name -> t, e
          | _::ns, _::ts, _::es -> go ns ts es
          | [], [], [] -> raise (NotInScope name)
          | _ -> failwith "unreachable" in
        go names tys env
      method lookup_dim name =
        let rec go ns es = match ns, es with
          | n::_, EDim e::_ when n = name -> e
          | [], [] -> raise (NotInScope name)
          | _ -> failwith "unreachable" in
        go names env

      method with_defn name ty x =
        let ctx' = new ctx (lvl+1)
          (name::names) (Some ty::tys) (EVal x::env)
          formula diseq in
        ctx'
      method with_var name ty =
        let x = lazy (Eval.reify ty (DVar lvl)) in
        x, self#with_defn name ty x
      method with_dim_var name =
        let x = DimVar lvl in
        let ctx' = new ctx (lvl+1)
          (name::names) (None::tys) (EDim x::env)
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
    new ctx 0 [] [] [] IntMap.(add 0 0 (singleton 1 1)) [Zero, One]
end

module Pretty : sig
  open Domain

  val show : Ctx.ctx -> dl -> dl -> string
end = struct
  (* TODO: pretty-printing *)
end

module Conv : sig
  open Domain

  val eq : Ctx.ctx -> dl -> dl -> dl -> bool
end = struct
  open Domain

  exception NotEqual

  let rec conv (ctx : Ctx.ctx) (ty : dl) (a : dl) (b : dl) =
    failwith "TODO"


  

end

module Tychk = struct
  open Core
  open Domain

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




module Typechecker = struct
  open Core


