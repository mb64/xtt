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
    | Pi of ty * ty binds_one
    | Lam of tm binds_one
    | App of tm * tm
    (* Sigma types *)
    | Sigma of ty * ty binds_one
    | Pair of tm * tm
    | Fst of tm | Snd of tm
    (* Paths *)
    | PathTy of ty * tm * tm
    | PathTm of tm binds_a_dim
    | AppDim of tm * dim
    (* Universes *)
    | U of int
    | GlueType of { b: ty; t_e: tm partial }
    | GlueTerm of tm partial
    (* TODO: how much type info is needed here exactly?
       I think only the function from the equivalence is needed
       But IDK it might be convenient to just throw the whole [α ↦ T,e] in *)
    | Unglue of { equiv_fun: tm partial; x: tm }
  and 'a partial = (dim * dim * 'a) list
end

module Domain = struct
  type lvl = int

  type dim = DZero | DDimVar of lvl | DOne
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
    | DComp of { ty: dne; TODO }
    (* Pi *)
    | DApp of dne * dl
    (* Sigma *)
    | DFst of dne
    | DSnd of dne
    (* Path *)
    | DDimApp of dne * dim
    (* Universes *)
    | DUnglue of dne (* TODO: how much more info is needed? *)

  let abort: dl = lazy (failwith "unreachable: abort")

  type env_item = EVal of dl | EDim of dim
  type env = env_item list

  let app : dl -> dl -> d
  let fst : dl -> d
  let snd : dl -> d
  let dim_app : dl -> dim -> d
  let glue_type : dl partial -> dl -> d
  let glue_term : dl partial -> dl -> d
  let unglue : dl -> d
end

module Ctx : sig
  open Domain

  exception NotInScope of name

  type 'ctx split_on_eqn_result =
    | Yes of 'ctx
    | No of 'ctx
    | Either of { yes: 'ctx; no: 'ctx }

  class type conv_ctx = (* Smaller context used in conversion checking *)
    object
      method lvl : lvl
      method env : env
      method names : name list
      method with_var : name -> dl * conv_ctx
      method with_dim_var : name -> dim * conv_ctx
      method with_eqn : eqn -> conv_ctx option
      method split_on_eqn : eqn -> conv_ctx split_on_eqn_result
    end

  class type elab_ctx = (* Main context used in elaboration *)
    object
      method lvl : lvl
      method env : env
      method conv_ctx : conv_ctx
      method lookup_var : name -> dl * dl
      method lookup_dim : name -> dim
      method with_var  : name -> dl -> dl * elab_ctx
      method with_defn : name -> dl -> dl -> elab_ctx
      method with_dim_var : name -> dim * elab_ctx
      method with_eqn : eqn -> elab_ctx option
    end

  val initial_ctx : elab_ctx
end = struct
  open Domain

  exception NotInScope of name

  (* Type-directed reification *)
  let rec reify (ty: dl) (tm: dne) = match Lazy.force ty with
    | Depends { eqn; yes; no } ->
        Depends { eqn = eqn
                ; yes = lazy (reify yes tm)
                ; no  = lazy (reify no  tm) }
    | DNe _ -> DNe tm
    | DPi(name, a, b) ->
        let name = if name = "_" then "x" else name in
        DLam(name, fun x -> reify (apply ty x) (DNe (DApp(tm, x))))
    | DSigma(name, a, b) ->
        let fst = lazy (reify a (DFst tm)) in
        DPair(fst, lazy (reify (b fst) (DSnd tm)))
    | DPathTy(a, lhs, rhs) ->
        DDimAbs("i", fun dim ->
          Depends
            { eqn = dim, Zero
            ; yes = lhs
            ; no  = lazy (Depends
                { eqn = dim, One
                ; yes = rhs
                ; no  = lazy (reify a (DDimApp(tm, dim))) }) }
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
    | DLam _ | DPair _ | DPathTm _ | DGlueTerm _  ->
        failwith "unreachable: not a type"

  module IntMap = Map.Make (Int)
  type formula = int IntMap.t

  let idx_of_dim = function Zero -> 0 | One -> 1 | DimVar x -> 2 + x

  class conv_ctx lvl env names formula diseq =
    object
      method lvl : lvl = lvl
      method env : env = env
      method names : name list = names
      method with_var name =
        let var = reify 
        let ctx' = new conv_ctx (lvl+1) (name::names) formula diseq in






  (* TODO: a ctx class *)
  (* It should have as methods:
     lookup_dim
     lookup_var
     with_dim_var
     with_eqn
     with_var
     with_defn
   *)
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
  - kan composition: in eval for comp at a neutral type
  - paths: in reification at path type
  - Glue type: in eval for Glue
  - glue term: in eval for glue
  - unglue term: in eval for unglue of a neutral term

*)



(* TODO: add ⊤/⊥ types, tt : ⊤, abort : ∀ A → ⊥ → A *)




module Typechecker = struct
  open Core


