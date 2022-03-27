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
    | DimAbs of name * exp
    | DimApp of exp * dim
    (* Universes: U_i, Glue B [α ↦ T,e], glue [α ↦ t] b, unglue B [α ↦ T,e] x *)
    | U of int
    | GlueType of { b: ty; t_e: partial }
    | GlueTerm of { a: partial; b: exp }
    | Unglue of { b: ty; t_e: partial; x: exp }
  and partial = (cofib * exp) list
  and dim = Zero | DimVar of name | One
  and cofib = Eq of dim * dim | Disj of cofib * cofib
end

module Core = struct
  type lvl = int and idx = int

  (* Just comments *)
  type 'a binds_one = 'a
  type 'a binds_a_dim = 'a

  type dim = Zero | DimVar of idx | One
  and cofib = (dim * dim) list
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
  and 'a partial = (cofib * 'a) list
end

module type CUBE = sig
  type var  (* Interval variables i, j *)
  type dim = Zero | Var of var | One (* Dimensions i, j, 0, 1 *)
  type cofib (* Cofibrations (constraints) α *)
  type ctx (* The dimension context and formula Ψ ; φ *)

  val nah : cofib (* = (0 = 1) *)
  val eq : dim -> dim -> cofib
  val disj : cofib -> cofib -> cofib
  val forall : (var -> cofib) -> cofib

  exception NotInScope of name

  val empty_ctx : ctx
  val lookup_var : ctx -> name -> var
  val with_new_var : ctx -> name -> var * ctx
  val with_cofib : ctx -> cofib -> ctx

  val entails : ctx -> cofib -> bool
  val is_borked : ctx -> bool (* = entails (0 = 1) *)

  val are_dims_equal   : ctx -> dim -> dim -> bool
  val are_cofibs_equal : ctx -> cofib -> cofib -> bool
end

module Cube : CUBE = struct
  type var = int
  type dim = Zero | Var of var | One
  type cofib = (dim * dim) list (* a disjunction of equations *)
  type ctx =
    { next_var: var
    ; names: name list
    ; formula: cofib list (* a conjunction of clauses *) }

  let nah: cofib = []
  let eq a b: cofib = [a, b]
  let disj = (@)
  let forall f = failwith "heck how do I implement this. some kinda quantifier elimination?"

  exception NotInScope of name

  let empty_ctx: ctx = { next_var = 0; names = []; formula = [] }
  let lookup_var (ctx: ctx) name =
    let rec go v = function
      | [] -> raise (NotInScope name)
      | n::_ when n = name -> v
      | _::rest -> go (v-1) rest in
    go (ctx.next_var - 1) ctx.names
  let with_new_var (ctx: ctx) name =
    ctx.next_var,
    { ctx with next_var = ctx.next_var + 1; names = name :: ctx.names }
  let with_cofib (ctx: ctx) cofib =
    { ctx with formula = cofib :: ctx.formula }

  let entails (ctx: ctx) cofib =
    (* Check that ctx.formula and not(cofib) is unsat *)
    let parents = Array.make (ctx.next_var + 2) (-1) in
    let idx_of_dim = function Zero -> 0 | One -> 1 | Var i -> 2 + i in
    let rec find i =
      let p = parents.(i) in
      if p = -1 then i else let x = find p in parents.(i) <- x; x in
    let find_dim d = find (idx_of_dim d) in
    let union_dim (x, y) = parents.(find_dim x) <- find_dim y in
    let rec is_unsat eqs = function
      | [] ->
          Array.fill parents 0 (Array.length parents) (-1);
          List.iter union_dim eqs;
          List.exists (fun (x,y) -> find_dim x = find_dim y) ((Zero,One)::cofib)
      | c::cs -> List.for_all (fun eq -> is_unsat (eq::eqs) cs) c in
    is_unsat [] ctx.formula
  let is_borked ctx = entails ctx nah

  let are_dims_equal ctx x y = entails ctx (eq x y)
  let are_cofibs_equal ctx x y =
    entails (with_cofib ctx x) y && entails (with_cofib ctx y) x
end

module Domain = struct
  (* the semantic domain (?) *)
  type dl = d Lazy.t
  and d =
    (* Basics: neutrals *)
    | DNe of dne
    (* Pi types *)
    | DPi of dl * (dl -> d)
    | DLam of (dl -> d)
    (* Sigma types *)
    | DSigma of dl * (dl -> d)
    | DPair of dl * dl
    (* Paths *)
    | DPathTy of dl * dl * dl
    | DPathTm of (Cube.dim -> d)
    (* Universes *)
    | DU of int
    | DGlueType of ...
    | DGlueTerm of ...
  (* ugh this is not great. it's not stable under cube context extension!
     how to make it stable under cube context extension?
     or is it just hopeless?
     - partial elements are fine (?) are they?
     - Unglue! It is like a neutral term
   *)
  (* neutral terms, i hope *)
  and dne =
    | DVar of lvl
    | DApp of dne * dl
    | DFst of dne
    | DSnd of dne
    | DUnglue

module Typechecker = struct
  open Core


  (* type ctx = { ctx } *)

  (* val force : d *)


