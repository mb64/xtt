(* Aaaaaaa we're tryin' XTT *)

type name = string
type idx = int and lvl = int

module AST = struct
  type ty = exp
  and dim = exp
  and exp =
    | Var of name
    | Let of name * exp * exp
    | Annot of exp * ty
    | Coe of { r: dim; r': dim; i: name; ty: ty; a: exp }
    | Com of { s: dim; r: dim; r': dim
             ; i: name; ty: ty
             ; lhs: exp; rhs: exp; a: exp }
    | Zero | One
    (* Set and weird typecase stuff *)
    | Set (* Set : Set lol *)
    | DomTy of exp
    | CodTy of exp
    | PathPTyLhs of exp
    | PathPTyRhs of exp
    | PathPTyPath of exp
    | PathPLhs of exp
    | PathPRhs of exp
    (* Functions *)
    | Pi of name * ty * ty
    | PathP of name * ty * exp * exp
    | Lam of name * exp
    | App of exp * exp
    (* (1* Pairs *1) *)
    (* | Sigma of name * ty * ty *)
    (* | Pair of exp * exp *)
    (* | Fst of exp *)
    (* | Snd of exp *)
    (* | FstTy of exp *)
    (* | SndTy of exp *)
end

module Core = struct
  type 'a binds = 'a

  type dim = Zero | DimVar of idx | One
  type ty = tm
  and tm =
    | Var of idx
    | Let of name * tm * tm binds
    | Coe of dim * dim * name * ty binds * tm
    | Com of { s: dim; r: dim; r': dim
             ; i: name; ty: ty binds
             ; lhs: tm binds; rhs: tm binds }
    | HCom of { s: dim; r': dim; i: name; lhs: tm binds; rhs: tm binds }
    (* Set *)
    | Set
    | DomTy of tm
    | CodTy of tm
    | PathPTyLhs of tm
    | PathPTyRhs of tm
    | PathPTyPath of tm
    | PathPLhs of tm
    | PathPRhs of tm
    (* Functions *)
    | Pi of name * ty * ty binds
    | Lam of name * tm binds
    | App of tm * tm
    (* Paths *)
    | PathP of name * ty binds * tm * tm
    | DimAbs of name * tm binds
    | DimApp of tm * dim
end

module Domain = struct
  type 'n dim = Zero | DimVar of (* n *) idx | One 

  module TypeNats : sig
    type z
    type 'n s
  end = struct type z = unit and 'n s = unit end
  include TypeNats

  type 'n cond =
    | DimEq of 'n dim * 'n dim
    | TyEq of 'n dne * 'n dne
    | Forall_i of 'n s cond

  and 'n dl = 'n d lazy_t
  and 'n d =
    | DNe of 'n dne
    | DSplit of 'n dim * 'n dl * 'n dl
    | DIf of { cond: 'n cond; yes: 'n dl; no: 'n dl } (* unstable elements *)
    | DSet
    | DPi of 'n dl * 'n clos
    | DLam of 'n clos
    | DPathP of name * 'n s dl * 'n dl * 'n dl
    | DDimAbs of name * 'n s dl
    (* | DSigma of 'n dl * 'n clos *)
    (* | DPair of 'n dl * 'n dl *)

  and 'n dne =
    | DVar of lvl * 'n dl
    | DApp of 'n dne * 'n dl
    | DCoe of { r: 'n dim; r': 'n dim
              (* invariant: ty0 ≠ ty1 (or else it would compute) *)
              ; ty0: 'n dl; ty1: 'n dl
              ; a: 'n dl }
    (* | DFst of 'n dne *)
    (* | DSnd of 'n dne *)

  and 'n env_item =
    | Dim of 'n dim
    | Val of 'n dl
  and 'n env = 'n env_item list

  and 'n clos = { name: name; env: 'n env; body: Core.tm }

  module Sub : sig
    type ('n, 'm) sub

    val id : ('n, 'n) sub
    val compose : ('m, 'l) sub -> ('n, 'm) sub -> ('n, 'l) sub

    val shift_up : ('n, 'n s) sub
    val app : 'n dim -> ('n s, 'n) sub
    val extend : ('n, 'm) sub -> ('n s, 'm s) sub

    val dim  : ('n, 'm) sub -> 'n dim  -> 'm dim
    val d    : ('n, 'm) sub -> 'n d    -> 'm d
    val dl   : ('n, 'm) sub -> 'n dl   -> 'm dl
    val dne  : ('n, 'm) sub -> 'n dne  -> 'm dne
    val cond : ('n, 'm) sub -> 'n cond -> 'm cond
    val clos : ('n, 'm) sub -> 'n clos -> 'm clos
    val env  : ('n, 'm) sub -> 'n env  -> 'm env
    val env_item : ('n, 'm) sub -> 'n env_item -> 'm env_item
  end = struct
    type ('n, 'm) sub = idx -> 'm dim

    let dim s = function
      | Zero -> Zero
      | One  -> One
      | DimVar i -> s i

    let id x = DimVar x
    let compose s s' i = dim s (s' i)

    let shift_up i = DimVar (i+1)
    let app x i = if i = 0 then x else DimVar(i-1)
    let extend s i =
      if i = 0 then DimVar 0 else dim shift_up (s (i-1))

    let rec d : 'n 'm. ('n, 'm) sub -> 'n d -> 'm d
      = fun s tm -> match tm with
      | DNe ne -> DNe (dne s ne)
      | DIf { cond = c; yes; no } ->
          DIf { cond = cond s c; yes = dl s yes; no = dl s no }
      | DSplit(i, l, r) ->
          DSplit(dim s i, dl s l, dl s r)
      | DSet -> DSet
      | DPi(a, b) ->
          DPi(dl s a, clos s b)
      | DLam f ->
          DLam (clos s f)
      | DPathP(i, ty, lhs, rhs) ->
          DPathP(i, dl (extend s) ty, dl s lhs, dl s rhs)
      | DDimAbs(i, body) ->
          DDimAbs(i, dl (extend s) body)

    and dl : 'n 'm. ('n, 'm) sub -> 'n dl -> 'm dl
      = fun s dl -> Lazy.map (d s) dl

    and dne : 'n 'm. ('n, 'm) sub -> 'n dne -> 'm dne
      = fun s ne -> match ne with
      | DVar(lvl, ty) -> DVar(lvl, dl s ty)
      | DApp(f, x) -> DApp(dne s f, dl s x)
      | DCoe { r; r'; ty0; ty1; a } ->
          DCoe { r = dim s r; r' = dim s r'
               ; ty0 = dl s ty0; ty1 = dl s ty1
               ; a = dl s a }

    and cond : 'n 'm. ('n, 'm) sub -> 'n cond -> 'm cond
      = fun s c -> match c with
      | DimEq(i, j) -> DimEq(dim s i, dim s j)
      | TyEq(a, b) -> TyEq(dne s a, dne s b)
      | Forall_i c -> Forall_i (cond (extend s) c)
    
    and env_item : 'n 'm. ('n, 'm) sub -> 'n env_item -> 'm env_item
      = fun s i -> match i with
      | Dim d -> Dim (dim s d)
      | Val v -> Val (dl s v)

    and env : 'n 'm. ('n, 'm) sub -> 'n env -> 'm env
      = fun s env -> List.map (env_item s) env

    and clos : 'n 'm. ('n, 'm) sub -> 'n clos -> 'm clos
      = fun s c -> { name = c.name; env = env s c.env; body = c.body }
  end

  type ('n, 'm) sub = ('n, 'm) Sub.sub

end

module Eval : sig
  open Domain

  val ($) : 'n clos -> 'n dl -> 'n d

  val type_of_ne : 'n dne -> 'n d

  val app : 'n dl -> 'n dl -> 'n d
  val dim_app : 'n dl -> 'n dim -> 'n d
  (* val fst : 'n dl -> 'n d *)
  (* val snd : 'n dl -> 'n d *)

  val un_dim_abs : 'n dl -> 'n s d

  val eval : 'n env -> Core.tm -> 'n d
end = struct
  open Domain

  let bind_with_sub : 'n 'm. ('n, 'm) sub -> 'n d -> ('n d -> 'm d) -> 'm d
    = fun s x f ->
    let rec go = function
      | DIf { cond; yes; no } ->
          DIf { cond = Sub.cond s cond
              ; yes = Lazy.map go yes
              ; no = Lazy.map go no }
      | DSplit(dim, l, r) ->
          DSplit(Sub.dim s dim, Lazy.map go l, Lazy.map go r)
      | x -> f x in
    go x
  let bind x f = bind_with_sub Sub.id x f

  let bind_shift_down : 'n. 'n s d -> ('n s d -> 'n d) -> 'n d
    = fun x f ->
    let rec go = function
      | DIf { cond; yes; no } ->
          DIf { cond = Forall_i cond
              ; yes = Lazy.map go yes
              ; no = Lazy.map go no }
      | DSplit(Zero, l, r) -> go (Lazy.force l) (* lol *)
      | DSplit(One, l, r) -> go (Lazy.force r) (* lol *)
      | DSplit(DimVar 0, l, r) as x -> f x
      | DSplit(DimVar n, l, r) ->
          DSplit(DimVar (n-1), Lazy.map go l, Lazy.map go r)
      | x -> f x in
    go x

  let rec ($) : 'n. 'n clos -> 'n dl -> 'n d
    = fun clos x -> eval (Val x::clos.env) clos.body

  and type_of_ne : 'n. 'n dne -> 'n d = function
    | DVar(_, ty) -> Lazy.force ty
    | DApp(f, x) -> begin
        match type_of_ne f with
        | DPi(_, b) -> b $ x
        | _ -> failwith "internal type error"
        end
    | DCoe { r'; ty0; ty1; _ } ->
        DSplit(r', ty0, ty1)

  and app : 'n. 'n dl -> 'n dl -> 'n d
    = fun f x -> bind (Lazy.force f) (function
      | DLam f -> f $ x
      | DNe f -> DNe (DApp(f, x))
      | _ -> failwith "internal type error")

  and dim_app : 'n. 'n dl -> 'n dim -> 'n d
    = fun f i -> bind (Lazy.force f) (function
      | DDimAbs(_, x) -> Sub.d (Sub.app i) (Lazy.force x)
      | DNe ne -> begin
          match type_of_ne ne with
          | DPathP(_, _, l, r) ->
              DSplit(i, l, r)
          | _ -> failwith "internal type error"
          end
      | _ -> failwith "internal type error")

  and un_dim_abs : 'n. 'n dl -> 'n s d
    = fun x -> match Lazy.force x with
    | DIf { cond; yes; no } ->
        DIf { cond = Sub.cond Sub.shift_up cond
            ; yes = lazy (un_dim_abs yes)
            ; no  = lazy (un_dim_abs no) }
    | DSplit(dim, l, r) ->
        DSplit(Sub.dim Sub.shift_up dim
              , lazy (un_dim_abs l)
              , lazy (un_dim_abs r))
    | DDimAbs(_, x) -> Lazy.force x
    | DNe ne -> begin
        match type_of_ne ne with
        | DPathP(_, _, l, r) ->
            DSplit(DimVar 0, Sub.dl Sub.shift_up l, Sub.dl Sub.shift_up r)
        | _ -> failwith "internal type error"
        end
    | _ -> failwith "internal type error"

  and eval : 'n. 'n env -> Core.tm -> 'n d
    = fun env tm -> match tm with
    | Var idx -> begin
        match List.nth env idx with
        | Val v -> Lazy.force v
        | Dim _ -> failwith "internal scoping error"
        end
    | Let(_, x, body) ->
        eval (Val (lazy (eval env x))::env) body
    | Coe(r, r', i, ty, a) ->
        failwith "TODO"
    | Com { s; r; r'; i; ty; lhs; rhs } ->
        failwith "TODO"
    | HCom { s; r'; i; lhs; rhs } ->
        failwith "TODO"
    | Set -> DSet
    | DomTy x -> failwith "TODO"
    | CodTy x -> failwith "TODO"
    | PathPTyLhs x -> failwith "TODO"
    | PathPTyRhs x -> failwith "TODO"
    | PathPTyPath x -> failwith "TODO"
    | PathPLhs x -> failwith "TODO"
    | PathPRhs x -> failwith "TODO"
    | Pi(name, a, b) ->
        DPi(lazy (eval env a), { name; env; body = b})
    | Lam(name, body) ->
        DLam { name; env; body }
    | App(f, x) ->
        app (lazy (eval env f)) (lazy (eval env x))
    | PathP(name, ty, lhs, rhs) ->
        let env' = Dim (DimVar 0) :: Sub.env Sub.shift_up env in
        DPathP( name
              , lazy (eval env' ty)
              , lazy (eval env lhs)
              , lazy (eval env rhs))
    | DimAbs(name, body) ->
        let env' = Dim (DimVar 0) :: Sub.env Sub.shift_up env in
        DDimAbs(name, lazy (eval env' body))
    | DimApp(p, i) ->
        dim_app (lazy (eval env p)) (eval_dim env i)

  and eval_dim : 'n. 'n env -> Core.dim -> 'n dim
    = fun env d -> match d with
    | Zero -> Zero
    | One  -> One
    | DimVar idx ->
        match List.nth env idx with
        | Dim d -> d
        | Val _ -> failwith "internal scoping error"

end

module Ctx : sig
  open Domain

  exception NotInScope of name
  exception GotDimWantedVal
  exception GotValWantedDim

  type 'n t

  val initial_ctx : z t

  (* The length of the term context Γ and its names *)
  val lvl : 'n t -> lvl
  val tm_names : 'n t -> name list

  (* The length of the dimension context Ψ is 'n, and these are its names *)
  val dim_names : 'n t -> name list

  val env : 'n t -> 'n env
  val lookup_var : 'n t -> name -> idx * 'n dl
  val lookup_dim : 'n t -> name -> idx
  val with_defn : 'n t -> name -> 'n dl -> 'n dl -> 'n t
  val with_var : 'n t -> name -> 'n dl -> 'n dl * 'n t
  val with_dim_var : 'n t -> name -> 'n s dim * 'n s t
  val with_eqn : 'n t -> 'n dim -> 'n dim -> 'n t option
  val are_dims_eq : 'n t -> 'n dim -> 'n dim -> bool
end = struct
  open Domain

  exception NotInScope of name
  exception GotDimWantedVal
  exception GotValWantedDim

  module DisjSets = struct
    module IntMap = Map.Make (Int)
    include IntMap
    type t = int IntMap.t

    let rec find i m =
      let p = IntMap.find i m in
      if p = i then i else find p m
    let union i j m =
      let i, j = find i m, find j m in
      IntMap.add i j m
  end
  
  type 'n t =
    { lvl: int
    ; tm_names: name list
    ; dim_count: int
    ; dim_names: name list
    ; env: 'n env
    ; tys: (name * 'n env_item) list
    ; formula: DisjSets.t }

  let initial_ctx =
    { lvl = 0
    ; tm_names = []
    ; dim_count = 0
    ; dim_names = []
    ; env = []
    ; tys = []
    ; formula = DisjSets.empty }

  let lvl ctx = ctx.lvl
  let tm_names ctx = ctx.tm_names
  let dim_names ctx = ctx.dim_names

  let env ctx = ctx.env

  let lookup_helper ctx name =
    let rec go i = function
      | [] -> raise (NotInScope name)
      | (n,x)::_ when n = name -> i, x
      | _::rest -> go (i+1) rest in
    go 0 ctx.tys

  let lookup_var ctx name = match lookup_helper ctx name with
    | i, Val ty -> i, ty
    | _, Dim _ -> raise GotDimWantedVal

  let lookup_dim ctx name = match lookup_helper ctx name with
    | i, Dim _ -> i
    | _, Val _ -> raise GotValWantedDim

  let with_defn ctx name ty value =
    { lvl = 1 + ctx.lvl
    ; tm_names = name :: ctx.tm_names
    ; dim_count = ctx.dim_count
    ; dim_names = ctx.dim_names
    ; env = Val value :: ctx.env
    ; tys = (name, Val ty) :: ctx.tys
    ; formula = ctx.formula }

  let with_var ctx name ty =
    let value = lazy (DNe (DVar(ctx.lvl, ty))) in
    value, with_defn ctx name ty value

  let dim_to_id ctx = function
    | Zero -> 0
    | One  -> 1
    | DimVar idx -> 2 + ctx.dim_count - idx - 1

  let with_dim_var ctx name =
    let i = DimVar 0 in
    let id = 2 + ctx.dim_count in
    i, { lvl = ctx.lvl
    ; tm_names = ctx.tm_names
    ; dim_count = 1 + ctx.dim_count
    ; dim_names = name :: ctx.dim_names
    ; env = Dim i :: Sub.env Sub.shift_up ctx.env
    ; tys = (name, Dim i)
        :: List.map (fun (n, it) -> n, Sub.env_item Sub.shift_up it) ctx.tys
    ; formula = DisjSets.add id id ctx.formula }

  let is_consistent formula =
    DisjSets.find 0 formula <> DisjSets.find 1 formula

  let with_eqn ctx i j =
    let i_id, j_id = dim_to_id ctx i, dim_to_id ctx j in
    let formula' = DisjSets.union i_id j_id ctx.formula in
    if is_consistent formula' then
      Some { ctx with formula = formula' }
    else
      None

  let are_dims_eq ctx i j =
    let i_id, j_id = dim_to_id ctx i, dim_to_id ctx j in
    DisjSets.find i_id ctx.formula = DisjSets.find j_id ctx.formula
end

module Pretty : sig
  open Domain

  val show : 'n Ctx.t -> 'n dl -> 'n dl -> string
end = struct
  open Domain

  (* TODO *)
  let show ctx ty x = failwith "TODO"
end

module Conv : sig
  open Domain
  
  val force : 'n Ctx.t -> 'n dl -> 'n d

  (* Conversion checking *)
  val eq : 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> bool

  (* Subtype checking *)
  val sub : 'n Ctx.t -> 'n dl -> 'n dl -> bool

  (* Same thing but it throws an exception if not *)
  exception Mismatch of string * string

  val check_eq : 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> unit
  val check_sub : 'n Ctx.t -> 'n dl -> 'n dl -> unit
end = struct
  open Domain
  
  exception Mismatch of string * string

  let rec force : 'n. 'n Ctx.t -> 'n dl -> 'n d
    = fun ctx x -> match Lazy.force x with
    | DIf { cond; yes; no } ->
        force ctx (if is_cond_true ctx cond then yes else no)
    | DSplit(dim, l, r) -> begin
        if Ctx.are_dims_eq ctx dim Zero then
          force ctx l
        else if Ctx.are_dims_eq ctx dim One then
          force ctx r
        else match force ctx l, force ctx r with
          | DNe l, DNe r when eq_ne ctx l r -> DNe l
          | DSet, DSet -> DSet
          | DPi(al, bl), DPi(ar, br) ->
              let b = failwith "TODO" in
              DPi(lazy (DSplit(dim, al, ar)), b)
          | DPathP(i, lty, llhs, lrhs), DPathP(_, rty, rlhs, rrhs) ->
              DPathP( i
                    , lazy (DSplit(Sub.dim Sub.shift_up dim, lty, rty))
                    , lazy (DSplit(dim, llhs, rlhs))
                    , lazy (DSplit(dim, lrhs, rrhs)))
          | l, r -> DSplit(dim, lazy l, lazy r)
        end
    | x -> x

  and is_cond_true : 'n. 'n Ctx.t -> 'n cond -> bool
    = fun ctx cond -> match cond with
    | DimEq(i, j) -> Ctx.are_dims_eq ctx i j
    | TyEq(x, y) -> eq_ne ctx x y
    | Forall_i cond ->
        let _i, ctx' = Ctx.with_dim_var ctx "i" in
        is_cond_true ctx' cond

  and eq_ne : 'n. 'n Ctx.t -> 'n dne -> 'n dne -> bool
    = fun ctx a b -> Option.is_some (conv_ne ctx a b)

  and conv_ne : 'n. 'n Ctx.t -> 'n dne -> 'n dne -> 'n dl option
    = fun ctx a b -> failwith "TODO"

  and eq : 'n. 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> bool
    = fun ctx ty a b -> failwith "TODO"

  (* TODO *)
end


(*

How to coe r r' (i.A) a: (force A and) match A with
  | Π(x:A) → B  ⇒  (...) (bottom of p.14)
  | Σ(x:A) × B  ⇒  (...)
  | Path A x y  ⇒  (...)
  | Bool        ⇒  a
  | Set         ⇒  a
  | i ? l : r   ⇒  ??? (some kinda neutral term; BUT ALSO cube rules)
  | neutral     ⇒  ??? (some kinda neutral term; BUT ALSO cube rules)

Special rules for coe:
  when r = r', coe is identity
    ⇒ DIf (Eq r r') a (neutral term)
  REGULARITY: when i,j ⊢ A(i) = A(j), coe is identity
    ⇒ DIf (IsEq A(0) A(1)) a (neutral term)

How to com<s> r r' (i.A) i.lhs i.rhs a:
  hcom<s> r r' A(r')
    i.(coe i r' (i.A) lhs)
    i.(coe i r' (i.A) rhs)
    (coe r r' (i.A) a)

How to hcom<s> r r' A i.lhs i.rhs a:
  All that matters is the boundary behavior!
  Just return DSplit s lhs(r') rhs(r')
  Lmao

→ I think XTT satisfies canonicity but not normalization
→ so I shouldn't bother to put unnecessary-for-computation things in the core
  language, lol
→ definitional UIP is one helluva drug


*)




