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
    (* coe r r' i.A a *)
    | Coe of { r: dim; r': dim; i: name; ty: ty; a: exp }
    (* com<s> r r' i.A i.lhs i.rhs a *)
    | Com of { s: dim; r: dim; r': dim
             ; ty: name * ty
             ; lhs: name * exp; rhs: name * exp; a: exp }
    (* TODO: hcom *)
    | Zero | One
    (* Set and weird injectivity stuff *)
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
    (* pathp i.A lhs rhs *)
    | PathP of name * ty * exp * exp
    (* lhs ≡ rhs *)
    | Eq of exp * exp
    | Lam of name * exp
    | App of exp * exp
    (* Pairs *)
    | Sigma of name * ty * ty
    | Pair of exp * exp
    | Fst of exp
    | Snd of exp
    | FstTy of exp
    | SndTy of exp
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
    | Abort
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
    | TyEq of 'n dl * 'n dl
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
      | TyEq(a, b) -> TyEq(dl s a, dl s b)
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

  val dom_ty : 'n d -> 'n d
  val cod_ty : 'n d -> 'n d
  val pathp_ty_lhs : 'n d -> 'n d
  val pathp_ty_rhs : 'n d -> 'n d
  val pathp_ty_path : 'n d -> 'n d
  val pathp_lhs : 'n d -> 'n d
  val pathp_rhs : 'n d -> 'n d

  val eval : 'n env -> Core.tm -> 'n d
  val eval_dim : 'n env -> Core.dim -> 'n dim
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

  and dom_ty : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPi(a, _) -> Lazy.force a
      | _ -> failwith "internal type error")

  and cod_ty : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPi(_, b) -> DLam b
      | _ -> failwith "internal type error")

  and pathp_ty_lhs : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPathP(_, a, _, _) -> Sub.d (Sub.app Zero) (Lazy.force a)
      | _ -> failwith "internal type error")

  and pathp_ty_rhs : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPathP(_, a, _, _) -> Sub.d (Sub.app One) (Lazy.force a)
      | _ -> failwith "internal type error")

  and pathp_ty_path : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPathP(i, a, _, _) -> DDimAbs(i, a)
      | _ -> failwith "internal type error")

  and pathp_lhs : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPathP(_, _, lhs, _) -> Lazy.force lhs
      | _ -> failwith "internal type error")

  and pathp_rhs : 'n. 'n d -> 'n d
    = fun x -> bind x (function
      | DPathP(_, _, _, rhs) -> Lazy.force rhs
      | _ -> failwith "internal type error")

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
        let env' = Dim (DimVar 0) :: Sub.env Sub.shift_up env in
        let r, r' = eval_dim env r, eval_dim env r' in
        let ty = lazy (eval env' ty) in
        let a = lazy (eval env a) in
        coe r r' ty a
    | Com { s; r; r'; i; ty; lhs; rhs } ->
        let env' = Dim (DimVar 0) :: Sub.env Sub.shift_up env in
        let s, r, r' = eval_dim env s, eval_dim env r, eval_dim env r' in
        let ty = lazy (eval env' ty) in
        let lhs = lazy (eval env' lhs) in
        let rhs = lazy (eval env' rhs) in
        com s r r' ty lhs rhs
    | HCom { s; r'; i; lhs; rhs } ->
        let env' = Dim (DimVar 0) :: Sub.env Sub.shift_up env in
        let s, r' = eval_dim env s, eval_dim env r' in
        let lhs = lazy (eval env' lhs) in
        let rhs = lazy (eval env' rhs) in
        hcom s r' lhs rhs
    | Abort -> failwith "unreachable"
    | Set -> DSet
    | DomTy x -> dom_ty (eval env x)
    | CodTy x -> cod_ty (eval env x)
    | PathPTyLhs x -> pathp_ty_lhs (eval env x)
    | PathPTyRhs x -> pathp_ty_rhs (eval env x)
    | PathPTyPath x -> pathp_ty_path (eval env x)
    | PathPLhs x -> pathp_lhs (eval env x)
    | PathPRhs x -> pathp_rhs (eval env x)
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

  (* How to coe r r' (i.A) a: (bottom of p.14)
    (force A and) match A with
    | Π(x:A) → B   ⇒  λ x. coe r r' i.B(coe r' i (i.A) x) (a(coe r' r i.A x))
    | Σ(x:A) × B   ⇒  (coe r r' i.A a.0, coe r r' i.B(coe r i i.A a.0) a.1
    | Path j.A x y ⇒  λ j. com<j> r r' i.A(j) i.x i.y i.a@j
    | Bool         ⇒  a
    | Set          ⇒  a
    | i ? l : r    ⇒  (a neutral term; BUT ALSO special rules)
    | neutral      ⇒  (a neutral term; BUT ALSO special rules)

  Special rules for coe:
   - when r = r', coe is identity
   - REGULARITY: when i,j ⊢ A(i) = A(j), coe is identity
  *)
  and coe : 'n. 'n dim -> 'n dim -> 'n s dl -> 'n dl -> 'n d
    = fun r r' ty x -> bind_shift_down (Lazy.force ty) (function
        | DSet -> Lazy.force x
        | DPi(a, b) ->
            let a = lazy (DDimAbs("i", a)) in
            let b = lazy (DDimAbs("i", lazy (DLam b))) in

            (* indices:    1      2       3      4      5 *)
            let env = [Dim r; Dim r'; Val a; Val b; Val x] in

            (* λ x. coe r r' i.B(coe r' i (i.A) x) (a(coe r' r i.A x)) *)
            let open Core in
            let arg, r, r', a, b, x =
              Var 0, DimVar 1, DimVar 2, Var 3, Var 4, Var 5 in
            let body = Coe(r, r', "i",
              begin
                let i, arg, r, r', a, b, x =
                  DimVar 0, Var 1, DimVar 2, DimVar 3, Var 4, Var 5, Var 6 in
                App(DimApp(b, i), Coe(r', i, "i", DimApp(Var 5, DimVar 0), arg))
              end,
              App(x, Coe(r', r, "i", DimApp(Var 4, DimVar 0), arg))) in
            DLam { name = "x"; env; body }
        | DPathP(j, ty, lhs, rhs) ->
            DDimAbs(j, lazy (
              let shift: ('n, 'n s) sub = Sub.shift_up in
              let shift' = Sub.extend shift in
              let r, r' = Sub.dim shift r, Sub.dim shift r' in
              let lhs, rhs = Sub.dl shift' lhs, Sub.dl shift' rhs in
              (* let cap = lazy (dim_app *)
              (*   (Sub.dl (Sub.compose Sub.shift_up shift) a) (DimVar 1)) in *)
              let swap: ('n s s, 'n s s) sub =
                Sub.(compose (app (DimVar 1)) (extend shift')) in
              let ty = Sub.dl swap ty in
              com (DimVar 0) r r' ty lhs rhs))
        | (DSplit _ | DNe _) as ty ->
            let ty0 = lazy (Sub.d (Sub.app Zero) ty) in
            let ty1 = lazy (Sub.d (Sub.app One) ty) in
            let neutral = lazy (DNe (DCoe { r; r'; ty0; ty1; a = x })) in
            DIf { cond = DimEq(r, r')
                ; yes = x
                ; no = lazy (DIf
                  { cond = TyEq(ty0, ty1); yes = x; no = neutral }) }
        | _ -> failwith "internal type error")

  (* How to com<s> r r' (i.A) i.lhs i.rhs a:
    hcom<s> r r' A(r')
      i.(coe i r' (i.A) lhs)
      i.(coe i r' (i.A) rhs)
      (coe r r' (i.A) a)
  *)
  and com
    : 'n. 'n dim -> 'n dim -> 'n dim -> 'n s dl -> 'n s dl -> 'n s dl -> 'n d
    = fun s r r' ty lhs rhs ->
    let ty_up = Sub.dl Sub.shift_up ty in
    let r'_up = Sub.dim Sub.shift_up r' in
    let coerce_it x = lazy (coe (DimVar 0) r'_up ty_up x) in
    let lhs', rhs' = coerce_it lhs, coerce_it rhs in
    hcom s r' lhs' rhs'

  (* How to hcom<s> r r' A i.lhs i.rhs a:
    All that matters is the boundary behavior!
    Just return DSplit s lhs(r') rhs(r')
    Lmao
  *)
  and hcom : 'n. 'n dim -> 'n dim -> 'n s dl -> 'n s dl -> 'n d
    = fun s r' lhs rhs ->
      let lhs_r' = Sub.dl (Sub.app r') lhs in
      let rhs_r' = Sub.dl (Sub.app r') rhs in
      DSplit(s, lhs_r', rhs_r')
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
    ; formula = DisjSets.(empty |> add 0 0 |> add 1 1) }

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

  let dim_to_id ctx =
    function
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

module Conv : sig
  open Domain
  
  val force : 'n Ctx.t -> 'n dl -> 'n d

  (* Conversion checking *)
  val eq : 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> bool

  (* Subtype checking *)
  val sub : 'n Ctx.t -> 'n dl -> 'n dl -> bool
end = struct
  open Domain
  
  let lam_to_clos lam =
    { name = "x"
    ; env = [Val lam]
    ; body = App(Var 1, Var 0) }

  (* Resolve DIf/DSplit conditions and apply INTERNAL INJECTIVITY! *)
  let rec force : 'n. 'n Ctx.t -> 'n dl -> 'n d
    = fun ctx x -> match Lazy.force x with
    | DIf { cond; yes; no } ->
        force ctx (if is_cond_true ctx cond then yes else no)
    | DSplit(dim, l, r) -> begin
        if Ctx.are_dims_eq ctx dim Zero then
          force ctx l
        else if Ctx.are_dims_eq ctx dim One then
          force ctx r
        else
          let l, r = force ctx l, force ctx r in
          let tm = DSplit(dim, lazy l, lazy r) in
          match l, r with
          | DNe l, DNe r when eq_ne ctx l r -> DNe l
          | DSet, DSet -> DSet
          | DPi _, DPi _ ->
              let dom = lazy (Eval.dom_ty tm) in
              let cod = lazy (Eval.cod_ty tm) in
              DPi(dom, lam_to_clos cod)
          | DPathP _, DPathP _ ->
              let a = lazy (Eval.un_dim_abs (lazy (Eval.pathp_ty_path tm))) in
              let lhs = lazy (Eval.pathp_lhs tm) in
              let rhs = lazy (Eval.pathp_rhs tm) in
              DPathP("i", a, lhs, rhs)
          (* TODO: extend this when extending the domain *)
          | _ -> DSplit(dim, lazy l, lazy r)
        end
    | x -> x

  and is_cond_true : 'n. 'n Ctx.t -> 'n cond -> bool
    = fun ctx cond -> match cond with
    | DimEq(i, j) -> Ctx.are_dims_eq ctx i j
    | TyEq(x, y) -> eq ctx (lazy DSet) x y
    | Forall_i cond ->
        let _i, ctx' = Ctx.with_dim_var ctx "i" in
        is_cond_true ctx' cond

  and eq_ne : 'n. 'n Ctx.t -> 'n dne -> 'n dne -> bool
    = fun ctx x y -> Option.is_some (conv_ne ctx x y)

  (* Conversion checking of neutrals returns their type *)
  and conv_ne : 'n. 'n Ctx.t -> 'n dne -> 'n dne -> 'n dl option
    = fun ctx x y -> match x, y with
    | DVar(x, ty), DVar(y, _) ->
        if x = y then Some ty else None
    | DApp(fx, arg_x), DApp(fy, arg_y) ->
        Option.bind (Option.map Lazy.force (conv_ne ctx fx fy)) (function
          | DPi(a, b) ->
              let open Eval in
              if eq ctx a arg_x arg_y then Some (lazy (b $ arg_x)) else None
          | _ -> failwith "internal type error")
    | DCoe { r = rx; r' = r'_x; ty0 = ty0_x; ty1 = ty1_x; a = ax }
    , DCoe { r = ry; r' = r'_y; ty0 = ty0_y; ty1 = ty1_y; a = ay } ->
        if not (Ctx.are_dims_eq ctx rx ry) then None
        else if not (Ctx.are_dims_eq ctx r'_x r'_y) then None
        else if not (eq ctx (lazy DSet) ty0_x ty0_y) then None
        else if not (eq ctx (lazy DSet) ty1_x ty1_y) then None
        else if not (eq ctx (lazy (DSplit(rx, ty0_x, ty1_x))) ax ay) then None
        else Some (lazy (DSplit(r'_x, ty0_x, ty0_y)))
    | _ -> None

  (* hooray for *boundary separation* *)
  and check_both : 'n Ctx.t -> 'n dim -> 'n dl -> 'n dl
    -> ('n Ctx.t -> 'n dl -> bool) -> bool
    = fun ctx dim l r k ->
    let ctx_l = Option.get @@ Ctx.with_eqn ctx dim Zero in
    let ctx_r = Option.get @@ Ctx.with_eqn ctx dim One in
    k ctx_l l && k ctx_r r

  and eq : 'n. 'n Ctx.t -> 'n dl -> 'n dl -> 'n dl -> bool
    = fun ctx ty x y -> match force ctx ty with
    | DNe _ as ty -> begin
        match force ctx x, force ctx y with
        | DSplit(dim, xl, xr), y ->
            let ty, y = lazy ty, lazy y in
            check_both ctx dim xl xr (fun ctx x -> eq ctx ty x y)
        | x, DSplit(dim, yl, yr) ->
            let ty, x = lazy ty, lazy x in
            check_both ctx dim yl yr (fun ctx y -> eq ctx ty x y)
        | DNe x, DNe y -> eq_ne ctx x y
        | _ -> failwith "internal type error"
        end
    | DSplit(dim, ty_l, ty_r) ->
        check_both ctx dim ty_l ty_r (fun ctx ty -> eq ctx ty x y)
    | DSet -> begin
        match force ctx x, force ctx y with
        | DSplit(dim, xl, xr), y ->
            let ty, y = lazy DSet, lazy y in
            check_both ctx dim xl xr (fun ctx x -> eq ctx ty x y)
        | x, DSplit(dim, yl, yr) ->
            let ty, x = lazy DSet, lazy x in
            check_both ctx dim yl yr (fun ctx y -> eq ctx ty x y)
        | DNe x, DNe y -> eq_ne ctx x y
        | DSet, DSet -> true
        | DPi(xa, xb), DPi(ya, yb) ->
            let open Eval in
            eq ctx (lazy DSet) xa ya &&
              let v, ctx' = Ctx.with_var ctx xb.name xa in
              eq ctx' (lazy DSet) (lazy (xb $ v)) (lazy (yb $ v))
        | DPathP(name, xa, xl, xr), DPathP(_, ya, yl, yr) ->
            let _i, ctx' = Ctx.with_dim_var ctx name in
            eq ctx' (lazy DSet) xa ya &&
              let ty_l = Sub.dl (Sub.app Zero) xa in
              let ty_r = Sub.dl (Sub.app One) xa in
              eq ctx ty_l xl yl && eq ctx ty_r xr yr
        | _ -> false
        end
    | DPi(a, b) ->
        let v, ctx' = Ctx.with_var ctx b.name a in
        let open Eval in
        eq ctx' (lazy (b $ v)) (lazy (app x v)) (lazy (app y v))
    | DPathP _ -> true (* lol definitional UIP *)
    | _ -> failwith "internal error: not a type"

  (* TODO *)
  let sub : 'n. 'n Ctx.t -> 'n dl -> 'n dl -> bool
    = fun ctx x y -> eq ctx (lazy DSet) x y

end

module Pretty : sig
  open Domain

  (* Given ctx ⊢ x : ty, show ctx ty x pretty-prints x *)
  val show : 'n Ctx.t -> 'n dl -> 'n dl -> string
end = struct
  open Domain
  let ($) f x = lazy Eval.(f $ x)

  let parens p s = if p then "(" ^ s ^ ")" else s

  let rec go : 'n. bool -> 'n Ctx.t -> 'n dl -> 'n dl -> string
    = fun p ctx ty x -> match Conv.force ctx x with
    | DNe ne -> fst (go_ne p ctx ne)
    | DSplit(dim, a, b) ->
        let ctx_l = Option.get @@ Ctx.with_eqn ctx dim Zero in
        let ctx_r = Option.get @@ Ctx.with_eqn ctx dim One in
        let dim = show_dim ctx dim in
        "[" ^ dim ^ " ↦ " ^ go false ctx_l ty a ^ " | "
        ^ dim ^ " ↦ " ^ go false ctx_r ty b ^ "]"
    | DIf _ -> failwith "unreachable"
    | DSet -> "Set"
    | DPi(a, b) ->
        let v, ctx' = Ctx.with_var ctx b.name a in
        parens p @@
          "Π (" ^ b.name ^ " : " ^ go false ctx ty a ^ ") → "
          ^ go false ctx' ty (b $ v)
    | DLam f ->
        let a, b = match Conv.force ctx ty with
          | DPi(a, b) -> a, b
          | _ -> failwith "internal type error" in
        let v, ctx' = Ctx.with_var ctx f.name a in
        parens p @@ "λ " ^ f.name ^ " → " ^ go false ctx' (b $ v) (f $ v)
    | DPathP(i, ty, lhs, rhs) ->
        let _, ctx' = Ctx.with_dim_var ctx i in
        let lhs_ty = Sub.dl (Sub.app Zero) ty in
        let rhs_ty = Sub.dl (Sub.app One) ty in
        parens p @@
          "pathp " ^ i ^ "." ^ go true ctx' (lazy DSet) ty
            ^ " " ^ go true ctx lhs_ty lhs ^ " " ^ go true ctx rhs_ty rhs
    | DDimAbs(i, body) ->
        let _, ctx' = Ctx.with_dim_var ctx i in
        let ty = match Conv.force ctx ty with
          | DPathP(_, ty, _, _) -> ty
          | _ -> failwith "internal type error" in
        parens p @@ "λ " ^ i ^ " → " ^ go false ctx' ty body

  and go_ne : 'n. bool -> 'n Ctx.t -> 'n dne -> string * 'n dl
    = fun p ctx x -> match x with
    | DVar(l, ty) -> List.nth (Ctx.tm_names ctx) (Ctx.lvl ctx - l - 1), ty
    | DApp(f, x) ->
        let f, fty = go_ne false ctx f in
        let a, b = match Conv.force ctx fty with
          | DPi(a, b) -> a, b
          | _ -> failwith "internal type error" in
        let str = parens p @@ f ^ " " ^ go true ctx a x in
        str, (b $ x)
    | DCoe { r; r'; ty0; ty1; a } ->
        let a_ty = lazy (DSplit(r', ty0, ty1)) in
        let res_ty = lazy (DSplit(r', ty0, ty1)) in
        let whole_ty =
          lazy (DSplit(DimVar 0
               , Sub.dl Sub.shift_up ty0
               , Sub.dl Sub.shift_up ty1)) in
        let _, ctx' = Ctx.with_dim_var ctx "i" in
        let str = parens p @@
          "coe " ^ show_dim ctx r ^ " " ^ show_dim ctx r' ^ " i."
          ^ go true ctx' whole_ty (lazy DSet) ^ " " ^ go true ctx a a_ty in
        str, res_ty

  and show_dim : 'n. 'n Ctx.t -> 'n dim -> string
    = fun ctx d -> match d with
    | Zero -> "0"
    | One -> "1"
    | DimVar idx -> List.nth (Ctx.dim_names ctx) idx

  let show ctx ty x =
    go false ctx ty x
end

module Tychk = struct
  open Domain

  exception TypeError of string

  let check_eq ctx ty x y =
    if not (Conv.eq ctx ty x y) then
      let x = Pretty.show ctx ty x in
      let y = Pretty.show ctx ty y in
      raise (TypeError(x ^ " is different from " ^ y))

  let check_sub ctx x y =
    if not (Conv.sub ctx x y) then
      let x = Pretty.show ctx (lazy DSet) x in
      let y = Pretty.show ctx (lazy DSet) y in
      raise (TypeError(x ^ " is not a subtype of " ^ y))

  (* the main check/infer loop! *)
  let rec check : 'n. 'n Ctx.t -> AST.exp -> 'n dl -> Core.tm =
    fun ctx exp ty -> match exp, Conv.force ctx ty with
    | Lam(x, body), DPi(a, b) ->
        let v, ctx' = Ctx.with_var ctx x a in
        Core.Lam(x, check ctx' body (lazy Eval.(b $ v)))
    | Let(x, e, b), t ->
        let tm, ty = infer ctx e in
        let value = lazy (Eval.eval (Ctx.env ctx) tm) in
        let ctx' = Ctx.with_defn ctx x ty value in
        Core.Let(x, tm, check ctx' b (lazy t))
    | Lam(name, body), DPathP(_, ty, lhs, rhs) ->
        let i, ctx' = Ctx.with_dim_var ctx name in
        let body = check ctx' body ty in
        let actual_lhs = lazy (Eval.eval (Dim Zero::Ctx.env ctx) body) in
        let actual_rhs = lazy (Eval.eval (Dim One ::Ctx.env ctx) body) in
        check_eq ctx (Sub.dl (Sub.app Zero) ty) actual_lhs lhs;
        check_eq ctx (Sub.dl (Sub.app One) ty) actual_rhs rhs;
        Core.DimAbs(name, body)
    | e, t ->
        let tm, t' = infer ctx e in
        check_sub ctx t' (lazy t);
        tm
  
  and check_dim : 'n. 'n Ctx.t -> AST.exp -> Core.dim
    = fun ctx e -> match e with
    | Zero -> Core.Zero
    | One  -> Core.One
    | Var v -> Core.DimVar (Ctx.lookup_dim ctx v)
    | _ -> raise (TypeError("it is not a dimension"))

  and infer : 'n. 'n Ctx.t -> AST.exp -> Core.tm * 'n dl
    = fun ctx exp -> match exp with
    | Var v ->
        let i, ty = Ctx.lookup_var ctx v in
        Core.Var i, ty
    | Let(x, e, b) ->
        let tm, ty = infer ctx e in
        let value = lazy (Eval.eval (Ctx.env ctx) tm) in
        let ctx' = Ctx.with_defn ctx x ty value in
        let body, t = infer ctx' b in
        Core.Let(x, tm, body), t
    | Annot(e, t) ->
        let t_tm = check ctx t (lazy DSet) in
        let t = lazy (Eval.eval (Ctx.env ctx) t_tm) in
        let tm = check ctx e t in
        tm, t
    | Coe { r; r'; i; ty; a } ->
        let r', r = check_dim ctx r', check_dim ctx r in
        let _, ctx' = Ctx.with_dim_var ctx i in
        let ty = check ctx' ty (lazy DSet) in
        let ty_at dim =
          let env = Ctx.env ctx in
          lazy (Eval.eval (Dim (Eval.eval_dim env dim)::env) ty) in
        let ty_r, ty_r' = ty_at r, ty_at r' in
        let a = check ctx a ty_r in
        Core.Coe(r, r', i, ty, a), ty_r'
    | Com { s; r; r'; ty; lhs; rhs; a } ->
        let r', r, s = check_dim ctx r', check_dim ctx r, check_dim ctx s in
        let name = fst ty in
        let _, ctx' = Ctx.with_dim_var ctx (fst ty) in
        let ty = check ctx' (snd ty) (lazy DSet) in
        let ty_v = lazy (Eval.eval (Ctx.env ctx') ty) in
        let s_v = Sub.dim Sub.shift_up @@ Eval.eval_dim (Ctx.env ctx) s in
        let r_v = Eval.eval_dim (Ctx.env ctx) r in
        let r'_v = Eval.eval_dim (Ctx.env ctx) r' in 
        let a_ty = Sub.dl (Sub.app r_v) ty_v in
        let res_ty = Sub.dl (Sub.app r'_v) ty_v in
        let a = check ctx a a_ty in
        let _, ctx' = Ctx.with_dim_var ctx (fst lhs) in
        let lhs = match Ctx.with_eqn ctx' s_v Zero with
          | None -> print_endline "warning: wack"; Core.Abort
          | Some ctx'' -> check ctx'' (snd lhs) ty_v in
        let _, ctx' = Ctx.with_dim_var ctx (fst rhs) in
        let rhs = match Ctx.with_eqn ctx' s_v One with
          | None -> print_endline "warning: wack"; Core.Abort
          | Some ctx'' -> check ctx'' (snd rhs) ty_v in
        (* coherence conditions:
          s=0 ⊢ a = lhs@r
          s=1 ⊢ a = rhs@r
        *)
        let a_v = lazy (Eval.eval (Ctx.env ctx) a) in
        let s_v = Eval.eval_dim (Ctx.env ctx) s in
        Option.iter (fun ctx ->
          let lhs = lazy (Eval.eval (Dim r_v::Ctx.env ctx) lhs) in
          check_eq ctx a_ty lhs a_v) (Ctx.with_eqn ctx s_v Zero);
        Option.iter (fun ctx ->
          let rhs = lazy (Eval.eval (Dim r_v::Ctx.env ctx) rhs) in
          check_eq ctx a_ty rhs a_v) (Ctx.with_eqn ctx s_v One);

        Core.Com { s; r; r'; i = name; ty; lhs; rhs }, res_ty

    | Set -> Core.Set, lazy DSet
    | Pi(x, a, b) ->
        let a = check ctx a (lazy DSet) in
        let _, ctx' = Ctx.with_var ctx x (lazy (Eval.eval (Ctx.env ctx) a)) in
        let b = check ctx' b (lazy DSet) in
        Core.Pi(x, a, b), lazy DSet
    | PathP(i, ty, lhs, rhs) ->
        let _, ctx' = Ctx.with_dim_var ctx i in
        let ty = check ctx' ty (lazy DSet) in
        let ty_at dim =
          let env = Ctx.env ctx in
          lazy (Eval.eval (Dim dim::env) ty) in
        let ty0, ty1 = ty_at Zero, ty_at One in
        let lhs = check ctx lhs ty0 in
        let rhs = check ctx rhs ty1 in
        Core.PathP(i, ty, lhs, rhs), lazy DSet
    | Eq(x, y) ->
        let x, ty = infer ctx x in
        let _y = check ctx y ty in
        (* Aaaaa need to be able to *quote*! *)
        failwith "TODO gotta implement quote"
    | App(f, x) ->
        let f, f_ty = infer ctx f in
        begin match Conv.force ctx f_ty with
          | DPi(a, b) ->
              let x = check ctx x a in
              let v = lazy (Eval.eval (Ctx.env ctx) x) in
              Core.App(f, x), lazy Eval.(b $ v)
          | DPathP(_, a, _, _) ->
              let i = check_dim ctx x in
              let ty = Sub.dl (Sub.app (Eval.eval_dim (Ctx.env ctx) i)) a in
              Core.DimApp(f, i), ty
          | _ -> raise (TypeError "that's not a function")
        end
    | _ -> failwith "TODO (or maybe that's not a thing you could infer)"

end

module Parser : sig
  exception ParseError of string

  val parse : string -> AST.exp
end = struct
  open AST

  exception ParseError of string

  let parse s =
    (* a hack but it works *)
    let len = String.length s in
    let s = s ^ "\000" in

    let rec many p i =
      Option.fold ~none:([], i) ~some:(fun (x, i) ->
        let xs, i = many p i in x :: xs, i) (p i) in

    let matches k i =
      String.length s - i >= String.length k
        && String.sub s i (String.length k) = k in

    let definitely n = function
      | Some x -> x
      | None -> raise (ParseError("expected " ^ n)) in

    let rec ws i =
      if String.contains " \n\t" s.[i] then ws (i+1)
      else if matches "--" i then
        ws (String.index_from s (i+2) '\n' + 1)
      else i
    and end_of_ident i =
      if 'a' <= s.[i] && s.[i] <= 'z'
        || 'A' <= s.[i] && s.[i] <= 'Z'
        || String.contains "-_" s.[i] then end_of_ident (i+1) else i

    and try_ident i =
      let l = end_of_ident i - i in
      if l = 0 then None else Some(String.sub s i l, ws (i+l))

    and reserved = ["let"]

    and after_kw k i = ws (i + String.length k)

    and str x i =
      if matches x i then after_kw x i else raise (ParseError("expected " ^ x))

    and try_atomic i =
      if matches "0" i then
        Some(Zero, ws (i+1))
      else if matches "1" i then
        Some(One, ws (i+1))
      else if matches "(" i then
        let i = after_kw "(" i in
        let x, i = expr i in
        let i = str ")" i in
        Some(x, i)
      else Option.bind (try_ident i) (fun (x, i) ->
        if List.mem x reserved then None
        else if x = "Set" then Some (Set, i)
        else Some(Var x, i))

    and binder i =
      let dim, i = definitely "ident" (try_ident i) in
      let i = str "." i in
      let exp, i = definitely "expression" (try_atomic i) in
      dim, exp, i

    and app_expr i =
      (* TODO clean this up (coe, com should be reserved words) *)
      match try_atomic i with
      | Some(Var "coe", i) ->
          let r, i = definitely "dimension" (try_atomic i) in
          let r', i = definitely "dimension" (try_atomic i) in
          let name, ty, i = binder i in
          let a, i = definitely "expression" (try_atomic i) in
          Coe { r; r'; i = name; ty; a }, i
      | Some(Var "com", i) ->
          let i = str "<" i in
          let s, i = definitely "dimension" (try_atomic i) in
          let i = str ">" i in
          let r, i = definitely "dimension" (try_atomic i) in
          let r', i = definitely "dimension" (try_atomic i) in
          let ty_dim, ty, i = binder i in 
          let lhs_dim, lhs, i = binder i in
          let rhs_dim, rhs, i = binder i in
          let a, i = definitely "expression" (try_atomic i) in
          Com { s; r; r'; ty = ty_dim, ty
              ; lhs = lhs_dim, lhs; rhs = rhs_dim, rhs; a }, i
      | Some(Var "pathp", i) ->
          let dim, ty, i = binder i in
          let lhs, i = definitely "expression" (try_atomic i) in
          let rhs, i = definitely "expression" (try_atomic i) in
          PathP(dim, ty, lhs, rhs), i
      | Some(hd, i) ->
          let args, i = many try_atomic i in
          List.fold_left (fun f x -> App(f, x)) hd args, i
      | None ->
          raise (ParseError "expecting expression")

    and arrow i =
      if matches "→" i then after_kw "→" i else str "->" i
    and times i =
      if matches "×" i then after_kw "×" i else str "*" i

    and rest_of_lam i =
      match try_ident i with
      | Some(x, i) ->
          let body, i = rest_of_lam i in
          Lam(x, body), i
      | None -> expr (arrow i)

    and telescope c k i =
      if matches "(" i then
        let i = after_kw "(" i in
        let names, i = many try_ident i in
        let i = str ":" i in
        let ty, i = expr i in
        let i = str ")" i in
        let rest, i = telescope c k i in
        List.fold_right (fun name r -> c name ty r) names rest, i
      else k i

    and expr_no_annot i =
      if matches "Σ" i then
        let i = after_kw "Σ" i in
        telescope (fun x a b -> Sigma(x, a, b)) (fun i -> expr (times i)) i
      else if matches "Π" i then
        let i = after_kw "Π" i in
        telescope (fun x a b -> Pi(x, a, b)) (fun i -> expr (arrow i)) i
      else if matches "∀" i then
        let i = after_kw "∀" i in
        telescope (fun x a b -> Pi(x, a, b)) (fun i -> expr (arrow i)) i
      else if matches "λ" i then
        rest_of_lam (after_kw "λ" i)
      else if matches "\\" i then
        rest_of_lam (after_kw "\\" i)
      else match try_ident i with
      | Some("let", i) ->
          let name, i = definitely "name" (try_ident i) in
          let e, i = expr (str "=" i) in
          let i = str ";" i in
          let body, i = expr i in
          Let(name, e, body), i
      | _ -> app_expr i

    and expr i =
      let e, i = expr_no_annot i in
      if matches ":" i then
        let i = after_kw ":" i in
        let ty, i = expr i in
        Annot(e, ty), i
      else if matches "≡" i then
        let i = after_kw "≡" i in
        let rhs, i = expr_no_annot i in
        Eq(e, rhs), i
      else e, i in

    let e, i = expr (ws 0) in
    if i = len then e
    else raise (ParseError "didn't parse everything")
end

let repl () =
  let ctx = Ctx.initial_ctx in
  try while true do
    print_string "> "; Format.print_flush ();
    let line = input_line stdin in
    let ast = Parser.parse line in
    let _, ty = Tychk.infer ctx ast in
    print_endline "<stdin> is well-typed!";
    print_endline ("it : " ^ Pretty.show ctx (lazy Domain.DSet) ty)
  done with End_of_file -> ()

(* From stackoverflow *)
let read_file filename =
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch; s

let main () =
  if Array.length Sys.argv > 1 then
    let fn = Sys.argv.(1) in
    let input = read_file fn in
    let ast = Parser.parse input in
    let ctx = Ctx.initial_ctx in
    let _, ty = Tychk.infer ctx ast in
    print_endline (fn ^ " is well-typed!");
    print_endline ("it : " ^ Pretty.show ctx (lazy Domain.DSet) ty)
  else repl ()

let () = main ()

