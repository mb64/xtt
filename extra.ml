type name = string
type idx = int and lvl = int

type z = unit
type 'n s = unit

module CubeSolver = struct
  type dim = int
  type eqn = dim * dim
  type cof = eqn list (* disjunction of equations; [] is false *)

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
    { dim_count: int
    ; alg: DisjSets.t
    ; non_alg: cof list }

  let zero = 0
  let one = 1
  let from_idx s i = 2 + (s.dim_count - i - 1)

  let with_new_dim s =
    let new_dim = 2 + s.dim_count in
    { dim_count = s.dim_count + 1
    ; alg = DisjSets.add new_dim new_dim s.alg
    ; non_alg = s.non_alg }

  let implies s cof =
    let rec go m = function
      | [] ->
          List.exists (fun (i, j) -> DisjSets.find i m = DisjSets.find j m) ((zero, one) :: cof)
      | c::cs ->
          List.for_all (fun (i, j) -> go (DisjSets.union i j m) cs) c in
    go s.alg s.non_alg

  let eq s i j =
    implies s [i, j]

  let with_cofib s = function
    | [] -> None
    | [i, j] ->
        let new_s = { s with alg = DisjSets.union i j s.alg } in
        if implies new_s [] then None else Some new_s
    | cof ->
        let new_s = { s with non_alg = cof :: s.non_alg } in
        if implies new_s [] then None else Some new_s
end

module UnivSolver = struct
  (* TODO lol *)

  type univ = unit

  exception UniverseError of string

  let infty = ()
  let new_lvl () = ()

  let eq () () = ()
  let lte () () = ()
  let strictly_lt () () = ()

  let show () = "0"
end

type univ = UnivSolver.univ
