(* Extra stuff *)

type name = string
type idx = int and lvl = int

(* Type-level naturals *)
type z
type 'n s

module CubeSolver : sig
  (* Solver for dimension variable constraints *)

  type 'n t

  type dim
  type eqn = dim * dim
  type cof = eqn list (* an OR of equations; [] is false *)

  val zero : dim
  val one : dim
  val from_idx : 'n t -> idx -> dim

  val with_new_dim : 'n t -> 'n s t
  val with_cofib : 'n t -> cof -> 'n t option

  val implies : 'n t -> cof -> bool
  val eq : 'n t -> dim -> dim -> bool
end

module UnivSolver : sig
  (* Solver for universe level constraints *)

  type univ

  exception UniverseError of string

  (* Making new universe variables *)
  val infty : univ
  val new_lvl : unit -> univ

  (* Adding constriants *)
  val eq : univ -> univ -> unit
  val lte : univ -> univ -> unit
  val strictly_lt : univ -> univ -> unit

  (* Pretty-printing *)
  val show : univ -> string
end

type univ = UnivSolver.univ

