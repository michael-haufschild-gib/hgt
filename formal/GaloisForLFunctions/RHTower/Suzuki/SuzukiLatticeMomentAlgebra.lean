import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticePositionCommutator

/-!
# The exact position moments of an adjacency word applied to the origin

Iterating the position commutator `(16)` on the delta field at the origin collapses completely:
because every commutator is again a finite-range adjacency and all of them commute, the `n`-th power
of the adjacency has position moment exactly `-n` times the `(n-1)`-st power of the commutator
adjacency.  No cancellation is lost, which is why the moments of the evolution grow only
polynomially in the time.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The delta field at a lattice point. -/
def deltaField (ν₀ : P → ℤ) : (P → ℤ) → ℂ := fun ν => if ν = ν₀ then 1 else 0

omit [DecidableEq P] in
theorem posMulField_deltaField (p : P) : posMulField p (deltaField (0 : P → ℤ)) = 0 := by
  funext ν
  rw [posMulField, deltaField]
  by_cases h : ν = 0
  · subst h
    simp
  · simp [h]

omit [Fintype P] [DecidableEq P] in
theorem adjacencyField_zero (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) :
    adjacencyField Q c (0 : (P → ℤ) → ℂ) = 0 := by
  funext ν
  rw [adjacencyField]
  simp

omit [Fintype P] [DecidableEq P] in
theorem adjacencyField_smul (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (a : ℂ)
    (ψ : (P → ℤ) → ℂ) :
    adjacencyField Q c (fun ν => a * ψ ν) = fun ν => a * adjacencyField Q c ψ ν := by
  funext ν
  rw [adjacencyField, adjacencyField, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

omit [Fintype P] [DecidableEq P] in
theorem adjacencyField_sub (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (ψ φ : (P → ℤ) → ℂ) :
    adjacencyField Q c (fun ν => ψ ν - φ ν)
      = fun ν => adjacencyField Q c ψ ν - adjacencyField Q c φ ν := by
  funext ν
  rw [adjacencyField, adjacencyField, adjacencyField, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

omit [Fintype P] [DecidableEq P] in
/-- Two finite-range adjacencies on the same step set commute: all the shifts commute. -/
theorem adjacencyField_comm (Q : Finset (P → ℤ)) (c c' : (P → ℤ) → ℂ) (ψ : (P → ℤ) → ℂ) :
    adjacencyField Q c (adjacencyField Q c' ψ)
      = adjacencyField Q c' (adjacencyField Q c ψ) := by
  funext ν
  simp only [adjacencyField, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
  rw [show ν + q' + q = ν + q + q' by abel]
  ring

omit [Fintype P] [DecidableEq P] in
theorem adjacencyField_iterate_comm (Q : Finset (P → ℤ)) (c c' : (P → ℤ) → ℂ) (n : ℕ)
    (ψ : (P → ℤ) → ℂ) :
    (adjacencyField Q c)^[n] (adjacencyField Q c' ψ)
      = adjacencyField Q c' ((adjacencyField Q c)^[n] ψ) := by
  induction n generalizing ψ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih,
      adjacencyField_comm Q c c' ψ]

omit [DecidableEq P] in
/-- **The exact position moment of an adjacency word at the origin.** -/
theorem posMulField_adjacencyField_iterate (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P)
    (n : ℕ) :
    posMulField p ((adjacencyField Q c)^[n + 1] (deltaField (0 : P → ℤ)))
      = fun r => -((n : ℂ) + 1) *
          ((adjacencyField Q c)^[n]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)))) r := by
  induction n with
  | zero =>
    rw [Function.iterate_one, posMulField_adjacencyField, posMulField_deltaField,
      adjacencyField_zero]
    funext r
    simp only [Pi.zero_apply, zero_sub, Function.iterate_zero, id_eq, Nat.cast_zero, zero_add,
      neg_mul, one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (f := adjacencyField Q c) (n := k + 1),
      posMulField_adjacencyField, ih]
    have hsmul : adjacencyField Q c
        (fun r => -((k : ℂ) + 1) *
          ((adjacencyField Q c)^[k]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)))) r)
        = fun r => -((k : ℂ) + 1) *
          adjacencyField Q c ((adjacencyField Q c)^[k]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ)))) r :=
      adjacencyField_smul Q c _ _
    rw [hsmul]
    funext r
    have hcomm : adjacencyField Q (stepWeighted p c)
        ((adjacencyField Q c)^[k + 1] (deltaField (0 : P → ℤ)))
        = (adjacencyField Q c)^[k + 1]
            (adjacencyField Q (stepWeighted p c) (deltaField (0 : P → ℤ))) :=
      (adjacencyField_iterate_comm Q c (stepWeighted p c) (k + 1) _).symm
    rw [hcomm, ← Function.iterate_succ_apply' (f := adjacencyField Q c) (n := k)]
    push_cast
    ring

end RHTower
