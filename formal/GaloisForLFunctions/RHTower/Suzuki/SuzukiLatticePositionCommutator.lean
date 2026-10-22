import GaloisForLFunctions.HTGeometry.LatticeL2Shift
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrbitWeightSummability

/-!
# `(15)`--`(16)`: the position commutator of a finite-range lattice adjacency

Multiplying by a coordinate and applying a finite-range adjacency fail to commute by exactly one
more finite-range adjacency: the coefficient of the step `q` picks up the factor `q_j`.  That is the
whole of `(16)`, and it is an identity of fields, not an asymptotic statement — which is why the
iterated commutators of `(15)` terminate and every one of them is again a bounded Laurent
polynomial in the commuting shifts.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The finite-range lattice adjacency acting on a scalar field. -/
def adjacencyField (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (ψ : (P → ℤ) → ℂ) :
    (P → ℤ) → ℂ := fun ν => ∑ q ∈ Q, c q * ψ (ν + q)

/-- Multiplication by a coordinate of the valuation. -/
def posMulField (j : P) (ψ : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun ν => ((ν j : ℤ) : ℂ) * ψ ν

/-- The adjacency with each step weighted by that coordinate of the step. -/
def stepWeighted (j : P) (c : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun q => c q * ((q j : ℤ) : ℂ)

omit [Fintype P] [DecidableEq P] in
/-- **`(16)`: the exact position commutator.**  `[M_j, A] = A_j`, the adjacency whose step
coefficients carry the extra factor `q_j`. -/
theorem posMulField_adjacencyField (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ)
    (ψ : (P → ℤ) → ℂ) (j : P) :
    posMulField j (adjacencyField Q c ψ)
      = fun ν => adjacencyField Q c (posMulField j ψ) ν
          - adjacencyField Q (stepWeighted j c) ψ ν := by
  funext ν
  rw [posMulField, adjacencyField, Finset.mul_sum]
  simp only [adjacencyField, posMulField, stepWeighted]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hcoord : (((ν + q) j : ℤ) : ℂ) = ((ν j : ℤ) : ℂ) + ((q j : ℤ) : ℂ) := by
    have : ((ν + q) j : ℤ) = ν j + q j := rfl
    rw [this]
    push_cast
    ring
  rw [hcoord]
  ring

omit [Fintype P] [DecidableEq P] in
/-- The commutator adjacency has the same finite support, so `(15)` terminates: every iterated
commutator is again a finite-range adjacency. -/
theorem stepWeighted_iterate (c : (P → ℤ) → ℂ) (j k : P) :
    stepWeighted k (stepWeighted j c) = fun q => c q * (((q j : ℤ) : ℂ) * ((q k : ℤ) : ℂ)) := by
  funext q
  rw [stepWeighted, stepWeighted]
  ring

omit [Fintype P] [DecidableEq P] in
/-- **`(15)`: the two-fold position commutator.**  Iterating `(16)` produces only finite-range
adjacencies, with the step coefficients carrying the monomial `q_j q_k`. -/
theorem posMulField_two_adjacencyField (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ)
    (ψ : (P → ℤ) → ℂ) (j k : P) :
    posMulField k (posMulField j (adjacencyField Q c ψ))
      = fun ν => adjacencyField Q c (posMulField k (posMulField j ψ)) ν
          - adjacencyField Q (stepWeighted j c) (posMulField k ψ) ν
          - (adjacencyField Q (stepWeighted k c) (posMulField j ψ) ν
              - adjacencyField Q (stepWeighted k (stepWeighted j c)) ψ ν) := by
  funext ν
  have h1 := posMulField_adjacencyField Q c ψ j
  have h2 := posMulField_adjacencyField Q c (posMulField j ψ) k
  have h3 := posMulField_adjacencyField Q (stepWeighted j c) ψ k
  rw [h1]
  simp only [posMulField]
  have hexp : ((ν k : ℤ) : ℂ) * (adjacencyField Q c (posMulField j ψ) ν
        - adjacencyField Q (stepWeighted j c) ψ ν)
      = ((ν k : ℤ) : ℂ) * adjacencyField Q c (posMulField j ψ) ν
        - ((ν k : ℤ) : ℂ) * adjacencyField Q (stepWeighted j c) ψ ν := by ring
  rw [hexp]
  have e2 : ((ν k : ℤ) : ℂ) * adjacencyField Q c (posMulField j ψ) ν
      = adjacencyField Q c (posMulField k (posMulField j ψ)) ν
        - adjacencyField Q (stepWeighted k c) (posMulField j ψ) ν := by
    have := congrFun h2 ν
    rw [posMulField] at this
    exact this
  have e3 : ((ν k : ℤ) : ℂ) * adjacencyField Q (stepWeighted j c) ψ ν
      = adjacencyField Q (stepWeighted j c) (posMulField k ψ) ν
        - adjacencyField Q (stepWeighted k (stepWeighted j c)) ψ ν := by
    have := congrFun h3 ν
    rw [posMulField] at this
    exact this
  rw [e2, e3]
  ring

end RHTower
