import GaloisForLFunctions.RHTower.SuzukiLatticePolynomialGroup

/-!
# Moving a coordinate power through a finite-range adjacency

A coordinate power does not commute with a finite-range adjacency, but the defect is completely
explicit: `r_p = (r+q)_p - q_p`, so the binomial theorem expresses `r_p^j A` as a finite combination
of adjacencies applied to lower coordinate powers, with the step coefficients carrying powers of
`q_p`.  Every coefficient family is again finitely supported, so each term is again a bounded
operator — which is why the moment tower of the evolution stays inside the polynomial class.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Multiplication by a power of a coordinate. -/
def posPowField (p : P) (j : ℕ) (ψ : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun r => ((r p : ℤ) : ℂ) ^ j * ψ r

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem posPowField_zero (p : P) (ψ : (P → ℤ) → ℂ) : posPowField p 0 ψ = ψ := by
  funext r
  rw [posPowField, pow_zero, one_mul]

omit [Fintype P] [DecidableEq P] in
theorem posPowField_succ (p : P) (j : ℕ) (ψ : (P → ℤ) → ℂ) :
    posPowField p (j + 1) ψ = posMulField p (posPowField p j ψ) := by
  funext r
  rw [posPowField, posMulField, posPowField, pow_succ]
  ring

/-- The step coefficients produced by moving a coordinate power across the adjacency. -/
def stepPowWeighted (p : P) (k : ℕ) (c : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun q => c q * (-((q p : ℤ) : ℂ)) ^ k

omit [Fintype P] [DecidableEq P] in
/-- **The binomial transfer.**  A coordinate power moves across a finite-range adjacency at the cost
of finitely many lower powers. -/
theorem posPowField_adjacencyField (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (j : ℕ)
    (ψ : (P → ℤ) → ℂ) :
    posPowField p j (adjacencyField Q c ψ)
      = fun r => ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ)
          * adjacencyField Q (stepPowWeighted p (j - i) c) (posPowField p i ψ) r := by
  funext r
  rw [posPowField, adjacencyField]
  have hexpand : ∀ q : P → ℤ, ((r p : ℤ) : ℂ) ^ j
      = ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ)
          * ((((r + q) p : ℤ) : ℂ) ^ i * (-((q p : ℤ) : ℂ)) ^ (j - i)) := by
    intro q
    have hsplit : ((r p : ℤ) : ℂ) = ((((r + q) p : ℤ) : ℂ)) + (-((q p : ℤ) : ℂ)) := by
      have hco : ((r + q) p : ℤ) = r p + q p := rfl
      rw [hco]
      push_cast
      ring
    rw [hsplit, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.mul_sum]
  have hstep : ∀ q ∈ Q, ((r p : ℤ) : ℂ) ^ j * (c q * ψ (r + q))
      = ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ)
          * ((c q * (-((q p : ℤ) : ℂ)) ^ (j - i))
            * (((((r + q) p : ℤ) : ℂ) ^ i) * ψ (r + q))) := by
    intro q _
    rw [hexpand q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adjacencyField, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [stepPowWeighted, posPowField]

end RHTower
