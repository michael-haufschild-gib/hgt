import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite weight range and a finite operator algebra

The part of any matrix that raises an integral weight by one is nilpotent
with exponent at most the weight width plus one, regardless of weight-space
multiplicities. Its generated algebra is spanned by that many powers, and
its resolvent is a finite geometric sum. This is the finite weight-range
mechanism behind the PBW truncation in Zehavi, Claim 3.32, arXiv:2611.18218.
-/

namespace GaloisForLFunctions.RepresentationLifting.Weights

open scoped BigOperators Classical

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] {w : ℕ}

/-- Retain exactly the matrix entries that raise the prescribed weight by one. -/
def weightRaisingPart (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) : Matrix ι ι K :=
  fun i j => if (wt i : ℕ) = (wt j : ℕ) + 1 then A i j else 0

/-- A product of `k` raising steps can connect only weights differing by `k`. -/
theorem weightRaisingPart_pow_support (wt : ι → Fin (w + 1)) (A : Matrix ι ι K)
    (k : ℕ) (i j : ι) (h : (wt i : ℕ) ≠ (wt j : ℕ) + k) :
    (weightRaisingPart wt A ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero]
    apply Matrix.one_apply_ne
    intro hij
    subst j
    exact h (by omega)
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hil : (wt i : ℕ) = (wt l : ℕ) + k
    · have hlj : (wt l : ℕ) ≠ (wt j : ℕ) + 1 := by omega
      simp only [weightRaisingPart, if_neg hlj, mul_zero]
    · rw [ih i l hil, zero_mul]

/-- The nilpotence bound depends on the weight range, not the matrix size. -/
theorem weightRaisingPart_nilpotent (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) :
    weightRaisingPart wt A ^ (w + 1) = 0 := by
  ext i j
  exact weightRaisingPart_pow_support wt A _ i j (by have := (wt i).isLt; omega)

/-- Every positive power is invisible to the trace. -/
theorem weightRaisingPart_trace (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) (k : ℕ) :
    Matrix.trace (weightRaisingPart wt A ^ (k + 1)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact weightRaisingPart_pow_support wt A _ i i (by omega)

/-- The full generated algebra already lies in the finite span of the first powers. -/
theorem weightRaisingPart_power_span (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) :
    Submodule.span K ((Finset.range (w + 1)).image (weightRaisingPart wt A ^ ·) :
      Set (Matrix ι ι K)) = (Algebra.adjoin K {weightRaisingPart wt A}).toSubmodule := by
  have h := Submodule.span_range_natDegree_eq_adjoin
    (R := K) (x := weightRaisingPart wt A) (Polynomial.monic_X_pow (w + 1))
    (by simpa using weightRaisingPart_nilpotent wt A)
  simpa only [Polynomial.natDegree_X_pow, Finset.coe_image] using h

/-- Weight multiplicities do not enlarge the dimension of the one-generator algebra. -/
theorem weightRaisingPart_adjoin_finrank (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) :
    Module.finrank K (Algebra.adjoin K {weightRaisingPart wt A}) ≤ w + 1 := by
  change Module.finrank K (Algebra.adjoin K {weightRaisingPart wt A}).toSubmodule ≤ _
  rw [← weightRaisingPart_power_span]
  exact (finrank_span_finset_le_card _).trans
    ((Finset.card_image_le).trans_eq (Finset.card_range _))

/-- The inverse of one minus the raising operator is polynomial of degree at most the width. -/
theorem weightRaisingPart_geometric_inverse (wt : ι → Fin (w + 1)) (A : Matrix ι ι K) :
    (∑ k ∈ Finset.range (w + 1), weightRaisingPart wt A ^ k) *
      (1 - weightRaisingPart wt A) = 1 ∧
    (1 - weightRaisingPart wt A) *
      (∑ k ∈ Finset.range (w + 1), weightRaisingPart wt A ^ k) = 1 := by
  have h₁ := geom_sum_mul (weightRaisingPart wt A) (w + 1)
  have h₂ := mul_geom_sum (weightRaisingPart wt A) (w + 1)
  rw [weightRaisingPart_nilpotent, zero_sub] at h₁ h₂
  constructor
  · rw [← neg_sub (weightRaisingPart wt A) 1, mul_neg, h₁, neg_neg]
  · rw [← neg_sub (weightRaisingPart wt A) 1, neg_mul, h₂, neg_neg]

end GaloisForLFunctions.RepresentationLifting.Weights

#print axioms GaloisForLFunctions.RepresentationLifting.Weights.weightRaisingPart_nilpotent
#print axioms GaloisForLFunctions.RepresentationLifting.Weights.weightRaisingPart_adjoin_finrank
#print axioms GaloisForLFunctions.RepresentationLifting.Weights.weightRaisingPart_geometric_inverse
