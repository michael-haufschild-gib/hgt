import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuated determinant multilinearity

Finite linear combinations in one row or column expand into the corresponding linear combination
of determinants. A nonarchimedean valuation then bounds the result by the product of the largest
coefficient value and the largest replacement-determinant value. This is the reusable algebraic
core of the projected-minor estimate in the k-server paper's Lemma 4.3.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

section Multilinearity

variable {n κ R : Type*} [Fintype n] [DecidableEq n] [DecidableEq κ] [CommRing R]

/-- Determinant is linear in one replaced column over a finite external family. -/
theorem det_updateCol_finset_sum
    (A : Matrix n n R) (j : n) (s : Finset κ) (c : κ → R) (v : κ → n → R) :
    (A.updateCol j (∑ x ∈ s, c x • v x)).det =
      ∑ x ∈ s, c x * (A.updateCol j (v x)).det := by
  induction s using Finset.induction with
  | empty =>
      have hzero := Matrix.det_updateCol_smul A j (0 : R) (0 : n → R)
      simpa using hzero
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ih]

/-- Determinant is linear in one replaced row over a finite external family. -/
theorem det_updateRow_finset_sum
    (A : Matrix n n R) (i : n) (s : Finset κ) (c : κ → R) (v : κ → n → R) :
    (A.updateRow i (∑ x ∈ s, c x • v x)).det =
      ∑ x ∈ s, c x * (A.updateRow i (v x)).det := by
  induction s using Finset.induction with
  | empty =>
      have hzero := Matrix.det_updateRow_smul A i (0 : R) (0 : n → R)
      simpa using hzero
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]

end Multilinearity

section Valuation

variable {n κ K : Type*} [Fintype n] [DecidableEq n] [DecidableEq κ] [Field K]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- Valuation bound for a finite linear combination in one determinant column. -/
theorem valuation_det_updateCol_finset_sum_le
    (val : Valuation K Γ) (A : Matrix n n K) (j : n)
    (s : Finset κ) (c : κ → K) (v : κ → n → K) (ρ D : Γ)
    (hc : ∀ x ∈ s, val (c x) ≤ ρ)
    (hv : ∀ x ∈ s, val (A.updateCol j (v x)).det ≤ D) :
    val (A.updateCol j (∑ x ∈ s, c x • v x)).det ≤ ρ * D := by
  rw [det_updateCol_finset_sum]
  refine Valuation.map_sum_le val fun x hx => ?_
  rw [Valuation.map_mul]
  exact mul_le_mul' (hc x hx) (hv x hx)

/-- Sharp finite-supremum form of the column-combination valuation bound. -/
theorem valuation_det_updateCol_finset_sum_le_sup
    (val : Valuation K Γ) (A : Matrix n n K) (j : n)
    (s : Finset κ) (c : κ → K) (v : κ → n → K) :
    val (A.updateCol j (∑ x ∈ s, c x • v x)).det ≤
      (s.sup fun x => val (c x)) *
        (s.sup fun x => val (A.updateCol j (v x)).det) := by
  apply valuation_det_updateCol_finset_sum_le val A j s c v
  · intro x hx
    exact Finset.le_sup_of_le hx le_rfl
  · intro x hx
    exact Finset.le_sup_of_le hx le_rfl

/-- Valuation bound for a finite linear combination in one determinant row. -/
theorem valuation_det_updateRow_finset_sum_le
    (val : Valuation K Γ) (A : Matrix n n K) (i : n)
    (s : Finset κ) (c : κ → K) (v : κ → n → K) (ρ D : Γ)
    (hc : ∀ x ∈ s, val (c x) ≤ ρ)
    (hv : ∀ x ∈ s, val (A.updateRow i (v x)).det ≤ D) :
    val (A.updateRow i (∑ x ∈ s, c x • v x)).det ≤ ρ * D := by
  rw [det_updateRow_finset_sum]
  refine Valuation.map_sum_le val fun x hx => ?_
  rw [Valuation.map_mul]
  exact mul_le_mul' (hc x hx) (hv x hx)

/-- Sharp finite-supremum form of the row-combination valuation bound. -/
theorem valuation_det_updateRow_finset_sum_le_sup
    (val : Valuation K Γ) (A : Matrix n n K) (i : n)
    (s : Finset κ) (c : κ → K) (v : κ → n → K) :
    val (A.updateRow i (∑ x ∈ s, c x • v x)).det ≤
      (s.sup fun x => val (c x)) *
        (s.sup fun x => val (A.updateRow i (v x)).det) := by
  apply valuation_det_updateRow_finset_sum_le val A i s c v
  · intro x hx
    exact Finset.le_sup_of_le hx le_rfl
  · intro x hx
    exact Finset.le_sup_of_le hx le_rfl

end Valuation

end GaloisForLFunctions.HTGeometry
