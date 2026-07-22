import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Field-generic finite modal Hankel rank

An observed packet with `d` modes has values

`m n = ∑ a : Fin d, weight a * node a ^ n`.

Over any field, the polynomial whose roots are the nodes supplies a nonzero kernel vector for the
leading Hankel block in size `d+1`.  Its determinant therefore vanishes.  The complex specialization
directly covers sampled damped oscillations and quasinormal-mode ringdown signals; no temporal
interpretation is needed.

This strictly enlarges the real-node interface in `FiniteSpectralHankelRank`: complex masses and
nodes permit decay and phase in one modal coordinate.
-/

open Polynomial
open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- Hankel matrix of a sequence over an arbitrary coefficient type. -/
def algebraicHankelMatrix {K : Type*}
    (s : ℕ → K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => s ((i : ℕ) + (j : ℕ))

/-- A finite modal packet over a commutative semiring. -/
def finiteModalSequence {K : Type*} [CommSemiring K] {d : ℕ}
    (weight node : Fin d → K) (n : ℕ) : K :=
  ∑ i, weight i * node i ^ n

/-- A sequence has a modal presentation of width at most `d`. -/
def FiniteModalWidthAtMost {K : Type*} [CommSemiring K]
    (d : ℕ) (m : ℕ → K) : Prop :=
  ∃ weight node : Fin d → K, m = finiteModalSequence weight node

/-- The node polynomial supplies a nonzero kernel vector for the first oversized Hankel block. -/
theorem algebraicHankelMatrix_mulVec_nodePolynomial_eq_zero
    {K : Type*} [Field K] {d : ℕ} (weight node : Fin d → K) :
    algebraicHankelMatrix (finiteModalSequence weight node) (d + 1) *ᵥ
        (fun j : Fin (d + 1) ↦
          (∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))).coeff (j : ℕ)) = 0 := by
  let p : Polynomial K := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ ↦ Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ ↦ Polynomial.monic_X_sub_C (node i))]
    simp
  have hroot : ∀ i : Fin d, p.eval (node i) = 0 := by
    intro i
    rw [show p = ∏ k : Fin d, (Polynomial.X - Polynomial.C (node k)) by rfl,
      Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  funext r
  simp only [Matrix.mulVec, algebraicHankelMatrix, Pi.zero_apply]
  change ∑ j : Fin (d + 1),
      finiteModalSequence weight node ((r : ℕ) + (j : ℕ)) * p.coeff (j : ℕ) = 0
  calc
    ∑ j : Fin (d + 1),
        finiteModalSequence weight node ((r : ℕ) + (j : ℕ)) * p.coeff (j : ℕ) =
        ∑ j : Fin (d + 1), ∑ i : Fin d,
          (weight i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteModalSequence, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = ∑ i : Fin d, ∑ j : Fin (d + 1),
          (weight i * node i ^ (r : ℕ)) * (p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, (weight i * node i ^ (r : ℕ)) *
          (∑ j : Fin (d + 1), p.coeff (j : ℕ) * node i ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin d, (weight i * node i ^ (r : ℕ)) * p.eval (node i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
      rw [Finset.sum_range fun j ↦ p.coeff j * node i ^ j]
    _ = 0 := by simp [hroot]

/-- **Finite modal rank law.**  A width-`d` modal packet over a field has singular Hankel block in
size `d+1`. -/
theorem det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero
    {K : Type*} [Field K] {d : ℕ} (weight node : Fin d → K) :
    (algebraicHankelMatrix (finiteModalSequence weight node) (d + 1)).det = 0 := by
  let p : Polynomial K := ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i))
  have hpmon : p.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ ↦ Polynomial.monic_X_sub_C (node i))
  have hpdeg : p.natDegree = d := by
    rw [show p = ∏ i : Fin d, (Polynomial.X - Polynomial.C (node i)) by rfl,
      Polynomial.natDegree_prod_of_monic _ _
        (fun i _ ↦ Polynomial.monic_X_sub_C (node i))]
    simp
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (algebraicHankelMatrix_mulVec_nodePolynomial_eq_zero weight node)
    (i := Fin.last d)
  change p.coeff d ∈ nonZeroDivisors K
  have hp1 : p.coeff d = 1 := by
    rw [← hpdeg]
    exact hpmon.coeff_natDegree
  simp [hp1]

/-- The determinant obstruction in representation form. -/
theorem det_algebraicHankelMatrix_succ_eq_zero_of_finiteModalWidthAtMost
    {K : Type*} [Field K] {d : ℕ} {m : ℕ → K}
    (hm : FiniteModalWidthAtMost d m) :
    (algebraicHankelMatrix m (d + 1)).det = 0 := by
  obtain ⟨weight, node, rfl⟩ := hm
  exact det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero weight node

/-- A nonzero Hankel determinant excludes every modal model of the corresponding width. -/
theorem not_finiteModalWidthAtMost_of_det_ne_zero
    {K : Type*} [Field K] {d : ℕ} {m : ℕ → K}
    (hdet : (algebraicHankelMatrix m (d + 1)).det ≠ 0) :
    ¬ FiniteModalWidthAtMost d m := by
  intro hm
  exact hdet (det_algebraicHankelMatrix_succ_eq_zero_of_finiteModalWidthAtMost hm)

/-- A finite modal Hankel matrix factors through its Vandermonde observation matrix. -/
theorem algebraicHankelMatrix_finiteModalSequence_eq_vandermonde
    {K : Type*} [CommRing K] {d : ℕ} (weight node : Fin d → K) :
    algebraicHankelMatrix (finiteModalSequence weight node) d =
      (Matrix.vandermonde node)ᵀ * Matrix.diagonal weight * Matrix.vandermonde node := by
  ext i j
  simp [algebraicHankelMatrix, finiteModalSequence, Matrix.mul_apply,
    Matrix.vandermonde_apply, Matrix.diagonal_apply, pow_add]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Exact determinant value of an active `d`-mode packet. -/
theorem det_algebraicHankelMatrix_finiteModalSequence
    {K : Type*} [CommRing K] {d : ℕ} (weight node : Fin d → K) :
    (algebraicHankelMatrix (finiteModalSequence weight node) d).det =
      (Matrix.vandermonde node).det ^ 2 * ∏ i, weight i := by
  rw [algebraicHankelMatrix_finiteModalSequence_eq_vandermonde,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- Distinct nodes with nonzero amplitudes make the maximal active modal block nonsingular. -/
theorem det_algebraicHankelMatrix_finiteModalSequence_ne_zero
    {K : Type*} [Field K] {d : ℕ} {weight node : Fin d → K}
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0) :
    (algebraicHankelMatrix (finiteModalSequence weight node) d).det ≠ 0 := by
  rw [det_algebraicHankelMatrix_finiteModalSequence]
  exact mul_ne_zero (pow_ne_zero 2 (Matrix.det_vandermonde_ne_zero_iff.mpr hnode))
    (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hweight i)

/-- **Exact noiseless mode-count certificate.**  The active block is nonsingular and the next
block is singular. -/
theorem finiteModalSequence_exact_hankel_mode_count
    {K : Type*} [Field K] {d : ℕ} {weight node : Fin d → K}
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0) :
    (algebraicHankelMatrix (finiteModalSequence weight node) d).det ≠ 0 ∧
      (algebraicHankelMatrix (finiteModalSequence weight node) (d + 1)).det = 0 :=
  ⟨det_algebraicHankelMatrix_finiteModalSequence_ne_zero hnode hweight,
    det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero weight node⟩

end

end HTGeometry
