/-
# Chen--Gupta--Li Lemma 4.1

This is the source large-value estimate for the literal weighted character
matrix.  A packet carries its finite rows, its bounded Dirichlet coefficients,
and the asserted lower value as certified data; the theorem has no
caller-supplied mathematical premise.  The finite Euclidean operator norm is
the source largest singular value.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCharacterGram
import GaloisForLFunctions.RHTower.ChenGuptaLiAffinePoisson

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RHTower

/-- Certified data in CGL Lemma 4.1.  The source condition
`|S_N(t, χ)| ≥ N^σ / 6` is part of the finite packet itself. -/
structure CGLLemma41Packet where
  length : CGLPositiveLength
  modulus : CGLPositiveModulus
  cutoff : CGLSmoothBump
  sigma : ℝ
  rowCount : ℕ
  rows : Fin rowCount → CGLCharacterDyadicRowData modulus.value
  coefficients : CGLCharacterDyadicBoundedCoefficients length.value
  large : ∀ r,
    ((length.value : ℝ) ^ sigma / 6) ≤
      ‖cglCharacterDyadicWeightedPolynomial length.value modulus.value
        (fun j => cutoff.value ((cglCharacterDyadicIndex length.value j : ℝ) / length.value))
        (rows r) coefficients.value‖

/-- The literal CGL smoothing weight `w(n/N)` on `N < n ≤ 2N`. -/
noncomputable def cglLemma41Weight (P : CGLLemma41Packet) (j : Fin P.length.value) : ℂ :=
  P.cutoff.value ((cglCharacterDyadicIndex P.length.value j : ℝ) / P.length.value)

/-- The source large-value threshold `N^σ / 6`, certified nonnegative. -/
noncomputable def cglLemma41Threshold (P : CGLLemma41Packet) : NNReal :=
  ⟨(P.length.value : ℝ) ^ P.sigma / 6, by positivity⟩

theorem cglLemma41Threshold_coe (P : CGLLemma41Packet) :
    (cglLemma41Threshold P : ℝ) = (P.length.value : ℝ) ^ P.sigma / 6 := rfl

theorem cglLemma41Threshold_sq (P : CGLLemma41Packet) :
    (cglLemma41Threshold P : ℝ) ^ 2 = (P.length.value : ℝ) ^ (2 * P.sigma) / 36 := by
  rw [cglLemma41Threshold_coe, div_pow]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast P.length.positive.le)]
  congr 1
  ring

/-- Every member of the certified packet is selected by the source threshold. -/
theorem cglLemma41_largeValues_eq_univ (P : CGLLemma41Packet) :
    cglCharacterDyadicWeightedLargeValues P.length.value P.modulus.value P.rowCount
      (cglLemma41Weight P) P.rows P.coefficients.value (cglLemma41Threshold P) = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro r
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · change (P.length.value : ℝ) ^ P.sigma / 6 ≤
      ‖cglCharacterDyadicWeightedPolynomial P.length.value P.modulus.value
        (fun j => P.cutoff.value ((cglCharacterDyadicIndex P.length.value j : ℝ) / P.length.value))
        (P.rows r) P.coefficients.value‖
    exact P.large r

/-- **CGL Lemma 4.1.** For the source matrix and every certified source
large-value packet, `|W| ≤ 36 N^(1-2σ) s₁(M)^2`. -/
theorem cglLemma41_source_bound (P : CGLLemma41Packet) :
    (P.rowCount : ℝ) ≤ 36 * (P.length.value : ℝ) ^ (1 - 2 * P.sigma) *
      ‖cglCharacterDyadicWeightedEvaluationOperator P.length.value P.modulus.value P.rowCount
        (cglLemma41Weight P) P.rows‖ ^ 2 := by
  have hbase := card_cglCharacterDyadicWeightedLargeValues_mul_sq_le_operator_bounded
    P.length.value P.modulus.value P.rowCount (cglLemma41Weight P) P.rows P.coefficients
      (cglLemma41Threshold P)
  rw [cglLemma41_largeValues_eq_univ, Finset.card_univ, cglLemma41Threshold_sq] at hbase
  have hbase' : (P.rowCount : ℝ) * ((P.length.value : ℝ) ^ (2 * P.sigma) / 36) ≤
      (P.length.value : ℝ) *
        ‖cglCharacterDyadicWeightedEvaluationOperator P.length.value P.modulus.value P.rowCount
          (cglLemma41Weight P) P.rows‖ ^ 2 := by
    simpa using hbase
  have hN : 0 < (P.length.value : ℝ) := by exact_mod_cast P.length.positive
  have hNpow : 0 < (P.length.value : ℝ) ^ (2 * P.sigma) := Real.rpow_pos_of_pos hN _
  calc
    (P.rowCount : ℝ) =
        ((P.rowCount : ℝ) * ((P.length.value : ℝ) ^ (2 * P.sigma) / 36)) *
          (36 / (P.length.value : ℝ) ^ (2 * P.sigma)) := by
      field_simp
    _ ≤ ((P.length.value : ℝ) *
        ‖cglCharacterDyadicWeightedEvaluationOperator P.length.value P.modulus.value P.rowCount
          (cglLemma41Weight P) P.rows‖ ^ 2) *
          (36 / (P.length.value : ℝ) ^ (2 * P.sigma)) := by
      exact mul_le_mul_of_nonneg_right hbase' (by positivity)
    _ = 36 * (P.length.value : ℝ) ^ (1 - 2 * P.sigma) *
        ‖cglCharacterDyadicWeightedEvaluationOperator P.length.value P.modulus.value P.rowCount
          (cglLemma41Weight P) P.rows‖ ^ 2 := by
      rw [Real.rpow_sub hN]
      norm_num
      field_simp

/-- Matrix-norm form of CGL Lemma 4.1, where Mathlib's `ℓ²` matrix norm is
the source largest singular value. -/
theorem cglLemma41_source_matrix_bound (P : CGLLemma41Packet) :
    (P.rowCount : ℝ) ≤ 36 * (P.length.value : ℝ) ^ (1 - 2 * P.sigma) *
      ‖cglCharacterDyadicWeightedEvaluationMatrix P.length.value P.modulus.value P.rowCount
        (cglLemma41Weight P) P.rows‖ ^ 2 := by
  rw [← norm_cglCharacterDyadicWeightedEvaluationOperator_eq_matrix]
  exact cglLemma41_source_bound P

end RHTower
