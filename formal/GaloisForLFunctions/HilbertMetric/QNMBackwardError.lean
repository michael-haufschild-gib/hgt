import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-!
# Exact generalized eigenpair backward error

The rank-one perturbation mechanism behind equations (31)--(32) of Al Sheikh--Jaramillo,
* A geometric approach to QNMs in optics*, arXiv:2607.25133. This supplies the missing
optimal-correction direction alongside the corpus norm-resolvent pseudospectrum.
No normality, finite-dimensionality, invertibility, or eigenvector hypothesis is assumed.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Rank-at-most-one perturbation correcting the residual of a generalized eigenpair.
The zero vector gives the zero correction. -/
def qnmBackwardCorrection (A B : E →L[𝕜] E) (z : 𝕜) (v : E) : E →L[𝕜] E :=
  (inner 𝕜 v v)⁻¹ • InnerProductSpace.rankOne 𝕜 (z • B v - A v) v

/-- Every trial vector satisfies the perturbed generalized eigen-equation exactly. -/
theorem qnmBackwardCorrection_exact (A B : E →L[𝕜] E) (z : 𝕜) (v : E) :
    (A + qnmBackwardCorrection A B z v) v = z • B v := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : inner 𝕜 v v ≠ 0 := inner_self_ne_zero.mpr hv
  change A v + (inner 𝕜 v v)⁻¹ •
    (inner 𝕜 v v • (z • B v - A v)) = z • B v
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  abel

/-- The correction norm is exactly the relative residual, including at the zero vector. -/
theorem norm_qnmBackwardCorrection (A B : E →L[𝕜] E) (z : 𝕜) (v : E) :
    ‖qnmBackwardCorrection A B z v‖ = ‖A v - z • B v‖ / ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, qnmBackwardCorrection]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [qnmBackwardCorrection, norm_smul, norm_inv, inner_self_eq_norm_sq_to_K, norm_pow,
    RCLike.norm_ofReal, abs_norm, InnerProductSpace.norm_rankOne]
  rw [norm_sub_rev]
  field_simp

/-- The constructed correction attains the least operator norm among all exact corrections. -/
theorem qnmBackwardError_isLeast (A B : E →L[𝕜] E) (z : 𝕜) (v : E) :
    IsLeast {r : ℝ | ∃ D : E →L[𝕜] E, (A + D) v = z • B v ∧ ‖D‖ = r}
      (‖A v - z • B v‖ / ‖v‖) := by
  constructor
  · exact ⟨qnmBackwardCorrection A B z v, qnmBackwardCorrection_exact A B z v,
      norm_qnmBackwardCorrection A B z v⟩
  · rintro r ⟨D, hD, rfl⟩
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hres : A v - z • B v = -D v := by
      have h : A v + D v = z • B v := hD
      rw [← h]
      abel
    rw [hres, norm_neg, div_le_iff₀ hn]
    exact D.le_opNorm v

/-- Relative residual and smallest-perturbation descriptions agree for every real tolerance.
A nonzero-vector condition must additionally be imposed to define a pseudospectrum. -/
theorem qnm_relativeResidual_iff_perturbation
    (A B : E →L[𝕜] E) (z : 𝕜) (v : E) (ε : ℝ) :
    ‖A v - z • B v‖ / ‖v‖ < ε ↔
      ∃ D : E →L[𝕜] E, (A + D) v = z • B v ∧ ‖D‖ < ε := by
  constructor
  · intro h
    exact ⟨qnmBackwardCorrection A B z v, qnmBackwardCorrection_exact A B z v,
      (norm_qnmBackwardCorrection A B z v).trans_lt h⟩
  · rintro ⟨D, hD, hnorm⟩
    exact ((qnmBackwardError_isLeast A B z v).2 ⟨D, hD, rfl⟩).trans_lt hnorm

/-- Relative quasimodes exclude the zero vector explicitly. -/
def qnmQuasimodeSet (A B : E →L[𝕜] E) (ε : ℝ) : Set 𝕜 :=
  {z | ∃ v : E, v ≠ 0 ∧ ‖A v - z • B v‖ / ‖v‖ < ε}

/-- Without normalization or exclusion of zero, every parameter qualifies at positive tolerance. -/
theorem qnmUnnormalizedResidualSet_eq_univ (A B : E →L[𝕜] E) (ε : ℝ) :
    {z : 𝕜 | ∃ v : E, ‖A v - z • B v‖ < |ε| + 1} = Set.univ := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨0, ?_⟩
    simp only [map_zero, smul_zero, sub_zero, norm_zero]
    positivity

/-- The relative residual characterizes exact point eigenvalues after a small perturbation. -/
theorem qnmQuasimodeSet_eq_perturbedEigenvectors (A B : E →L[𝕜] E) (ε : ℝ) :
    qnmQuasimodeSet A B ε =
      {z | ∃ D : E →L[𝕜] E, ‖D‖ < ε ∧ ∃ v : E, v ≠ 0 ∧ (A + D) v = z • B v} := by
  ext z
  constructor
  · rintro ⟨v, hv, hr⟩
    obtain ⟨D, hD, hn⟩ := (qnm_relativeResidual_iff_perturbation A B z v ε).mp hr
    exact ⟨D, hn, v, hv, hD⟩
  · rintro ⟨D, hn, v, hv, hD⟩
    exact ⟨v, hv, (qnm_relativeResidual_iff_perturbation A B z v ε).mpr ⟨D, hD, hn⟩⟩

/-- Unit normalization and the homogeneous relative-residual formulation agree. -/
theorem qnmQuasimodeSet_eq_unitResidual (A B : E →L[𝕜] E) (ε : ℝ) :
    qnmQuasimodeSet A B ε = {z | ∃ v : E, ‖v‖ = 1 ∧ ‖A v - z • B v‖ < ε} := by
  ext z
  constructor
  · rintro ⟨v, hv, hr⟩
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let c : 𝕜 := (RCLike.ofReal ‖v‖)⁻¹
    refine ⟨c • v, ?_, ?_⟩
    · simp [c, norm_smul, hn]
    · have heq : A (c • v) - z • B (c • v) = c • (A v - z • B v) := by
        simp only [map_smul, smul_sub]
        rw [smul_comm z c]
      rw [heq, norm_smul]
      simpa [c, RCLike.norm_ofReal, div_eq_mul_inv, mul_comm] using hr
  · rintro ⟨v, hv, hr⟩
    refine ⟨v, ?_, ?_⟩
    · intro hzero
      simp [hzero] at hv
    · simpa only [hv, div_one] using hr

end GaloisForLFunctions.HilbertMetric
