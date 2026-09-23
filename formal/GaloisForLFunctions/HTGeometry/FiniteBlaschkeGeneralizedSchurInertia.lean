import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension
import GaloisForLFunctions.HTGeometry.ProjectionMeasurementSurvival

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Abstract finite negative index -/

/-- A real quadratic form has exact finite negative index `n` when it has an `n`-dimensional
negative-definite subspace and no negative-definite subspace has larger dimension. -/
def HasExactNegativeIndex (q : H → ℝ) (n : ℕ) : Prop :=
  (∃ W : Submodule ℂ H, Module.finrank ℂ W = n ∧
    ∀ x ∈ W, x ≠ 0 → q x < 0) ∧
  ∀ W : Submodule ℂ H, (∀ x ∈ W, x ≠ 0 → q x < 0) →
    Module.finrank ℂ W ≤ n

/-- Adjoint defect of a contraction after subtracting an orthogonal model-space projection. -/
def projectedAdjointDefectForm (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (C : H →L[ℂ] H) (x : H) : ℝ :=
  ‖x‖ ^ (2 : ℕ) - ‖ContinuousLinearMap.adjoint C x‖ ^ (2 : ℕ) - ‖K.starProjection x‖ ^ (2 : ℕ)

lemma adjoint_norm_le_self_of_opNorm_le_one (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1) (x : H) :
    ‖ContinuousLinearMap.adjoint C x‖ ≤ ‖x‖ := by
  calc
    ‖ContinuousLinearMap.adjoint C x‖ ≤ ‖ContinuousLinearMap.adjoint C‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖C‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Every negative subspace of a positive adjoint defect minus a finite-dimensional projection
injects into the projection range. -/
theorem finrank_negativeSubspace_projectedAdjointDefect_le
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1)
    (W : Submodule ℂ H)
    (hW : ∀ x ∈ W, x ≠ 0 → projectedAdjointDefectForm K C x < 0) :
    Module.finrank ℂ W ≤ Module.finrank ℂ K := by
  let P : W →ₗ[ℂ] K := K.orthogonalProjectionOnto.toLinearMap.comp W.subtype
  have hPinj : Function.Injective P := by
    intro x y hxy
    have hPsub : P (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsub : x - y = 0 := by
      by_contra hsub0
      have hstar : K.starProjection ((x - y : W) : H) = 0 := by
        rw [Submodule.starProjection_apply]
        exact congrArg Subtype.val hPsub
      have hambient : (((x - y : W) : H)) ≠ 0 := by
        intro hzero
        exact hsub0 (Subtype.ext hzero)
      have hneg := hW (((x - y : W) : H)) (x - y).property hambient
      have hprojzero : ‖K.starProjection (((x - y : W) : H))‖ ^ (2 : ℕ) = 0 := by
        rw [hstar, norm_zero]
        norm_num
      rw [projectedAdjointDefectForm, hprojzero, sub_zero] at hneg
      have hadj := adjoint_norm_le_self_of_opNorm_le_one C hC (((x - y : W) : H))
      nlinarith [norm_nonneg (((x - y : W) : H)),
        norm_nonneg (ContinuousLinearMap.adjoint C (((x - y : W) : H)))]
    exact sub_eq_zero.mp hsub
  exact LinearMap.finrank_le_finrank_of_injective hPinj

/-- The projection range is a negative witness when compressed adjoint is injective. -/
theorem projectedAdjointDefectForm_negative_on_projectionRange
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (C : H →L[ℂ] H)
    (hinj : Function.Injective ((ContinuousLinearMap.adjoint C).toLinearMap.domRestrict K)) :
    ∀ x ∈ K, x ≠ 0 → projectedAdjointDefectForm K C x < 0 := by
  intro x hxK hx0
  have hstar : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hxK
  have hadj0 : ContinuousLinearMap.adjoint C x ≠ 0 := by
    intro hzero
    let y : K := ⟨x, hxK⟩
    have hy : ((ContinuousLinearMap.adjoint C).toLinearMap.domRestrict K) y = 0 := hzero
    have : y = 0 := hinj (by simpa using hy)
    exact hx0 (by simpa [y] using congrArg Subtype.val this)
  rw [projectedAdjointDefectForm, hstar]
  nlinarith [norm_pos_iff.mpr hadj0]

/-- Exact negative index of a contraction defect minus a finite-dimensional projection. -/
theorem projectedAdjointDefectForm_hasExactNegativeIndex
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1)
    (hinj : Function.Injective ((ContinuousLinearMap.adjoint C).toLinearMap.domRestrict K)) :
    HasExactNegativeIndex (projectedAdjointDefectForm K C) (Module.finrank ℂ K) := by
  constructor
  · exact ⟨K, rfl, projectedAdjointDefectForm_negative_on_projectionRange K C hinj⟩
  · intro W hW
    exact finrank_negativeSubspace_projectedAdjointDefect_le K C hC W hW

/-! ## Finite Blaschke specialization -/

/-- Hardy model space of a finite Blaschke product. -/
def finiteBlaschkeModelSpace (B : FiniteBlaschke) : Submodule ℂ HardyDisk :=
  Submodule.orthogonal
    (LinearMap.range ((hardyMul B.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk))

theorem finiteDimensional_finiteBlaschkeModelSpace (B : FiniteBlaschke) :
    FiniteDimensional ℂ (finiteBlaschkeModelSpace B) := by
  rcases B with ⟨k, a, c, hc0, hc1, hle⟩
  change FiniteDimensional ℂ
    (Submodule.orthogonal
      (LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)))
  exact (finrank_orthogonal_range_blaschkeOf k a hc0 hc1 hle).1

noncomputable instance (B : FiniteBlaschke) :
    FiniteDimensional ℂ (finiteBlaschkeModelSpace B) :=
  finiteDimensional_finiteBlaschkeModelSpace B

theorem finrank_finiteBlaschkeModelSpace (B : FiniteBlaschke) :
    Module.finrank ℂ (finiteBlaschkeModelSpace B) = B.deg := by
  rcases B with ⟨k, a, c, hc0, hc1, hle⟩
  change Module.finrank ℂ
    (Submodule.orthogonal
      (LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))) = k
  exact (finrank_orthogonal_range_blaschkeOf k a hc0 hc1 hle).2

/-- Generalized-Schur form attached to a Schur multiplier divided by a finite Blaschke product. -/
def finiteBlaschkeGeneralizedSchurForm (F : DiskMultiplier) (B : FiniteBlaschke) :
    HardyDisk → ℝ :=
  projectedAdjointDefectForm (finiteBlaschkeModelSpace B) (hardyMul F)

lemma norm_hardyMul_le (F : DiskMultiplier) : ‖hardyMul F‖ ≤ F.bd := by
  apply ContinuousLinearMap.opNorm_le_bound _ F.bd_nonneg
  intro x
  have hnorm : ‖hardyMul F x‖ ^ (2 : ℕ) ≤ (F.bd * ‖x‖) ^ (2 : ℕ) := by
    rw [hardyDisk_norm_sq, mul_pow]
    exact (hardyMulCoeff_bound F x).2
  have h1 : 0 ≤ ‖hardyMul F x‖ := norm_nonneg _
  have h2 : 0 ≤ F.bd * ‖x‖ := mul_nonneg F.bd_nonneg (norm_nonneg _)
  nlinarith

/-- Exact multiplicity-aware generalized-Schur index: a Schur numerator over a finite Blaschke
denominator has negative index equal to denominator degree whenever numerator adjoint does not kill
the denominator model space. -/
theorem finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1)
    (hinj : Function.Injective
      ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
        (finiteBlaschkeModelSpace B))) :
    HasExactNegativeIndex (finiteBlaschkeGeneralizedSchurForm F B) B.deg := by
  rw [← finrank_finiteBlaschkeModelSpace B]
  exact projectedAdjointDefectForm_hasExactNegativeIndex
    (finiteBlaschkeModelSpace B) (hardyMul F) ((norm_hardyMul_le F).trans hF) hinj

end GaloisForLFunctions.HTGeometry
