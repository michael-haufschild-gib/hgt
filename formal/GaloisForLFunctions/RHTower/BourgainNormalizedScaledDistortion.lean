/-
# Scaled coordinate distortion for Bourgain's normalized curve

The generic Gaussian perturbation theorem uses the inverse norm of the
two-base jet map followed by the anisotropic parabola dilation.  On scales
`0 < scale ≤ 1`, the inverse dilation has norm at most `scale⁻²`.  Combining
this with the uniform normalized jet inverse gives the physical Taylor-error
scale `D² ρ`.

In Bourgain's Theorem 1, `D` is the square root of the physical ball radius.
Consequently `D² (H/D)³` is exactly the source error `N K⁻³ᐟ²`.
-/
import GaloisForLFunctions.RHTower.BourgainNormalizedCoordinateDistortion
import GaloisForLFunctions.RHTower.BourgainGenericFrequencyPerturbation

namespace RHTower

noncomputable section

/-- The inverse anisotropic dilation is the same diagonal dilation at the
reciprocal scale. -/
theorem bourgainParabolaPhaseScaleContinuousLinearEquiv_symm_apply
    {scale : ℝ} (hscale : scale ≠ 0) (y : BourgainPhaseSpace) :
    (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).symm y =
      bourgainParabolaPhaseScale scale⁻¹ y := by
  apply (bourgainParabolaPhaseScaleContinuousLinearEquiv hscale).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    bourgainParabolaPhaseScaleContinuousLinearEquiv_apply]
  ext j
  fin_cases j <;>
    simp [bourgainParabolaPhaseScale, Matrix.cons_val, hscale]

/-- Pointwise inverse-dilation bound on a contracting scale. -/
theorem norm_bourgainParabolaPhaseScale_symm_le_inv_sq
    {scale : ℝ} (hscale0 : 0 < scale) (hscale1 : scale ≤ 1)
    (y : BourgainPhaseSpace) :
    ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale0.ne').symm y‖ ≤
      scale⁻¹ ^ (2 : ℕ) * ‖y‖ := by
  rw [bourgainParabolaPhaseScaleContinuousLinearEquiv_symm_apply]
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (sq_nonneg scale⁻¹) (norm_nonneg y))]
  intro j
  have hy (i : Fin 4) : ‖y i‖ ≤ ‖y‖ :=
    norm_apply_le_norm_bourgainPhaseSpace y i
  have hinv0 : 0 ≤ scale⁻¹ := inv_nonneg.mpr hscale0.le
  have hinv1 : 1 ≤ scale⁻¹ := (one_le_inv₀ hscale0).2 hscale1
  have hlin : scale⁻¹ ≤ scale⁻¹ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (scale⁻¹ - 1)]
  fin_cases j
  · change ‖scale⁻¹ * y 0‖ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hinv0]
    calc
      scale⁻¹ * ‖y 0‖ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y 0‖ :=
        mul_le_mul_of_nonneg_right hlin (norm_nonneg _)
      _ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y‖ :=
        mul_le_mul_of_nonneg_left (hy 0) (sq_nonneg _)
  · change ‖scale⁻¹ ^ (2 : ℕ) * y 1‖ ≤
      scale⁻¹ ^ (2 : ℕ) * ‖y‖
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hinv0]
    exact mul_le_mul_of_nonneg_left (hy 1) (sq_nonneg _)
  · change ‖scale⁻¹ * y 2‖ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hinv0]
    calc
      scale⁻¹ * ‖y 2‖ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y 2‖ :=
        mul_le_mul_of_nonneg_right hlin (norm_nonneg _)
      _ ≤ scale⁻¹ ^ (2 : ℕ) * ‖y‖ :=
        mul_le_mul_of_nonneg_left (hy 2) (sq_nonneg _)
  · change ‖scale⁻¹ ^ (2 : ℕ) * y 3‖ ≤
      scale⁻¹ ^ (2 : ℕ) * ‖y‖
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hinv0]
    exact mul_le_mul_of_nonneg_left (hy 3) (sq_nonneg _)

/-- Operator-norm form of the inverse anisotropic dilation bound. -/
theorem opNorm_bourgainParabolaPhaseScale_symm_le_inv_sq
    {scale : ℝ} (hscale0 : 0 < scale) (hscale1 : scale ≤ 1) :
    ‖((bourgainParabolaPhaseScaleContinuousLinearEquiv hscale0.ne').symm :
        BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
      scale⁻¹ ^ (2 : ℕ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  exact norm_bourgainParabolaPhaseScale_symm_le_inv_sq hscale0 hscale1

/-- Natural independent-parabola frequencies have sup norm at most `H²`. -/
theorem norm_bourgainIndependentParabolaNaturalScale_le
    {H : ℕ} (hH : 0 < H) :
    ‖bourgainIndependentParabolaNaturalScale H‖ ≤
      (H : ℝ) ^ (2 : ℕ) := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg (H : ℝ))]
  intro j
  fin_cases j <;>
    simp [bourgainIndependentParabolaNaturalScale, Matrix.cons_val] <;>
    nlinarith [sq_nonneg ((H : ℝ) - 1)]

/-- Uniform inverse bound for the full scaled normalized jet map. -/
theorem opNorm_bourgainNormalizedScaledPhaseCoordinate_inverse_le
    {q scale a b : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (hscale0 : 0 < scale) (hscale1 : scale ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    let hunit :=
      isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
        hq hq1 ha hb hab
    ‖((bourgainGenericScaledPhaseContinuousLinearEquiv
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        hscale0.ne' hunit).symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
      1048576000 * scale⁻¹ ^ (2 : ℕ) := by
  dsimp only
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 ha hb hab
  let A :=
    bourgainGenericPhaseCoordinateContinuousLinearEquiv
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) a b hunit
  let S :=
    bourgainParabolaPhaseScaleContinuousLinearEquiv hscale0.ne'
  let E := A.trans S
  have hA :
      ‖(A.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
        1048576000 := by
    exact opNorm_bourgainNormalizedPhaseCoordinate_inverse_le
      hq hq1 ha hb hab
  have hS :
      ‖(S.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
        scale⁻¹ ^ (2 : ℕ) := by
    exact opNorm_bourgainParabolaPhaseScale_symm_le_inv_sq
      hscale0 hscale1
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (sq_nonneg _))
  intro x
  change ‖A.symm (S.symm x)‖ ≤
    (1048576000 * scale⁻¹ ^ (2 : ℕ)) * ‖x‖
  calc
    ‖A.symm (S.symm x)‖ ≤
        ‖(A.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ *
          ‖S.symm x‖ :=
      (A.symm :
        BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace).le_opNorm _
    _ ≤ 1048576000 * (scale⁻¹ ^ (2 : ℕ) * ‖x‖) := by
      gcongr
      exact norm_bourgainParabolaPhaseScale_symm_le_inv_sq
        hscale0 hscale1 x
    _ = (1048576000 * scale⁻¹ ^ (2 : ℕ)) * ‖x‖ := by ring

/-- The generic perturbation radius is controlled by the physical
Taylor-error scale `D²ρ`. -/
theorem bourgainNormalizedFrequencyPerturbationSize_le
    {H : ℕ} (hH : 0 < H)
    {q D a b ρ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (hD : 0 < D) (hHD : (H : ℝ) ≤ D)
    (hρ : 0 ≤ ρ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : 1 / 4 ≤ b - a) :
    let hscale : (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
    let hunit :=
      isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
        hq hq1 ha hb hab
    let E :=
      bourgainGenericScaledPhaseContinuousLinearEquiv
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) hscale hunit
    bourgainGenericFrequencyPerturbationSize
        (bourgainIndependentParabolaNaturalScale H)
        ‖(E.symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ρ ≤
      4194304000 * D ^ (2 : ℕ) * ρ := by
  dsimp only
  let scale : ℝ := (H : ℝ) / D
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 ha hb hab
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q)
      (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne') hunit
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hscale0 : 0 < scale := by
    dsimp [scale]
    positivity
  have hscale1 : scale ≤ 1 := by
    exact (div_le_one hD).2 hHD
  have hE :
      ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ≤
        1048576000 * scale⁻¹ ^ (2 : ℕ) := by
    exact opNorm_bourgainNormalizedScaledPhaseCoordinate_inverse_le
      hq hq1 hscale0 hscale1 ha hb hab
  have hscaleInv :
      scale⁻¹ = D / (H : ℝ) := by
    dsimp [scale]
    field_simp
  unfold bourgainGenericFrequencyPerturbationSize
  calc
    4 * ‖bourgainIndependentParabolaNaturalScale H‖ *
          ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ * ρ ≤
        4 * (H : ℝ) ^ (2 : ℕ) *
          ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ * ρ := by
      gcongr
      exact norm_bourgainIndependentParabolaNaturalScale_le hH
    _ ≤ 4 * (H : ℝ) ^ (2 : ℕ) *
          (1048576000 * scale⁻¹ ^ (2 : ℕ)) * ρ := by
      gcongr
    _ = 4194304000 * D ^ (2 : ℕ) * ρ := by
      rw [hscaleInv]
      field_simp
      ring

end

end RHTower
