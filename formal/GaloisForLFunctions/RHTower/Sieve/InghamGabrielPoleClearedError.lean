import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielDualPower
import Mathlib.Analysis.Complex.Hadamard

open Complex Set

namespace RHTower.Sieve

noncomputable section

/-- Gaussian-regularized, pole-cleared mollified zeta error. The residue-unit numerator removes the
zeta pole at `1`; division by `z` is harmless on Route T's strip `Re z >= 1/2`. -/
def inghamGabrielPoleClearedError (X : ℕ) (kappa T : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2) *
    ((zetaResidueUnit z * inghamMollifier X z - (z - 1)) / z)

theorem analyticAt_inghamGabrielPoleClearedError
    (X : ℕ) (kappa T : ℝ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (inghamGabrielPoleClearedError X kappa T) z := by
  have hgauss : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp ((kappa : ℂ) * (w / (T : ℂ)) ^ 2)) z :=
    (analyticAt_const.mul ((analyticAt_id.div_const).pow 2)).cexp
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => zetaResidueUnit w * inghamMollifier X w - (w - 1)) z :=
    ((analyticAt_zetaResidueUnit z).mul (analyticAt_inghamMollifier X z)).sub
      (analyticAt_id.sub analyticAt_const)
  change AnalyticAt ℂ (fun w : ℂ =>
    Complex.exp ((kappa : ℂ) * (w / (T : ℂ)) ^ 2) *
      ((zetaResidueUnit w * inghamMollifier X w - (w - 1)) / w)) z
  have heq :
      (fun w : ℂ =>
        Complex.exp ((kappa : ℂ) * (w / (T : ℂ)) ^ 2) *
          ((zetaResidueUnit w * inghamMollifier X w - (w - 1)) / w)) =
        (fun w : ℂ => Complex.exp ((kappa : ℂ) * (w / (T : ℂ)) ^ 2)) *
          ((fun w : ℂ => zetaResidueUnit w * inghamMollifier X w - (w - 1)) / id) := by
    funext w
    rfl
  rw [heq]
  exact hgauss.mul (hnum.div analyticAt_id hz)

/-- Exact agreement with the raw mollified error away from the zeta pole and the auxiliary point
`0`. -/
theorem inghamGabrielPoleClearedError_eq_raw
    (X : ℕ) (kappa T : ℝ) {z : ℂ} (hz1 : z ≠ 1) :
    inghamGabrielPoleClearedError X kappa T z =
      Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2) *
        ((z - 1) / z) *
          (riemannZeta z * inghamMollifier X z - 1) := by
  have hG : zetaResidueUnit z = (z - 1) * riemannZeta z := by
    simp [zetaResidueUnit, Function.update_of_ne hz1]
  rw [inghamGabrielPoleClearedError, hG]
  ring

private theorem closure_fixedGabrielStrip_subset_closed :
    closure (Complex.HadamardThreeLines.verticalStrip
      (1 / 2) inghamPowerSavingRightEdge) ⊆
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  · exact isClosed_Icc.preimage continuous_re

private theorem ne_zero_of_mem_fixedGabrielClosedStrip {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge) : z ≠ 0 := by
  intro hzero
  subst z
  norm_num [Complex.HadamardThreeLines.verticalClosedStrip] at hz

/-- The regularized error has exactly the strip regularity required by Hadamard three-lines. -/
theorem diffContOnCl_inghamGabrielPoleClearedError_fixedStrip
    (X : ℕ) (kappa T : ℝ) :
    DiffContOnCl ℂ (inghamGabrielPoleClearedError X kappa T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) inghamPowerSavingRightEdge) := by
  constructor
  · intro z hz
    exact (analyticAt_inghamGabrielPoleClearedError X kappa T
      (ne_zero_of_mem_fixedGabrielClosedStrip
        ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (analyticAt_inghamGabrielPoleClearedError X kappa T
      (ne_zero_of_mem_fixedGabrielClosedStrip
        (closure_fixedGabrielStrip_subset_closed hz))).continuousAt.continuousWithinAt

/-- Exact Gaussian modulus in Cartesian coordinates. -/
theorem norm_inghamGabrielGaussian (kappa T : ℝ) {z : ℂ} (hT : T ≠ 0) :
    ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ =
      Real.exp (kappa * (z.re ^ 2 - z.im ^ 2) / T ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [div_eq_mul_inv, pow_two, Complex.mul_re]
  field_simp [hT]

/-- On a vertical line the Gabriel Gaussian splits into a fixed abscissa factor and genuine
Gaussian decay in height. -/
theorem norm_inghamGabrielGaussian_vertical
    (kappa T sigma t : ℝ) (hT : T ≠ 0) :
    ‖Complex.exp ((kappa : ℂ) *
      ((((sigma : ℂ) + (t : ℂ) * I) / (T : ℂ)) ^ 2))‖ =
      Real.exp (kappa * sigma ^ 2 / T ^ 2) *
        Real.exp (-kappa * t ^ 2 / T ^ 2) := by
  rw [norm_inghamGabrielGaussian kappa T hT, ← Real.exp_add]
  congr 1
  simp
  field_simp [hT]
  ring

/-- Pole-clearing factor `(z-1)/z` is contractive precisely on the half-plane used by Gabriel. -/
theorem norm_sub_one_le_norm_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖z - 1‖ ≤ ‖z‖ := by
  have hsq : ‖z - 1‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg (z - 1), norm_nonneg z]

/-- Pole clearing costs no modulus on the full fixed Gabriel strip. -/
theorem norm_inghamGabrielPoleClearedError_le_raw
    (X : ℕ) (kappa T : ℝ) {z : ℂ}
    (hzhalf : 1 / 2 ≤ z.re) (hz1 : z ≠ 1) :
    ‖inghamGabrielPoleClearedError X kappa T z‖ ≤
      ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ *
        ‖riemannZeta z * inghamMollifier X z - 1‖ := by
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    norm_num at hzhalf
  rw [inghamGabrielPoleClearedError_eq_raw X kappa T hz1,
    norm_mul, norm_mul, norm_div]
  have hratio : ‖z - 1‖ / ‖z‖ ≤ 1 := (div_le_one (norm_pos_iff.mpr hz0)).mpr
    (norm_sub_one_le_norm_of_half_le_re hzhalf)
  have hgauss : 0 ≤ ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ := norm_nonneg _
  have hraw : 0 ≤ ‖riemannZeta z * inghamMollifier X z - 1‖ := norm_nonneg _
  calc
    ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ *
          (‖z - 1‖ / ‖z‖) * ‖riemannZeta z * inghamMollifier X z - 1‖ ≤
        ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ * 1 *
          ‖riemannZeta z * inghamMollifier X z - 1‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hgauss) hraw
    _ = ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ *
        ‖riemannZeta z * inghamMollifier X z - 1‖ := by ring

/-- On the interpolation center line, reversing pole clearing costs exactly at most `7/3`. -/
theorem norm_fixedGabrielCenter_le_seven_thirds_mul_sub_one (t : ℝ) :
    ‖(inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I‖ ≤
      (7 / 3 : ℝ) * ‖(inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I - 1‖ := by
  have hsq : ‖(inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I‖ ^ 2 ≤
      ((7 / 3 : ℝ) * ‖(inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I - 1‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    norm_num [Complex.normSq_apply, inghamFixedGabrielSigma]
    nlinarith [sq_nonneg t]
  have hright : 0 ≤ (7 / 3 : ℝ) *
      ‖(inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I - 1‖ := by positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).mp hsq

/-- On `|t| <= T`, inverse Gaussian cost at the interpolation center is at most `exp kappa`. -/
theorem inv_norm_inghamGabrielGaussian_center_le_exp
    {kappa T t : ℝ} (hkappa : 0 ≤ kappa) (hT : 0 < T) (ht : |t| ≤ T) :
    (‖Complex.exp ((kappa : ℂ) *
      ((((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) / (T : ℂ)) ^ 2))‖)⁻¹ ≤
      Real.exp kappa := by
  rw [norm_inghamGabrielGaussian_vertical kappa T inghamFixedGabrielSigma t hT.ne',
    mul_inv, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htSq : t ^ 2 ≤ T ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_pos hT]
    exact ht)
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  norm_num [inghamFixedGabrielSigma]
  have hquot : kappa * t ^ 2 / T ^ 2 ≤ kappa := by
    apply (div_le_iff₀ hT2).mpr
    exact mul_le_mul_of_nonneg_left htSq hkappa
  have hleft : -(kappa * (49 / 100 : ℝ) / T ^ 2) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (mul_nonneg hkappa (by norm_num)) hT2.le)
  have hright : 0 ≤ kappa - kappa * t ^ 2 / T ^ 2 := sub_nonneg.mpr hquot
  simpa only [sub_eq_add_neg, neg_div] using hleft.trans hright

/-- Raw center-line error is quantitatively recovered from the Gaussian pole-cleared field on the
central height window. -/
theorem norm_inghamRawError_center_le_regularized
    (X : ℕ) {kappa T t : ℝ} (hkappa : 0 ≤ kappa) (hT : 0 < T) (ht : |t| ≤ T) :
    ‖riemannZeta ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I) - 1‖ ≤
      (7 / 3 : ℝ) * Real.exp kappa *
        ‖inghamGabrielPoleClearedError X kappa T
          ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖ := by
  let z : ℂ := (inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [z, inghamFixedGabrielSigma] at hre
  have hz1 : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [z, inghamFixedGabrielSigma] at hre
  have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hratio : ‖z‖ / ‖z - 1‖ ≤ 7 / 3 := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hzm1)).mpr
    simpa only [z] using norm_fixedGabrielCenter_le_seven_thirds_mul_sub_one t
  have hginv :
      (‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖)⁻¹ ≤ Real.exp kappa := by
    simpa only [z] using
      inv_norm_inghamGabrielGaussian_center_le_exp hkappa hT ht
  have heq := congrArg norm
    (inghamGabrielPoleClearedError_eq_raw X kappa T hz1)
  rw [norm_mul, norm_mul, norm_div] at heq
  have hsolve :
      ‖riemannZeta z * inghamMollifier X z - 1‖ =
        (‖z‖ / ‖z - 1‖) *
          (‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖)⁻¹ *
            ‖inghamGabrielPoleClearedError X kappa T z‖ := by
    rw [heq]
    field_simp [norm_ne_zero_iff.mpr hz0, norm_ne_zero_iff.mpr hzm1,
      norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)]
  change ‖riemannZeta z * inghamMollifier X z - 1‖ ≤
    (7 / 3 : ℝ) * Real.exp kappa * ‖inghamGabrielPoleClearedError X kappa T z‖
  rw [hsolve]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hratio hginv (inv_nonneg.mpr (norm_nonneg _)) (by norm_num))
    (norm_nonneg _)

end

end RHTower.Sieve
