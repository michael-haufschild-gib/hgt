import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianHorizonAdmission
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Analysis.Normed.Group.Tannery

/-! # A summable envelope in the original Xi divisor norm -/

open Complex Filter Topology
noncomputable section
namespace RHTower
open DeningerMeyerGaussianGreen

/-- The actual Gaussian source absorbs the full polynomial resolvent cost. -/
theorem summable_deningerGaussian_polynomial_envelope_sq :
    Summable (fun q : XiZeroCopy =>
      ((1+|(q.1 : ℂ).im|)^2 * ‖reflectedGaussianHorizonGrade q‖)^2) := by
  let τ : ℝ := 2*reflectedGaussianHorizonTime
  have hτ : 0 < τ := mul_pos (by norm_num) reflectedGaussianHorizonTime_pos
  have h0 : Summable (fun q : XiZeroCopy => ‖xiGaussianHeatTerm τ q‖) :=
    summable_norm_iff.mpr (summable_xiGaussianHeatTerm hτ)
  have h2 : Summable (fun q : XiZeroCopy =>
      ‖(xiSpectralPoint q^2)^2 * xiGaussianHeatTerm τ q‖) :=
    summable_norm_iff.mpr (summable_xiGaussianHeatMonomialTerm hτ 2)
  apply Summable.of_norm_bounded ((h0.add h2).mul_left 8)
  intro q
  let t : ℝ := |(q.1 : ℂ).im|
  let N : ℝ := ‖xiSpectralPoint q‖^2
  have ht : 0 ≤ t := abs_nonneg _
  have hN : 0 ≤ N := sq_nonneg _
  have htN : t^2 ≤ N :=
    pow_le_pow_left₀ ht (by simpa [t,xiSpectralPoint] using Complex.abs_re_le_norm (xiSpectralPoint q)) 2
  have hpoly1 : (1+t)^2 ≤ 2*(1+N) := by nlinarith [sq_nonneg (t-1)]
  have hpoly : (1+t)^4 ≤ 8*(1+N^2) := by
    have hh := pow_le_pow_left₀ (sq_nonneg (1+t)) hpoly1 2
    nlinarith [sq_nonneg (N-1)]
  have hg : ‖reflectedGaussianHorizonGrade q‖^2 = ‖xiGaussianHeatTerm τ q‖ := by
    rw [reflectedGaussianHorizonGrade_eq_heat,norm_xiGaussianHeatTerm,norm_xiGaussianHeatTerm]
    rw [pow_two,← Real.exp_add]
    congr 1
    dsimp [τ]
    ring
  have hm : ‖(xiSpectralPoint q^2)^2*xiGaussianHeatTerm τ q‖ =
      N^2*‖xiGaussianHeatTerm τ q‖ := by rw [norm_mul,norm_pow,norm_pow]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ = (1+t)^4*‖xiGaussianHeatTerm τ q‖ := by
      rw [mul_pow,hg]
      dsimp [t]
      ring
    _ ≤ (8*(1+N^2))*‖xiGaussianHeatTerm τ q‖ := mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
    _ = _ := by rw [hm]; ring

/-- A common square-summable envelope upgrades coordinate convergence in the original Xi norm. -/
theorem deningerXi_tendsto_of_dominated
    {F : ℕ → XiDivisorL2} {g : XiDivisorL2} {b : XiZeroCopy → ℝ}
    (hsum : Summable (fun q => b q^2))
    (hF : ∀ n q, ‖F n q‖ ≤ b q) (hg : ∀ q, ‖g q‖ ≤ b q)
    (hpoint : ∀ q, Tendsto (fun n => F n q) atTop (𝓝 (g q))) :
    Tendsto F atTop (𝓝 g) := by
  have hpointSq (q : XiZeroCopy) :
      Tendsto (fun n => ‖F n q-g q‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa using (((hpoint q).sub_const (g q)).norm.pow 2)
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ q, ‖‖F n q-g q‖^2‖ ≤ 4*b q^2 := by
    filter_upwards with n q
    have hb0 : 0 ≤ b q := (norm_nonneg (g q)).trans (hg q)
    have hh : ‖F n q-g q‖ ≤ 2*b q := (norm_sub_le _ _).trans (by linarith [hF n q,hg q])
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (F n q-g q)]
  have htot := tendsto_tsum_of_dominated_convergence (hsum.mul_left 4) hpointSq hbound
  have heq (n : ℕ) : (∑' q : XiZeroCopy, ‖F n q-g q‖^2) = ‖F n-g‖^2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rfl
  have hnorm : Tendsto (fun n => ‖F n-g‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [heq,tsum_zero] using htot
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hnorm.sqrt

end RHTower
