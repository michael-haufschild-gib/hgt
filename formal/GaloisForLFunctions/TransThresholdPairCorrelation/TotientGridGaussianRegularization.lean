import GaloisForLFunctions.TransThresholdPairCorrelation.GridFourierMultiplier
import GaloisForLFunctions.TransThresholdPairCorrelation.SincGapAndGaussianMargin
import GaloisForLFunctions.RHTower.CauchyBetaIntegral

/-!
# Gaussian regularization of the totient grid form factor

Blend the grid form factor with the GUE ramp using a Gaussian multiplier.
The exact unit-band data and spectral positivity survive the blend. On the
pair side, the origin mass above one supplies a narrow positive Gaussian;
the sinc deficit controls the remaining uniformly small correction.
-/

open Real Set MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Gaussian cutoff tending to one on every bounded frequency interval. -/
def gaussianFrequencyCutoff (R α : ℝ) : ℝ := exp (-π * (α / R) ^ 2)

/-- The Fourier transform of the frequency cutoff, for `R>0`. -/
def gaussianPairKernel (R x : ℝ) : ℝ := R * exp (-π * (R * x) ^ 2)

/-- The compact correction restoring the exact low-frequency ramp. -/
def gridRampCorrection (R α : ℝ) : ℝ :=
  triangleFn 1 α * (1 - gaussianFrequencyCutoff R α)

/-- A Gaussian blend with GUE preserves the prescribed unit-band data. -/
def regularizedTotientGridFormFactor (L : ℕ) (R α : ℝ) : ℝ :=
  gaussianFrequencyCutoff R α * totientGridFormFactor L α +
    (1 - gaussianFrequencyCutoff R α) * min |α| 1

theorem gaussianFrequencyCutoff_pos (R α : ℝ) : 0 < gaussianFrequencyCutoff R α := exp_pos _

theorem gaussianFrequencyCutoff_le_one (R α : ℝ) : gaussianFrequencyCutoff R α ≤ 1 := by
  apply exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _)

theorem regularizedTotientGridFormFactor_nonneg {L : ℕ} (hL : 1 ≤ L) (R α : ℝ) :
    0 ≤ regularizedTotientGridFormFactor L R α :=
  add_nonneg
    (mul_nonneg (gaussianFrequencyCutoff_pos R α).le (totientGridFormFactor_nonneg hL α))
    (mul_nonneg (sub_nonneg.mpr (gaussianFrequencyCutoff_le_one R α))
      (le_min (abs_nonneg _) zero_le_one))

theorem regularizedTotientGridFormFactor_eq_abs {L : ℕ} (hL : 1 ≤ L) (R : ℝ)
    {α : ℝ} (hα : |α| ≤ 1) : regularizedTotientGridFormFactor L R α = |α| := by
  rw [regularizedTotientGridFormFactor, totientGridFormFactor_eq_abs hL hα, min_eq_left hα]
  ring

theorem continuous_regularizedTotientGridFormFactor (L : ℕ) (R : ℝ) :
    Continuous (regularizedTotientGridFormFactor L R) := by
  have hχ : Continuous (gaussianFrequencyCutoff R) := by
    unfold gaussianFrequencyCutoff
    fun_prop
  exact (hχ.mul (continuous_totientGridFormFactor L)).add
    ((continuous_const.sub hχ).mul (continuous_abs.min continuous_const))

private theorem fourier_standardGaussian (ξ : ℝ) :
    𝓕 (fun t : ℝ => (exp (-π * t ^ 2) : ℂ)) ξ = (exp (-π * ξ ^ 2) : ℂ) := by
  have h := congrFun (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)) ξ
  simpa only [Complex.one_re, mul_one, Complex.one_cpow, one_div, one_mul, div_one,
    Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow] using h

/-- The Gaussian multiplier has the normalized positive Gaussian as its transform. -/
theorem fourier_gaussianFrequencyCutoff {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    𝓕 (fun α => (gaussianFrequencyCutoff R α : ℂ)) ξ = (gaussianPairKernel R ξ : ℂ) := by
  change 𝓕 (fun α : ℝ => (exp (-π * (α / R) ^ 2) : ℂ)) ξ = _
  rw [fourierIntegral_comp_div (fun t : ℝ => (exp (-π * t ^ 2) : ℂ)) R hR ξ,
    fourier_standardGaussian, Complex.real_smul]
  simp only [gaussianPairKernel, Complex.ofReal_mul]

theorem integrable_gaussianFrequencyCutoff {R : ℝ} (hR : 0 < R) :
    Integrable (gaussianFrequencyCutoff R) :=
  (integrable_exp_neg_mul_sq pi_pos).comp_div hR.ne'

theorem gaussianPairKernel_nonneg {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ gaussianPairKernel R x := mul_nonneg hR (exp_pos _).le

theorem integrable_gaussianPairKernel {R : ℝ} (hR : 0 < R) :
    Integrable (gaussianPairKernel R) := by
  have h := ((integrable_exp_neg_mul_sq pi_pos).comp_mul_left' hR.ne').const_mul R
  exact h

private theorem sqrt_gaussianScale {R : ℝ} (hR : 0 < R) :
    sqrt (π / (π * R ^ 2)) = 1 / R := by
  have he : π / (π * R ^ 2) = (1 / R) ^ 2 := by field_simp
  rw [he, sqrt_sq (one_div_nonneg.mpr hR.le)]

theorem integral_gaussianPairKernel {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, gaussianPairKernel R x) = 1 := by
  have hfun : gaussianPairKernel R = fun x => R * exp (-(π * R ^ 2) * x ^ 2) := by
    funext x
    unfold gaussianPairKernel
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian, sqrt_gaussianScale hR]
  field_simp

theorem integral_Ioi_gaussianPairKernel {R : ℝ} (hR : 0 < R) :
    (∫ x in Ioi (0 : ℝ), gaussianPairKernel R x) = 1 / 2 := by
  have hfun : gaussianPairKernel R = fun x => R * exp (-(π * R ^ 2) * x ^ 2) := by
    funext x
    unfold gaussianPairKernel
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian_Ioi, sqrt_gaussianScale hR]
  field_simp

theorem integral_Iic_gaussianPairKernel {R : ℝ} (hR : 0 < R) :
    (∫ x in Iic (0 : ℝ), gaussianPairKernel R x) = 1 / 2 := by
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi (integrable_gaussianPairKernel hR)
  rw [compl_Ioi, integral_Ioi_gaussianPairKernel hR, integral_gaussianPairKernel hR] at h
  linarith only [h]

theorem gridRampCorrection_nonneg (R α : ℝ) : 0 ≤ gridRampCorrection R α :=
  mul_nonneg (triangleFn_nonneg 1 α) (sub_nonneg.mpr (gaussianFrequencyCutoff_le_one R α))

theorem gridRampCorrection_le {R : ℝ} (_hR : 0 < R) (α : ℝ) :
    gridRampCorrection R α ≤ (π / R ^ 2) * triangleFn 1 α := by
  rcases le_or_gt |α| 1 with hα | hα
  · have hsq : α ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one α).mpr hα
    have hexp := Real.add_one_le_exp (-π * (α / R) ^ 2)
    have hu : π * (α / R) ^ 2 ≤ π / R ^ 2 := by
      rw [div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right pi_pos.le hsq) (sq_nonneg R)
    have hsmall : 1 - gaussianFrequencyCutoff R α ≤ π / R ^ 2 := by
      unfold gaussianFrequencyCutoff
      linarith only [hexp, hu]
    have h := mul_le_mul_of_nonneg_left hsmall (triangleFn_nonneg 1 α)
    simpa only [gridRampCorrection, mul_comm] using h
  · rw [gridRampCorrection, triangleFn_eq_zero one_pos hα.le, zero_mul, mul_zero]

theorem integrable_gridRampCorrection (R : ℝ) : Integrable (gridRampCorrection R) := by
  have htri : Integrable (triangleFn 1) := by
    simpa only [sub_zero] using integrable_triangleFn_sub one_pos 0
  have hi : Integrable (fun α => (1 - gaussianFrequencyCutoff R α) * triangleFn 1 α) := by
    apply htri.bdd_mul (c := 1)
    · have hχ : Continuous (gaussianFrequencyCutoff R) := by unfold gaussianFrequencyCutoff; fun_prop
      exact (continuous_const.sub hχ).aestronglyMeasurable
    · filter_upwards with α
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (gaussianFrequencyCutoff_le_one R α))]
      linarith only [(gaussianFrequencyCutoff_pos R α).le]
  change Integrable (fun α => triangleFn 1 α * (1 - gaussianFrequencyCutoff R α))
  simpa only [mul_comm] using hi


/-- The exact-ramp correction has a uniformly small Fourier transform. -/
theorem norm_fourier_gridRampCorrection_le {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    ‖𝓕 (fun α => (gridRampCorrection R α : ℂ)) ξ‖ ≤ π / R ^ 2 := by
  have htri : Integrable (triangleFn 1) := by
    simpa only [sub_zero] using integrable_triangleFn_sub one_pos 0
  have hphase (α : ℝ) : ‖Complex.exp ((-2 * π * α * ξ : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc
    ‖𝓕 (fun α => (gridRampCorrection R α : ℂ)) ξ‖ ≤
        ∫ α : ℝ, ‖(gridRampCorrection R α : ℂ)‖ := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simpa only [smul_eq_mul, norm_mul, hphase, one_mul] using
        (norm_integral_le_integral_norm (fun α : ℝ =>
          Complex.exp ((-2 * π * α * ξ : ℝ) * Complex.I) * (gridRampCorrection R α : ℂ)))
    _ = ∫ α : ℝ, gridRampCorrection R α := by
      apply integral_congr_ae
      filter_upwards with α
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gridRampCorrection_nonneg R α)]
    _ ≤ ∫ α : ℝ, (π / R ^ 2) * triangleFn 1 α :=
      integral_mono (integrable_gridRampCorrection R) (htri.const_mul _)
        (gridRampCorrection_le hR)
    _ = π / R ^ 2 := by
      rw [integral_const_mul, integral_triangleFn_real one_pos, mul_one]

private theorem one_sub_unitTriangle (α : ℝ) : 1 - triangleFn 1 α = min |α| 1 := by
  rcases le_or_gt |α| 1 with h | h
  · rw [triangleFn, div_one, max_eq_left (sub_nonneg.mpr h), min_eq_left h]
    ring
  · rw [triangleFn_eq_zero one_pos h.le, sub_zero, min_eq_right h.le]

theorem regularizedTotientGridFormFactor_sub_one (L : ℕ) (R α : ℝ) :
    regularizedTotientGridFormFactor L R α - 1 =
      gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1) - gridRampCorrection R α := by
  rw [regularizedTotientGridFormFactor, ← one_sub_unitTriangle, gridRampCorrection]
  ring

theorem integrable_regularizedTotientGridFormFactor_sub_one {L : ℕ} (hL : 1 ≤ L)
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun α => regularizedTotientGridFormFactor L R α - 1) := by
  have hχ := integrable_gaussianFrequencyCutoff hR
  have hb : Integrable (fun α => (totientGridFormFactor L α - 1) * gaussianFrequencyCutoff R α) := by
    apply hχ.bdd_mul (c := (L : ℝ) + 1)
    · exact ((continuous_totientGridFormFactor L).sub continuous_const).aestronglyMeasurable
    · filter_upwards with α
      rw [Real.norm_eq_abs, abs_le]
      have hn := totientGridFormFactor_nonneg hL α
      have hu := totientGridFormFactor_le hL α
      constructor <;> linarith only [hn, hu, Nat.cast_nonneg (α := ℝ) L]
  have h : Integrable (fun α => (totientGridFormFactor L α - 1) *
      gaussianFrequencyCutoff R α - gridRampCorrection R α) :=
    hb.sub (integrable_gridRampCorrection R)
  simpa only [regularizedTotientGridFormFactor_sub_one, mul_comm] using h

theorem fourier_gaussianPairKernel {R : ℝ} (hR : 0 < R) (ξ : ℝ) :
    𝓕 (fun x => (gaussianPairKernel R x : ℂ)) ξ = (gaussianFrequencyCutoff R ξ : ℂ) := by
  have hfun : (fun x => (gaussianPairKernel R x : ℂ)) =
      fun x => (R : ℂ) * (gaussianFrequencyCutoff (1 / R) x : ℂ) := by
    funext x
    have hd : x / (1 / R) = R * x := by field_simp
    simp only [gaussianPairKernel, gaussianFrequencyCutoff, Complex.ofReal_mul, hd]
  rw [hfun, fourierIntegral_const_mul, fourier_gaussianFrequencyCutoff (one_div_pos.mpr hR)]
  simp only [gaussianPairKernel, gaussianFrequencyCutoff, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast hR.ne' : (R : ℂ) ≠ 0), one_mul]
  congr 2
  rw [one_div_mul_eq_div]

/-- Positive background left after damping the central triangle. -/
def gaussianSincDeficit (L : ℕ) (R x : ℝ) : ℝ :=
  ∫ y : ℝ, gaussianPairKernel R y * (1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2)

theorem integrable_gaussianSincDeficit_integrand {R : ℝ} (hR : 0 < R) (L : ℕ) (x : ℝ) :
    Integrable (fun y => gaussianPairKernel R y * (1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2)) := by
  have h : Integrable (fun y => (1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2) * gaussianPairKernel R y) := by
    apply (integrable_gaussianPairKernel hR).bdd_mul (c := 1)
    · exact (by fun_prop : Continuous (fun y : ℝ => 1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2)).aestronglyMeasurable
    · filter_upwards with y
      have hsq : sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsq)]
      linarith only [sq_nonneg (sinc (π * (1 / (L : ℝ)) * (x + y)))]
  simpa only [mul_comm] using h

/-- Half of the Gaussian mass lies in a direction that increases the distance from zero. -/
theorem gaussianSincDeficit_quadratic_lower {R : ℝ} (hR : 0 < R) (L : ℕ) (x : ℝ) :
    (min ((π * (1 / (L : ℝ))) ^ 2) 1 / 24) * min (x ^ 2) 1 ≤
      gaussianSincDeficit L R x := by
  let a : ℝ := π * (1 / (L : ℝ))
  let c : ℝ := min (a ^ 2) 1 / 12
  let p : ℝ → ℝ := fun y => gaussianPairKernel R y * (1 - sinc (a * (x + y)) ^ 2)
  have hc : 0 ≤ c := div_nonneg (le_min (sq_nonneg a) zero_le_one) (by norm_num)
  have hp : Integrable p := integrable_gaussianSincDeficit_integrand hR L x
  have hpnonneg (y : ℝ) : 0 ≤ p y := by
    apply mul_nonneg (gaussianPairKernel_nonneg hR.le y)
    exact sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _))
  have hhalf (S : Set ℝ) (hS : MeasurableSet S)
      (hmass : (∫ y in S, gaussianPairKernel R y) = 1 / 2)
      (hxy : ∀ y ∈ S, 0 ≤ x * y) : c / 2 * min (x ^ 2) 1 ≤ ∫ y : ℝ, p y := by
    have hlocal (y : ℝ) (hy : y ∈ S) :
        (c * min (x ^ 2) 1) * gaussianPairKernel R y ≤ p y := by
      have hsq : x ^ 2 ≤ (x + y) ^ 2 := by nlinarith only [hxy y hy, sq_nonneg y]
      have hm := mul_le_mul_of_nonneg_left (min_le_min_right (1 : ℝ) hsq) hc
      have hg := scaled_sinc_gap a (x + y)
      have hlow : c * min (x ^ 2) 1 ≤ 1 - sinc (a * (x + y)) ^ 2 := hm.trans hg
      have h := mul_le_mul_of_nonneg_right hlow (gaussianPairKernel_nonneg hR.le y)
      simpa only [p, mul_comm] using h
    have hi : (∫ y in S, (c * min (x ^ 2) 1) * gaussianPairKernel R y) ≤ ∫ y in S, p y := by
      apply integral_mono_ae ((integrable_gaussianPairKernel hR).const_mul _).integrableOn hp.integrableOn
      filter_upwards [ae_restrict_mem hS] with y hy
      exact hlocal y hy
    calc
      c / 2 * min (x ^ 2) 1 = ∫ y in S, (c * min (x ^ 2) 1) * gaussianPairKernel R y := by
        rw [integral_const_mul, hmass]
        ring
      _ ≤ ∫ y in S, p y := hi
      _ ≤ ∫ y : ℝ, p y := setIntegral_le_integral hp (Filter.Eventually.of_forall hpnonneg)
  have hresult : c / 2 * min (x ^ 2) 1 ≤ ∫ y : ℝ, p y := by
    rcases le_or_gt 0 x with hx | hx
    · exact hhalf (Ioi 0) measurableSet_Ioi (integral_Ioi_gaussianPairKernel hR)
        (fun y hy => mul_nonneg hx hy.le)
    · exact hhalf (Iic 0) measurableSet_Iic (integral_Iic_gaussianPairKernel hR)
        (fun y hy => mul_nonneg_of_nonpos_of_nonpos hx.le hy)
  convert hresult using 1 <;> dsimp only [a, c, p, gaussianSincDeficit]
  ring

theorem regularizedTotientGridFormFactor_neg (L : ℕ) (R α : ℝ) :
    regularizedTotientGridFormFactor L R (-α) = regularizedTotientGridFormFactor L R α := by
  simp only [regularizedTotientGridFormFactor, gaussianFrequencyCutoff, neg_div, neg_sq,
    abs_neg, totientGridFormFactor_neg]

theorem regularizedTotientGridFormFactor_le {L : ℕ} (hL : 1 ≤ L) (R α : ℝ) :
    regularizedTotientGridFormFactor L R α ≤ L := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hχ := gaussianFrequencyCutoff_pos R α
  have hχ1 := gaussianFrequencyCutoff_le_one R α
  have hfirst := mul_le_mul_of_nonneg_left (totientGridFormFactor_le hL α) hχ.le
  have hsecond := mul_le_mul_of_nonneg_left
    ((min_le_right |α| (1 : ℝ)).trans hLR) (sub_nonneg.mpr hχ1)
  unfold regularizedTotientGridFormFactor
  nlinarith only [hfirst, hsecond]

theorem tendsto_gaussianFrequencyCutoff_nat (α : ℝ) :
    Tendsto (fun N : ℕ => gaussianFrequencyCutoff ((N : ℝ) + 1) α) atTop (𝓝 1) := by
  have hi : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun N : ℕ => α / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hi.const_mul α
  simpa only [gaussianFrequencyCutoff, zero_pow two_ne_zero, mul_zero, exp_zero, Function.comp_def] using
    (Real.continuous_exp.tendsto (-π * (0 : ℝ) ^ 2)).comp ((hd.pow 2).const_mul (-π))

theorem tendsto_regularizedTotientGridFormFactor (L : ℕ) (α : ℝ) :
    Tendsto (fun N : ℕ => regularizedTotientGridFormFactor L ((N : ℝ) + 1) α)
      atTop (𝓝 (totientGridFormFactor L α)) := by
  have hχ := tendsto_gaussianFrequencyCutoff_nat α
  have h := (hχ.mul (tendsto_const_nhds (x := totientGridFormFactor L α))).add
    ((hχ.const_sub 1).mul (tendsto_const_nhds (x := min |α| 1)))
  simpa only [regularizedTotientGridFormFactor, one_mul, sub_self, zero_mul, add_zero] using h

/-- At each fixed bandwidth the regularized Frobenius values recover the grid value. -/
theorem tendsto_frobenius_regularizedTotientGrid {L : ℕ} (hL : 1 ≤ L) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => frobeniusFormFactor (regularizedTotientGridFormFactor L ((N : ℝ) + 1)) lam)
      atTop (𝓝 (frobeniusFormFactor (totientGridFormFactor L) lam)) := by
  have hint : Tendsto (fun N : ℕ => ∫ α in Ioc (0 : ℝ) lam,
      (lam - α) * regularizedTotientGridFormFactor L ((N : ℝ) + 1) α) atTop
      (𝓝 (∫ α in Ioc (0 : ℝ) lam, (lam - α) * totientGridFormFactor L α)) := by
    apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
    · filter_upwards with N
      exact ((continuous_const.sub continuous_id).mul
        (continuous_regularizedTotientGridFormFactor L _)).aestronglyMeasurable
    · refine ⟨lam * (L : ℝ), Filter.Eventually.of_forall (fun N => ?_)⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      have hlama : 0 ≤ lam - α := sub_nonneg.mpr hα.2
      have hF0 := regularizedTotientGridFormFactor_nonneg hL ((N : ℝ) + 1) α
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlama hF0)]
      exact mul_le_mul (by linarith only [hα.1] : lam - α ≤ lam)
        (regularizedTotientGridFormFactor_le hL ((N : ℝ) + 1) α) hF0 hlam.le
    · exact Filter.Eventually.of_forall (fun α =>
        (tendsto_regularizedTotientGridFormFactor L α).const_mul (lam - α))
  have h := (hint.const_mul (2 / lam ^ 2)).const_add (1 / lam)
  simpa only [frobeniusFormFactor, intervalIntegral.integral_of_le hlam.le] using h

/-- Damping the central triangle convolves its squared-sinc transform with the Gaussian. -/
theorem fourier_gaussian_mul_gridCentralTriangle {L : ℕ} (hL : 0 < L)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    𝓕 (fun α => ((gaussianFrequencyCutoff R α *
      ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) : ℝ) : ℂ)) x =
      ((∫ y : ℝ, gaussianPairKernel R y *
        sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 : ℝ) : ℂ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let c : ℝ → ℂ := fun α => (((L : ℝ) * triangleFn 1 ((L : ℝ) * α) : ℝ) : ℂ)
  have hc : c = fun α => (L : ℂ) * (triangleFn (1 / (L : ℝ)) α : ℂ) := by
    funext α
    simp only [c, triangleFn_one_mul hLR, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hci : Integrable c := by
    have ht : Integrable (triangleFn (1 / (L : ℝ))) := by
      simpa only [sub_zero] using integrable_triangleFn_sub (one_div_pos.mpr hLR) 0
    rw [hc]
    exact ht.ofReal.const_mul _
  have hcf (ξ : ℝ) : 𝓕 c ξ = (sinc (π * (1 / (L : ℝ)) * ξ) ^ 2 : ℂ) := by
    rw [hc, fourierIntegral_const_mul, fourier_triangleFn (one_div_pos.mpr hLR)]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_pow]
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  let g : ℝ → ℂ := fun α => Complex.exp ((2 * π * (-x) * α : ℝ) * Complex.I) * c α
  have hgi : Integrable g := integrable_exp_mul hci (-x)
  have hgf (y : ℝ) : 𝓕 g y = (sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 : ℂ) := by
    rw [show 𝓕 g y = 𝓕 c (y - -x) from fourierIntegral_exp_mul c (-x) y, hcf]
    rw [sub_neg_eq_add, add_comm]
  have hp := GaloisForLFunctions.RHTower.Kuznetsov.integral_fourier_mul_eq
    (fun y => (gaussianPairKernel R y : ℂ)) g (integrable_gaussianPairKernel hR).ofReal hgi
  calc
    _ = ∫ α : ℝ, 𝓕 (fun y => (gaussianPairKernel R y : ℂ)) α * g α := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with α
      rw [fourier_gaussianPairKernel hR]
      dsimp only [g, c]
      have he : (-2 * π * α * x : ℝ) = 2 * π * (-x) * α := by ring
      rw [he]
      push_cast
      ring
    _ = ∫ y : ℝ, (gaussianPairKernel R y : ℂ) * 𝓕 g y := hp
    _ = _ := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with y
      rw [hgf, Complex.ofReal_mul, Complex.ofReal_pow]

theorem gaussianPairKernel_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : gaussianPairKernel R x ≤ R := by
  have h : exp (-π * (R * x) ^ 2) ≤ 1 :=
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left h hR
  simpa only [gaussianPairKernel, mul_one] using hm

/-- Each damped cyclic grid contributes at least its origin Gaussian. -/
theorem origin_gaussian_le_fourier_grid {m : ℕ} (hm : 0 < m) (L : ℕ)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    ((L : ℝ) / m) * gaussianPairKernel R x ≤
      (𝓕 (fun α => (gridPeriodicTriangle L m α : ℂ) *
        (gaussianFrequencyCutoff R α : ℂ)) x).re := by
  let t : ℤ → ℝ := fun r => (L : ℝ) * gridSincWeight m r *
    gaussianPairKernel R (x - gridFourierFrequency L m r)
  have ht (r : ℤ) : 0 ≤ t r :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg L) (gridSincWeight_nonneg m r))
      (gaussianPairKernel_nonneg hR.le _)
  have hs : Summable t := by
    apply Summable.of_nonneg_of_le ht (fun r => ?_)
      ((summable_gridSincWeight hm).mul_left ((L : ℝ) * R))
    have h := mul_le_mul_of_nonneg_left (gaussianPairKernel_le hR.le (x - gridFourierFrequency L m r))
      (mul_nonneg (Nat.cast_nonneg L) (gridSincWeight_nonneg m r))
    dsimp only [t]
    nlinarith only [h]
  have hft : 𝓕 (fun α => (gridPeriodicTriangle L m α : ℂ) *
        (gaussianFrequencyCutoff R α : ℂ)) x = ((∑' r : ℤ, t r : ℝ) : ℂ) := by
    rw [fourier_mul_gridPeriodicTriangle (f := fun α => (gaussianFrequencyCutoff R α : ℂ))
      hm L (integrable_gaussianFrequencyCutoff hR).ofReal x,
      Complex.ofReal_tsum]
    apply tsum_congr
    intro r
    rw [fourier_gaussianFrequencyCutoff hR]
    dsimp only [t]
    push_cast
    ring
  rw [hft, Complex.ofReal_re]
  have hzero : t 0 = ((L : ℝ) / m) * gaussianPairKernel R x := by
    simp only [t, gridSincWeight_zero, gridFourierFrequency, Int.cast_zero, mul_zero, sub_zero]
    ring
  rw [← hzero]
  exact hs.le_tsum 0 (fun r _ => ht r)

private theorem fourier_sub_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (x : ℝ) : 𝓕 (fun α => f α - g α) x = 𝓕 f x - 𝓕 g x := by
  have he : (fun α => f α - g α) = fun α => f α + (-1 : ℂ) * g α := by funext α; ring
  rw [he, fourierIntegral_add hf (hg.const_mul _), fourierIntegral_const_mul]
  ring

private theorem fourier_finsetSum_integrable {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℂ}
    (hF : ∀ i ∈ S, Integrable (F i)) (x : ℝ) :
    𝓕 (fun α => ∑ i ∈ S, F i α) x = ∑ i ∈ S, 𝓕 (F i) x := by
  classical
  revert hF
  induction S using Finset.induction_on with
  | empty =>
      intro hF
      simp only [Finset.sum_empty, Real.fourier_real_eq_integral_exp_smul, smul_zero, integral_zero]
  | @insert i S hi ih =>
      intro hF
      have hS : ∀ j ∈ S, Integrable (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [fourierIntegral_add (hF i (Finset.mem_insert_self _ _)) (integrable_finsetSum S hS), ih hS]

private theorem integrable_gaussian_grid {m : ℕ} (hm : 0 < m) (L : ℕ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun α => (gridPeriodicTriangle L m α : ℂ) * (gaussianFrequencyCutoff R α : ℂ)) := by
  apply (integrable_gaussianFrequencyCutoff hR).ofReal.bdd_mul (c := (L : ℝ))
  · exact (Complex.continuous_ofReal.comp (continuous_gridPeriodicTriangle hm L)).aestronglyMeasurable
  · filter_upwards with α
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gridPeriodicTriangle_nonneg L m α),
      gridPeriodicTriangle_eq_interpolation hm]
    have hcoeff (k : ℤ) : (if (m : ℤ) ∣ k then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have h := mul_le_mul_of_nonneg_left (integerHatInterpolation_le hcoeff ((L : ℝ) * α))
      (Nat.cast_nonneg (α := ℝ) L)
    simpa only [mul_one] using h

/-- Pair density before restoring the exact unit-band ramp. -/
def dampedTotientPairDensity (L : ℕ) (R x : ℝ) : ℝ :=
  1 + (𝓕 (fun α => ((gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1) : ℝ) : ℂ)) x).re

private theorem fourier_even_real {f : ℝ → ℝ} (heven : ∀ α, f (-α) = f α) (x : ℝ) :
    𝓕 (fun α => (f α : ℂ)) x = ((𝓕 (fun α => (f α : ℂ)) x).re : ℂ) := by
  have hconj : (starRingEnd ℂ) (𝓕 (fun α => (f α : ℂ)) x) =
      𝓕 (fun α => (f α : ℂ)) x := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
    simp only [smul_eq_mul]
    calc
      _ = ∫ α : ℝ, Complex.exp ((-2 * π * (-α) * x : ℝ) * Complex.I) * (f (-α) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with α
        rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, heven]
        simp only [Complex.conj_ofReal]
        congr 1
        congr 1
        push_cast
        ring
      _ = _ := MeasureTheory.integral_neg_eq_self
        (fun α : ℝ => Complex.exp ((-2 * π * α * x : ℝ) * Complex.I) * (f α : ℂ)) volume
  exact (Complex.conj_eq_iff_re.mp hconj).symm

/-- The pair density of the corrected, integrable form factor. -/
def regularizedTotientPairDensity (L : ℕ) (R x : ℝ) : ℝ :=
  1 + (𝓕 (fun α => ((regularizedTotientGridFormFactor L R α - 1 : ℝ) : ℂ)) x).re

theorem fourier_regularizedTotientGridFormFactor_real (L : ℕ) (R x : ℝ) :
    𝓕 (fun α => ((regularizedTotientGridFormFactor L R α - 1 : ℝ) : ℂ)) x =
      ((regularizedTotientPairDensity L R x - 1 : ℝ) : ℂ) := by
  have h := fourier_even_real (f := fun α => regularizedTotientGridFormFactor L R α - 1)
    (fun α => congrArg (fun t : ℝ => t - 1) (regularizedTotientGridFormFactor_neg L R α)) x
  simpa only [regularizedTotientPairDensity, add_sub_cancel_left] using h

private theorem re_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Complex.zero_re]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, Complex.add_re, ih]

/-- The origin surplus remains as a positive Gaussian after smoothing. -/
theorem dampedTotientPairDensity_lower {L : ℕ} (hL : 1 ≤ L) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    gaussianSincDeficit L R x + (totientGridOriginMass L - 1) * gaussianPairKernel R x ≤
      dampedTotientPairDensity L R x := by
  have hLpos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  let G : ℕ → ℝ → ℂ := fun m α =>
    (gridPeriodicTriangle L m α : ℂ) * (gaussianFrequencyCutoff R α : ℂ)
  let M : ℝ → ℂ := fun α =>
    (∑ m ∈ Finset.Icc 1 L, (totientGridWeight L m : ℂ) * G m α) +
      (totientGridRemainder L : ℂ) * G (L + 1) α
  let C : ℝ → ℂ := fun α => ((gaussianFrequencyCutoff R α *
    ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) : ℝ) : ℂ)
  have hG (m : ℕ) (hm : 0 < m) : Integrable (G m) := integrable_gaussian_grid hm L hR
  have hterms (m : ℕ) (hm : m ∈ Finset.Icc 1 L) :
      Integrable (fun α => (totientGridWeight L m : ℂ) * G m α) :=
    (hG m (Finset.mem_Icc.mp hm).1).const_mul _
  have hrest : Integrable (fun α => (totientGridRemainder L : ℂ) * G (L + 1) α) :=
    (hG (L + 1) (Nat.succ_pos L)).const_mul _
  have hsum := integrable_finsetSum (Finset.Icc 1 L) hterms
  have hMi : Integrable M := hsum.add hrest
  have hχc : Continuous (gaussianFrequencyCutoff R) := by unfold gaussianFrequencyCutoff; fun_prop
  have hCi : Integrable C := by
    have hi := integrable_triangle_mul_continuous (F := fun α => gaussianFrequencyCutoff R α * (L : ℝ))
      (one_div_pos.mpr hLR) (hχc.mul continuous_const)
    have hireal : Integrable (fun α => gaussianFrequencyCutoff R α *
        ((L : ℝ) * triangleFn 1 ((L : ℝ) * α))) := by
      simp_rw [triangleFn_one_mul hLR]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
    exact hireal.ofReal
  have hχi : Integrable (fun α => (gaussianFrequencyCutoff R α : ℂ)) :=
    (integrable_gaussianFrequencyCutoff hR).ofReal
  have hMCi : Integrable (fun α => M α - C α) := hMi.sub hCi
  have hpoint : (fun α => ((gaussianFrequencyCutoff R α *
      (totientGridFormFactor L α - 1) : ℝ) : ℂ)) =
      fun α => (M α - C α) - (gaussianFrequencyCutoff R α : ℂ) := by
    funext α
    dsimp only [M, G, C]
    rw [totientGridFormFactor_eq_mixture]
    push_cast
    simp only [mul_sub, mul_add, Finset.mul_sum, one_mul, mul_assoc, mul_comm]
  have hMF : 𝓕 M x =
      (∑ m ∈ Finset.Icc 1 L, (totientGridWeight L m : ℂ) * 𝓕 (G m) x) +
        (totientGridRemainder L : ℂ) * 𝓕 (G (L + 1)) x := by
    dsimp only [M]
    rw [fourierIntegral_add hsum hrest,
      fourier_finsetSum_integrable (Finset.Icc 1 L) hterms x, fourierIntegral_const_mul]
    simp only [fourierIntegral_const_mul]
  have hCF : 𝓕 C x = ((∫ y : ℝ, gaussianPairKernel R y *
      sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 : ℝ) : ℂ) :=
    fourier_gaussian_mul_gridCentralTriangle hLpos hR x
  have hFT : 𝓕 (fun α => ((gaussianFrequencyCutoff R α *
      (totientGridFormFactor L α - 1) : ℝ) : ℂ)) x =
      ((∑ m ∈ Finset.Icc 1 L, (totientGridWeight L m : ℂ) * 𝓕 (G m) x) +
        (totientGridRemainder L : ℂ) * 𝓕 (G (L + 1)) x) -
      ((∫ y : ℝ, gaussianPairKernel R y * sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 : ℝ) : ℂ) -
      (gaussianPairKernel R x : ℂ) := by
    rw [hpoint, fourier_sub_integrable hMCi hχi, fourier_sub_integrable hMi hCi,
      hMF, hCF, fourier_gaussianFrequencyCutoff hR]
  have hmain : totientGridOriginMass L * gaussianPairKernel R x ≤
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * (𝓕 (G m) x).re) +
        totientGridRemainder L * (𝓕 (G (L + 1)) x).re := by
    have hs := Finset.sum_le_sum (s := Finset.Icc 1 L) (fun m hm =>
      mul_le_mul_of_nonneg_left (origin_gaussian_le_fourier_grid (Finset.mem_Icc.mp hm).1 L hR x)
        (totientGridWeight_nonneg L m))
    have hn := mul_le_mul_of_nonneg_left (origin_gaussian_le_fourier_grid (Nat.succ_pos L) L hR x)
      (totientGridRemainder_nonneg hL)
    rw [totientGridOriginMass_eq_weighted_modes hLpos, add_mul, Finset.sum_mul]
    simpa only [G, Nat.cast_add, Nat.cast_one, Nat.cast_succ,
      Nat.succ_eq_add_one, mul_assoc, mul_left_comm, mul_comm] using add_le_add hs hn
  have hprod : Integrable (fun y => gaussianPairKernel R y *
      sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2) := by
    have hi : Integrable (fun y => gaussianPairKernel R y -
        gaussianPairKernel R y * (1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2)) :=
      (integrable_gaussianPairKernel hR).sub (integrable_gaussianSincDeficit_integrand hR L x)
    convert hi using 1
    funext y
    ring
  have hD : gaussianSincDeficit L R x = 1 -
      ∫ y : ℝ, gaussianPairKernel R y * sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 := by
    unfold gaussianSincDeficit
    have he : (fun y => gaussianPairKernel R y * (1 - sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2)) =
        fun y => gaussianPairKernel R y - gaussianPairKernel R y * sinc (π * (1 / (L : ℝ)) * (x + y)) ^ 2 := by
      funext y
      ring
    rw [he, integral_sub (integrable_gaussianPairKernel hR) hprod, integral_gaussianPairKernel hR]
  unfold dampedTotientPairDensity
  rw [hFT]
  simp only [Complex.sub_re, Complex.add_re, re_finsetSum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith only [hmain, hD]


/-- Restoring the exact ramp subtracts only the small correction transform. -/
theorem regularizedTotientPairDensity_eq {L : ℕ} (hL : 1 ≤ L) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    regularizedTotientPairDensity L R x = dampedTotientPairDensity L R x -
      (𝓕 (fun α => (gridRampCorrection R α : ℂ)) x).re := by
  have he : (fun α => gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1)) =
      fun α => (regularizedTotientGridFormFactor L R α - 1) + gridRampCorrection R α := by
    funext α
    rw [regularizedTotientGridFormFactor_sub_one]
    ring
  have hi : Integrable (fun α => gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1)) := by
    rw [he]
    exact (integrable_regularizedTotientGridFormFactor_sub_one hL hR).add (integrable_gridRampCorrection R)
  have hfun : (fun α => ((regularizedTotientGridFormFactor L R α - 1 : ℝ) : ℂ)) =
      fun α => ((gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1) : ℝ) : ℂ) -
        (gridRampCorrection R α : ℂ) := by
    funext α
    rw [regularizedTotientGridFormFactor_sub_one, Complex.ofReal_sub]
  unfold regularizedTotientPairDensity dampedTotientPairDensity
  rw [hfun, fourier_sub_integrable
    (f := fun α => ((gaussianFrequencyCutoff R α * (totientGridFormFactor L α - 1) : ℝ) : ℂ))
    (g := fun α => (gridRampCorrection R α : ℂ))
    hi.ofReal (integrable_gridRampCorrection R).ofReal,
    Complex.sub_re]
  ring

/-- A positive origin surplus makes the corrected pair density nonnegative at every point. -/
theorem eventually_regularizedTotientPairDensity_nonneg {L : ℕ} (hL : 1 ≤ L)
    (hA : 1 < totientGridOriginMass L) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ x : ℝ, 0 ≤ regularizedTotientPairDensity L R x := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hc : 0 < min ((π * (1 / (L : ℝ))) ^ 2) 1 / 24 := by
    apply div_pos (lt_min (sq_pos_of_pos (mul_pos pi_pos (one_div_pos.mpr hLR))) zero_lt_one)
    norm_num
  have h := eventually_gaussian_fills_quadratic_gap hc (sub_pos.mpr hA) pi_pos.le pi_pos.le
  filter_upwards [h] with R hR
  refine ⟨hR.1, fun x => ?_⟩
  have hsmall := hR.2 x
  have hbackground := gaussianSincDeficit_quadratic_lower hR.1 L x
  have hdamped := dampedTotientPairDensity_lower hL hR.1 x
  have herror := (Complex.re_le_norm (𝓕 (fun α => (gridRampCorrection R α : ℂ)) x)).trans
    (norm_fourier_gridRampCorrection_le hR.1 x)
  rw [regularizedTotientPairDensity_eq hL hR.1]
  dsimp only [gaussianPairKernel] at hdamped
  nlinarith only [hsmall, hbackground, hdamped, herror]

/-- Raw spectral and pair-density positivity cannot certify seventy percent at any bandwidth.
The witness is continuous, even, has an integrable perturbation of one, and has the exact
unit-band ramp. No lower bound of one outside that band is asserted. -/
theorem positivity_does_not_reach_seventy_percent_at_any_bandwidth (lam : ℝ) (hlam : 0 < lam) :
    ∃ F p : ℝ → ℝ,
      Continuous F ∧ (∀ α, F (-α) = F α) ∧ (∀ α, 0 ≤ F α) ∧
      (∀ α, |α| ≤ 1 → F α = |α|) ∧ Integrable (fun α => F α - 1) ∧
      (∀ x, 0 ≤ p x) ∧ (∀ x, 𝓕 (fun α => ((F α - 1 : ℝ) : ℂ)) x = ((p x - 1 : ℝ) : ℂ)) ∧
      (13 : ℝ) / 10 < frobeniusFormFactor F lam := by
  obtain ⟨L, hL, hA⟩ := exists_totientGridOriginMass_gt 0
  have hL1 : 1 ≤ L := (le_max_left 1 0).trans hL
  have hA1 : 1 < totientGridOriginMass L := by linarith only [hA]
  have hnat : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hp := hnat.eventually (eventually_regularizedTotientPairDensity_nonneg hL1 hA1)
  have hlimit : (13 : ℝ) / 10 < frobeniusFormFactor (totientGridFormFactor L) lam :=
    hA.trans_le (totientGridOriginMass_le_frobenius hL1 hlam)
  have hf := (tendsto_frobenius_regularizedTotientGrid hL1 hlam).eventually
    (Ioi_mem_nhds hlimit)
  obtain ⟨N, hN⟩ := (hp.and hf).exists
  refine ⟨regularizedTotientGridFormFactor L ((N : ℝ) + 1),
    regularizedTotientPairDensity L ((N : ℝ) + 1),
    continuous_regularizedTotientGridFormFactor L _, regularizedTotientGridFormFactor_neg L _,
    regularizedTotientGridFormFactor_nonneg hL1 _,
    fun α hα => regularizedTotientGridFormFactor_eq_abs hL1 _ hα,
    integrable_regularizedTotientGridFormFactor_sub_one hL1 hN.1.1,
    hN.1.2, fourier_regularizedTotientGridFormFactor_real L _, hN.2⟩

end GaloisForLFunctions.TransThresholdPairCorrelation
