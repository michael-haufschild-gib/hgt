import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The literal logarithmic Gamma shift along a horizontal segment. -/
def gammaHorizontalLogShift (σ lam t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..lam,
    Complex.digamma (((σ : ℂ) + (t : ℂ) * I) + (u : ℂ))

private theorem intervalIntegrable_horizontal_digamma
    {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam) (t : ℝ) :
    IntervalIntegrable (fun u : ℝ =>
      Complex.digamma (((σ : ℂ) + (t : ℂ) * I) + (u : ℂ))) volume 0 lam := by
  apply ContinuousOn.intervalIntegrable
  refine (continuousOn_digamma_shift ((σ : ℂ) + (t : ℂ) * I)).mono ?_
  intro u hu
  rw [Set.uIcc_of_le hlam] at hu
  change -(((σ : ℂ) + (t : ℂ) * I).re) < u
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_self, add_zero]
  linarith [hu.1]

/-- The shift exponent is exact, with no logarithm-branch choice. -/
theorem Gamma_horizontal_eq_exp_logShift
    {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam) (t : ℝ) :
    Complex.Gamma (((σ + lam : ℝ) : ℂ) + (t : ℂ) * I) =
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * I) *
        Complex.exp (gammaHorizontalLogShift σ lam t) := by
  have hz : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hσ
  have h := gamma_shift_exp_integral hz hlam
  rw [show (((σ + lam : ℝ) : ℂ) + (t : ℂ) * I) =
    ((σ : ℂ) + (t : ℂ) * I) + (lam : ℂ) by push_cast; ring]
  exact h

/-- The entire horizontal log shift has its explicit vertical main part. -/
theorem tendsto_gammaHorizontalLogShift_sub_main
    {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    Tendsto (fun t : ℝ => gammaHorizontalLogShift σ lam t -
      (lam : ℂ) * ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_uniform_bound_digamma_sub_vertLog
    (M := σ + lam) (by linarith)
  have heq (t : ℝ) : gammaHorizontalLogShift σ lam t -
      (lam : ℂ) * ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * I) =
      ∫ u in (0 : ℝ)..lam,
        Complex.digamma (((σ : ℂ) + (t : ℂ) * I) + (u : ℂ)) - vertLog t := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_horizontal_digamma hσ hlam t)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul]
    rfl
  simp_rw [heq]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => (C / t) * |lam - 0|) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C)).div_atTop (tendsto_id : Tendsto id atTop atTop)
    simpa using h.mul_const |lam - 0|
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  rw [Set.uIoc_of_le hlam] at hu
  have hz : ((σ : ℂ) + (t : ℂ) * I) + (u : ℂ) =
      ((σ + u : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  rw [hz]
  exact hbound (σ + u) t (by linarith [hu.1]) (by linarith [hu.2]) ht

/-- The limiting phase gained by a horizontal shift is lam*pi/2. -/
theorem tendsto_gammaHorizontalLogShift_im
    {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    Tendsto (fun t : ℝ => (gammaHorizontalLogShift σ lam t).im)
      atTop (𝓝 (lam * (Real.pi / 2))) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_gammaHorizontalLogShift_sub_main hσ hlam)
  have h' : Tendsto (fun t : ℝ =>
      (gammaHorizontalLogShift σ lam t).im - lam * (Real.pi / 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, mul_div_assoc] using h
  simpa using h'.add_const (lam * (Real.pi / 2))

end RHTower
