import GaloisForLFunctions.RHTower.WeilWorkDeficitZeroTransport
import GaloisForLFunctions.RHTower.WeilWorkDeficitArithmeticMean

/-!
# Square-root coefficient scale for actual spectral deficit

Exact arithmetic means, transport of both actual measures, and their common critical mass
improve the coefficient scale from n to √n. No upper deficit-density premise is assumed.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

private def coefficientPhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℝ :=
  (weilContinuation hW ((2 : ℂ) + t * I)).re

private def coefficientXi (t : ℝ) : ℝ := (logDeriv xi ((2 : ℂ) + t * I)).re

private theorem continuous_coefficientPhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Continuous (coefficientPhi hW) := by
  refine Complex.continuous_re.comp ?_
  refine (differentiableOn_weilContinuation hW).continuousOn.comp_continuous (by fun_prop)
    (fun t => ?_)
  show 1 / 2 < ((2 : ℂ) + t * I).re
  norm_num

private theorem continuous_coefficientXi : Continuous coefficientXi := by
  have h := continuous_weighted_copyPoisson (σ := 2) (by norm_num)
    (c := fun _ => 1) (fun _ => by norm_num) (fun _ => le_rfl)
  refine h.congr fun t => ?_
  simp only [one_mul]
  exact (re_logDeriv_xi_eq_tsum_copyPoisson (σ := 2) (by norm_num) t).symm

private theorem integrable_coefficientProduct (f : ℝ → ℝ) (hf : Continuous f) (k T : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp (((k * t : ℝ) : ℂ) * I) * (f t : ℂ)) (Ioc 0 T) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (((k * t : ℝ) : ℂ) * I)) := by fun_prop
  exact (hc.mul (Complex.continuous_ofReal.comp hf)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

private def coefficientSource {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (k T : ℝ) : ℂ :=
  ∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) *
    ((coefficientPhi hW t - coefficientXi t : ℝ) : ℂ)

/-- Finite-window character difference between the two actual measures. -/
def deficitCharacterGap {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (k T : ℝ) : ℂ :=
  (∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂boundaryMeasure hW) -
    ∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂deficitOrdinateMeasure

private theorem coefficientSource_re {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (k T : ℝ) :
    (coefficientSource hW k T).re = ∫ t in Ioc 0 T,
      (coefficientPhi hW t - coefficientXi t) * Real.cos (t * k) := by
  have hi := integrable_coefficientProduct (fun t => coefficientPhi hW t - coefficientXi t)
    ((continuous_coefficientPhi hW).sub continuous_coefficientXi) k T
  have hre := integral_re hi
  change (∫ t in Ioc 0 T,
      (Complex.exp (((k * t : ℝ) : ℂ) * I) *
        ((coefficientPhi hW t - coefficientXi t : ℝ) : ℂ)).re) =
    (coefficientSource hW k T).re at hre
  rw [← hre]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  rw [mul_comm k t, mul_comm]

private theorem coefficientSource_eq_errors {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k T : ℝ) :
    coefficientSource hW k T =
      ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ) * deficitCharacterGap hW k T +
        deficitFourierError hW k T - deficitZeroFourierError k T := by
  have hphi := integrable_coefficientProduct (coefficientPhi hW) (continuous_coefficientPhi hW) k T
  have hxi := integrable_coefficientProduct coefficientXi continuous_coefficientXi k T
  have heq : coefficientSource hW k T =
      (∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) * (coefficientPhi hW t : ℂ)) -
        ∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) * (coefficientXi t : ℂ) := by
    rw [coefficientSource, ← integral_sub hphi hxi]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by push_cast; ring
  rw [heq]
  unfold deficitCharacterGap deficitFourierError deficitZeroFourierError coefficientPhi coefficientXi
  ring

private theorem characterGap_limit_of_sourceMean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k L : ℝ)
    (hSource : Tendsto (fun T : ℝ => (coefficientSource hW k T).re / T) atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => (deficitCharacterGap hW k T).re / T) atTop
      (𝓝 (L / (Real.pi * Real.exp (-((3 / 2) * |k|))))) := by
  have hE : Tendsto (fun T : ℝ => deficitFourierError hW k T / (T : ℂ) -
      deficitZeroFourierError k T / (T : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [sub_zero] using
      (tendsto_deficitFourierError_div hW (fun _ => k)).sub (tendsto_deficitZeroFourierError_div k)
  have hr := (Complex.continuous_re.tendsto (0 : ℂ)).comp hE
  change Tendsto (fun T : ℝ => (deficitFourierError hW k T / (T : ℂ) -
      deficitZeroFourierError k T / (T : ℂ)).re) atTop (𝓝 0) at hr
  have herr : Tendsto (fun T : ℝ =>
      (deficitFourierError hW k T - deficitZeroFourierError k T).re / T) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Complex.sub_re, Complex.div_ofReal_re, sub_div,
      Complex.zero_re] using hr
  let c : ℝ := Real.pi * Real.exp (-((3 / 2) * |k|))
  have hc : c ≠ 0 := (mul_pos Real.pi_pos (Real.exp_pos _)).ne'
  have h := (hSource.sub herr).div_const c
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hrel := congrArg Complex.re (coefficientSource_eq_errors hW k T)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hrel
  change (coefficientSource hW k T).re = c * (deficitCharacterGap hW k T).re +
    (deficitFourierError hW k T).re - (deficitZeroFourierError k T).re at hrel
  rw [hrel, Complex.sub_re]
  field_simp [hc, show T ≠ 0 by linarith]
  ring

private theorem rpow_two_div_projection (x : ℝ) (hx : 0 < x) :
    x ^ (-2 : ℝ) / Real.exp (-((3 / 2) * Real.log x)) = 1 / Real.sqrt x := by
  have he : -((3 / 2) * Real.log x) = Real.log x * (-(3 / 2)) := by ring
  rw [he, ← Real.rpow_def_of_pos hx, ← Real.rpow_sub hx]
  rw [show (-2 : ℝ) - -(3 / 2) = -(1 / 2) by ring, Real.rpow_neg hx.le,
    ← Real.sqrt_eq_rpow, one_div]

/-- The exact real character discrepancy has the square-root arithmetic normalization. -/
theorem tendsto_deficitCharacterGap_re_div_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun T : ℝ => (deficitCharacterGap hW (Real.log n) T).re / T) atTop
      (𝓝 (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) / (2 * Real.pi * Real.sqrt n))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hs : Tendsto (fun T : ℝ => (coefficientSource hW (Real.log n) T).re / T) atTop
      (𝓝 (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (n : ℝ) ^ (-2 : ℝ) / 2)) := by
    simpa only [coefficientSource_re, coefficientPhi, coefficientXi, Complex.ofReal_ofNat] using
      tendsto_deficit_arithmetic_cosine_mean hW (σ := 2) (by norm_num) hn
  have h := characterGap_limit_of_sourceMean hW (Real.log n) _ hs
  rw [abs_of_nonneg hlog] at h
  have heq : (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (n : ℝ) ^ (-2 : ℝ) / 2) /
      (Real.pi * Real.exp (-((3 / 2) * Real.log n))) =
      ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) / (2 * Real.pi * Real.sqrt n) := by
    calc
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) / (2 * Real.pi)) *
          ((n : ℝ) ^ (-2 : ℝ) / Real.exp (-((3 / 2) * Real.log n))) := by ring
      _ = _ := by rw [rpow_two_div_projection _ hnpos]; ring
  rwa [heq] at h

private theorem deficitCharacterGap_zero_re {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) :
    (deficitCharacterGap hW 0 T).re =
      (boundaryMeasure hW).real (Ioc 0 T) - ((finite_deficitWindow T).toFinset.card : ℝ) := by
  simp [deficitCharacterGap, integral_const, measureReal_def,
    deficitOrdinateMeasure_Ioc]

/-- Canonical and actual zero masses agree up to sublinear error on the sharp height window. -/
theorem tendsto_deficitWindow_mass_sub_div {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun T : ℝ => ((boundaryMeasure hW).real (Ioc 0 T) -
      ((finite_deficitWindow T).toFinset.card : ℝ)) / T) atTop (𝓝 0) := by
  have hs : Tendsto (fun T : ℝ => (coefficientSource hW 0 T).re / T) atTop (𝓝 0) := by
    simpa only [coefficientSource_re, coefficientPhi, coefficientXi, Complex.ofReal_ofNat,
      mul_zero, Real.cos_zero, mul_one]
      using tendsto_deficit_arithmetic_mean hW (σ := 2) (by norm_num)
  simpa only [zero_div, deficitCharacterGap_zero_re] using characterGap_limit_of_sourceMean hW 0 0 hs

/-- Actual spectral deficit has the sharper square-root coefficient lower bound, eventually. -/
theorem eventually_sub_vonMangoldt_div_sqrt_le_deficit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / (4 * Real.pi * Real.sqrt n) ≤
        deficitCount hW T / T + ε := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hconst : |((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) /
      (2 * Real.pi * Real.sqrt n)| / 2 =
      |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / (4 * Real.pi * Real.sqrt n) := by
    rw [abs_div, abs_of_pos (show 0 < 2 * Real.pi * Real.sqrt (n : ℝ) from
      mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr hnpos)), abs_sub_comm]
    ring
  have hlim := ((tendsto_deficitCharacterGap_re_div_log hW hn).abs.sub
    (tendsto_deficitWindow_mass_sub_div hW)).div_const 2
  simp only [sub_zero, hconst] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds (show
      |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / (4 * Real.pi * Real.sqrt n) - ε <
      |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / (4 * Real.pi * Real.sqrt n) by linarith)),
    eventually_ge_atTop (1 : ℝ)] with T hsmall hT
  have hTpos : 0 < T := by linarith
  have hb0 := (Complex.abs_re_le_norm (deficitCharacterGap hW (Real.log n) T)).trans
    (norm_deficitWindow_fourier_sub_le hW (Real.log n) T)
  have hb := div_le_div_of_nonneg_right hb0 hTpos.le
  have hAbs : |(deficitCharacterGap hW (Real.log n) T).re / T| =
      |(deficitCharacterGap hW (Real.log n) T).re| / T := by
    rw [abs_div, abs_of_pos hTpos]
  rw [← hAbs] at hb
  simp only [add_div, mul_div_assoc] at hb
  linarith

end RHTower.WeilSpectral
end
