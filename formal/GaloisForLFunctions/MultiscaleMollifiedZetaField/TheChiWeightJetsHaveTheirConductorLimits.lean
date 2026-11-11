import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheChiConductorErrorHasVanishingScaledJets
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMainTermsHavePolynomialDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Conductor limits for the actual chi-weight jets

The opposite-height chi product is its conductor exponential times one
plus the normalized Stirling error. The finite Leibniz formula and
vanishing error jets give every displacement-jet limit, including
convergent moving centres and conductor-to-mollifier logarithmic ratios.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaNotch GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The complex exponential rate in normalized displacement. -/
def scaledChiConductorRate (L t : ℝ) : ℂ :=
  2 * (Real.log (t / (2 * Real.pi)) : ℂ) / (L : ℂ)

/-- Exact separation of the conductor exponential and the actual chi error. -/
theorem scaled_holomorphicChiPair_eq (L : ℝ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    holomorphicChiPair (z / (L : ℂ)) t =
      Complex.exp (scaledChiConductorRate L t * z) +
        scaledChiConductorError L t z * Complex.exp (scaledChiConductorRate L t * z) := by
  let w : ℂ := z / (L : ℂ)
  have hp : linePt t - w = (1 / 2 : ℂ) - w + (t : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  have hm : linePt (-t) - w = (1 / 2 : ℂ) - w - (t : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  have hc : critCarrier t (-w) = holomorphicChiPair w t := by
    rw [critCarrier_neg_eq, hp, hm]
    rfl
  have hb : 0 < t / (2 * Real.pi) := by positivity
  have he : ((t / (2 * Real.pi) : ℝ) : ℂ) ^ (2 * w) =
      Complex.exp (scaledChiConductorRate L t * z) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'), ← Complex.ofReal_log hb.le]
    congr 1
    dsimp only [scaledChiConductorRate, w]
    ring
  change holomorphicChiPair w t = _
  rw [← hc, critCarrier_neg_eq_quot_mul ht, he]
  dsimp only [scaledChiConductorError, w]
  ring

/-- The actual normalized chi jet is the exponential jet plus a finite sum of error jets. -/
theorem iteratedDeriv_scaled_holomorphicChiPair_eq (L : ℝ) {t : ℝ} (ht : 0 < t)
    {C : ℂ} (hC : 2 * |(C / (L : ℂ)).im| < t) (j : ℕ) :
    iteratedDeriv j (fun z => holomorphicChiPair (z / (L : ℂ)) t) C =
      scaledChiConductorRate L t ^ j * Complex.exp (scaledChiConductorRate L t * C) +
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) *
          iteratedDeriv i (scaledChiConductorError L t) C *
            (scaledChiConductorRate L t ^ (j - i) * Complex.exp (scaledChiConductorRate L t * C)) := by
  let g : ℂ → ℂ := fun z => Complex.exp (scaledChiConductorRate L t * z)
  have hg : ContDiffAt ℂ j g C := by dsimp only [g]; fun_prop
  have hf : ContDiffAt ℂ j (scaledChiConductorError L t) C :=
    (analyticAt_scaledChiConductorError ht hC).contDiffAt
  have he : (fun z => holomorphicChiPair (z / (L : ℂ)) t) = g + scaledChiConductorError L t * g := by
    funext z
    exact scaled_holomorphicChiPair_eq L ht z
  rw [he]
  change iteratedDeriv j (g + (fun z => scaledChiConductorError L t z * g z)) C = _
  rw [iteratedDeriv_add hg (hf.mul hg), iteratedDeriv_mul hf hg]
  simp only [g, iteratedDeriv_cexp_const_mul, Pi.mul_apply, Pi.add_apply]

/-- Every actual displacement jet has the conductor-exponential limit. -/
theorem tendsto_scaled_holomorphicChiPair_jet {ι : Type*} {l : Filter ι}
    {L t : ι → ℝ} (hL : Tendsto L l atTop) (ht : Tendsto t l atTop)
    {τ : ℝ} (hτ : Tendsto (fun N : ι => Real.log (t N / (2 * Real.pi)) / L N) l (𝓝 τ))
    {C : ι → ℂ} {C₀ : ℂ} (hC : Tendsto C l (𝓝 C₀)) (j : ℕ) :
    Tendsto (fun N => iteratedDeriv j (fun z => holomorphicChiPair (z / (L N : ℂ)) (t N)) (C N))
      l (𝓝 ((2 * (τ : ℂ)) ^ j * Complex.exp (2 * (τ : ℂ) * C₀))) := by
  let R : ℝ := ‖C₀‖ + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hb : ∀ᶠ N : ι in l, ‖C N‖ ≤ R := by
    have hh := hC.eventually (Metric.ball_mem_nhds C₀ zero_lt_one)
    filter_upwards [hh] with N hN
    have hn : ‖C N - C₀‖ < 1 := by simpa only [dist_eq_norm] using hN
    have hh := norm_add_le (C N - C₀) C₀
    rw [sub_add_cancel] at hh
    dsimp only [R]
    linarith only [hh, hn]
  have ha : Tendsto (fun N => scaledChiConductorRate (L N) (t N)) l (𝓝 (2 * (τ : ℂ))) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hτ).const_mul (2 : ℂ)
    simpa only [scaledChiConductorRate, Function.comp_def, Complex.ofReal_div, mul_div_assoc] using hh
  have hexp : Tendsto (fun N => Complex.exp (scaledChiConductorRate (L N) (t N) * C N))
      l (𝓝 (Complex.exp (2 * (τ : ℂ) * C₀))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (ha.mul hC)
  have hmain := (ha.pow j).mul hexp
  have hterm (i : ℕ) : Tendsto (fun N => (j.choose i : ℂ) *
      iteratedDeriv i (scaledChiConductorError (L N) (t N)) (C N) *
        (scaledChiConductorRate (L N) (t N) ^ (j - i) *
          Complex.exp (scaledChiConductorRate (L N) (t N) * C N))) l (𝓝 0) := by
    have hh := ((tendsto_scaledChiConductorError_jet hL ht hR hb i).const_mul (j.choose i : ℂ)).mul
      ((ha.pow (j - i)).mul hexp)
    simpa only [mul_zero, zero_mul] using hh
  have hs := tendsto_finset_sum (Finset.range (j + 1)) (fun i _ => hterm i)
  have htotal := hmain.add hs
  simp only [Finset.sum_const_zero, add_zero] at htotal
  apply htotal.congr'
  filter_upwards [hb, hL.eventually_ge_atTop (R + 2), ht.eventually_ge_atTop 4] with N hCN hLN htN
  have hL0 : 0 < L N := by linarith only [hLN, hR]
  have hn : ‖C N / (L N : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le]
    apply (div_le_one hL0).mpr
    linarith only [hCN, hLN]
  have him : 2 * |(C N / (L N : ℂ)).im| < t N := by
    have hh := (Complex.abs_im_le_norm _).trans hn
    linarith only [hh, htN]
  exact (iteratedDeriv_scaled_holomorphicChiPair_eq (L N) (by linarith only [htN]) him j).symm


private theorem chi_shift_Gamma_ne_zero {z : ℂ} (hz : 0 ≤ z.re) (t : ℝ) :
    Gammaℝ (1 - ((1 / 2 : ℂ) - z + (t : ℂ) * I)) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, Complex.one_re, Complex.div_ofNat_re]
  linarith only [hz]

private theorem holomorphicChiPair_opposite_heights (z : ℂ) (t : ℝ) :
    holomorphicChiPair z t =
      zetaChi ((1 / 2 : ℂ) - z + (t : ℂ) * I) *
        zetaChi ((1 / 2 : ℂ) - z + ((-t : ℝ) : ℂ) * I) := by
  unfold holomorphicChiPair
  congr 2 <;> push_cast <;> ring

private theorem scaled_displacement_re_pos {L : ℝ} (hL : 0 < L)
    {z : ℂ} (hz : 0 < z.re) : 0 < (z / (L : ℂ)).re := by
  have he : z / (L : ℂ) = z * ((1 / L : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div, div_eq_mul_inv]
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_pos hz (one_div_pos.mpr hL)

/-- At positive normalized real part, the chi family is holomorphic for every real height. -/
theorem analyticAt_scaled_holomorphicChiPair_pos {L : ℝ} (hL : 0 < L)
    {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    AnalyticAt ℂ (fun w => holomorphicChiPair (w / (L : ℂ)) t) z := by
  have hre := (scaled_displacement_re_pos hL hz).le
  have hp := (zetaChi_analyticAt (chi_shift_Gamma_ne_zero hre t)).comp
    (f := fun w : ℂ => (1 / 2 : ℂ) - w / (L : ℂ) + (t : ℂ) * I) (by fun_prop)
  have hm := (zetaChi_analyticAt (chi_shift_Gamma_ne_zero hre (-t))).comp
    (f := fun w : ℂ => (1 / 2 : ℂ) - w / (L : ℂ) + ((-t : ℝ) : ℂ) * I) (by fun_prop)
  convert hp.mul hm using 1
  funext w
  exact holomorphicChiPair_opposite_heights (w / (L : ℂ)) t

private theorem continuous_scaled_holomorphicChiPair_height {L : ℝ} (hL : 0 < L)
    {z : ℂ} (hz : 0 < z.re) : Continuous (fun t => holomorphicChiPair (z / (L : ℂ)) t) := by
  have hre := (scaled_displacement_re_pos hL hz).le
  have hc : Continuous (fun t : ℝ => zetaChi ((1 / 2 : ℂ) - z / (L : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (zetaChi_analyticAt (chi_shift_Gamma_ne_zero hre t)).continuousAt.comp
      (f := fun u : ℝ => (1 / 2 : ℂ) - z / (L : ℂ) + (u : ℂ) * I) (by fun_prop)
  convert hc.mul (hc.comp continuous_neg) using 1
  funext t
  exact holomorphicChiPair_opposite_heights (z / (L : ℂ)) t

/-- Every normalized displacement jet is measurable as a function of height. -/
theorem aestronglyMeasurable_scaled_holomorphicChiPair_jet {L : ℝ} (hL : 0 < L)
    (j : ℕ) {C : ℂ} (hC : 0 < C.re) :
    AEStronglyMeasurable
      (fun t : ℝ => iteratedDeriv j (fun z => holomorphicChiPair (z / (L : ℂ)) t) C) volume := by
  induction j generalizing C with
  | zero => exact (continuous_scaled_holomorphicChiPair_height hL hC).aestronglyMeasurable
  | succ j ih =>
      have hr : 0 < C.re / 2 := half_pos hC
      have hpos {v : ℂ} (hv : v ∈ ball C (C.re / 2)) : 0 < v.re := by
        have hn : ‖v - C‖ < C.re / 2 := by simpa only [mem_ball, dist_eq_norm] using hv
        have hh := (Complex.abs_re_le_norm (v - C)).trans_lt hn
        simp only [Complex.sub_re] at hh
        have hlo := (abs_lt.mp hh).1
        linarith only [hlo, hC]
      have ha (t : ℝ) (k : ℕ) : AnalyticAt ℂ
          (iteratedDeriv k (fun z => holomorphicChiPair (z / (L : ℂ)) t)) C := by
        induction k with
        | zero => exact analyticAt_scaled_holomorphicChiPair_pos hL hC t
        | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv
      simp only [iteratedDeriv_succ]
      exact aestronglyMeasurable_deriv_param_complex hr
        (fun v hv => ih (hpos hv)) (fun t => (ha t j).differentiableAt)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
