import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalSourceMellinLowFrequencyExclusion
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicIncrementEnergy
import GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage

/-!
# Logarithmic coercivity of the critical archimedean channel

The critical source `g` of a real phase combination lies in `L¹ ∩ L²`. Plancherel, its
polarization and the translation rule give the spectral form of the autocorrelation,
`ac(x) = (1/2π) ∫ ‖ĝ(t)‖² cos(tx) dt`, hence of every jump
`ac(0) - ac(x) = (1/2π) ∫ ‖ĝ(t)‖² (1 - cos(tx)) dt`. Tonelli turns the Lévy energy
`∫_{x>0} (ac(0) - ac(x)) ω(x) dx` into `(1/2π) ∫ ‖ĝ(t)‖² W(t) dt` with Lévy symbol
`W(t) = ∫_{x>0} (1 - cos(tx)) ω(x) dx ≥ e^{-1/2} (log|t| - 3)` for `|t| ≥ 1`
(from `ω(x) ≥ e^{-1/2}/x` on `(0,1]` and `|∫_1^T cos u/u du| ≤ 3`).

On scales `n + 1 ≥ M`, critical low-frequency exclusion confines at most half of the mass
`∫ g² ≥ A ∑ b_n²` to the band `|t| ≤ ηM`, so

  `Lévy(g_b) ≥ e^{-1/2} (A/2) (log M - 3 - log(1/η)) ∑ b_n²`,

uniformly in the number, size and positions of the scales.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- Critical sources are dominated by `2 (∑|b_n|) e^{x/2}` on `x ≤ 0` and vanish on `x > 0`. -/
theorem abs_criticalFactorialSource_le (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    |criticalFactorialSource S b x| ≤
      (Iic (0 : ℝ)).indicator (fun x => 2 * (∑ n ∈ S, |b n|) * Real.exp (x / 2)) x := by
  unfold criticalFactorialSource
  by_cases hx : x ∈ Iic (0 : ℝ)
  · rw [indicator_of_mem hx, indicator_of_mem hx, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine (Complex.abs_re_le_norm _).trans ?_
    unfold factorialPhaseCombination
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_factorialPhaseProfile_le (n + 1) (Real.exp (-x)), abs_nonneg (b n)]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, abs_zero]

/-- Critical sources are measurable. -/
theorem measurable_criticalFactorialSource (S : Finset ℕ) (b : ℕ → ℝ) :
    Measurable (criticalFactorialSource S b) := by
  unfold criticalFactorialSource
  refine Measurable.indicator ?_ measurableSet_Iic
  have := continuous_factorialPhaseCombination S (fun n => (b n : ℂ))
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2) *
    (factorialPhaseCombination S (fun n => (b n : ℂ)) (Real.exp (-x))).re).measurable

private theorem integrable_envelope (C : ℝ) :
    Integrable ((Iic (0 : ℝ)).indicator fun x => C * Real.exp (x / 2)) := by
  rw [integrable_indicator_iff measurableSet_Iic]
  have h : IntegrableOn (fun x => C * Real.exp (1 / 2 * x)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (by norm_num) 0).const_mul C
  exact h.congr_fun (fun x _ => by ring_nf) measurableSet_Iic

/-- Critical sources are integrable and square integrable. -/
theorem integrable_criticalFactorialSource (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (fun x => (criticalFactorialSource S b x : ℂ)) ∧
      MemLp (fun x => (criticalFactorialSource S b x : ℂ)) 2 := by
  set C := 2 * ∑ n ∈ S, |b n|
  have hC : 0 ≤ C := by positivity
  have hm : AEStronglyMeasurable (fun x => (criticalFactorialSource S b x : ℂ)) volume :=
    (Complex.measurable_ofReal.comp (measurable_criticalFactorialSource S b)).aestronglyMeasurable
  have hb (x : ℝ) : ‖(criticalFactorialSource S b x : ℂ)‖ ≤
      (Iic (0 : ℝ)).indicator (fun x => C * Real.exp (x / 2)) x := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_criticalFactorialSource_le S b x
  have h1 : Integrable (fun x => (criticalFactorialSource S b x : ℂ)) :=
    (integrable_envelope C).mono' hm (Eventually.of_forall hb)
  refine ⟨h1, (memLp_two_iff_integrable_sq_norm hm).mpr ?_⟩
  refine (integrable_envelope (C * C)).mono' (hm.norm.pow 2) (Eventually.of_forall fun x => ?_)
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := hb x
    by_cases hx : x ∈ Iic (0 : ℝ)
    · rw [indicator_of_mem hx] at h ⊢
      have he : Real.exp (x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by simp at hx; linarith)
      have h0 := norm_nonneg ((criticalFactorialSource S b x : ℂ))
      have hp := Real.exp_pos (x / 2)
      calc ‖(criticalFactorialSource S b x : ℂ)‖ ^ 2 ≤ (C * Real.exp (x / 2)) ^ 2 :=
            pow_le_pow_left₀ h0 h 2
        _ ≤ C * C * Real.exp (x / 2) := by nlinarith
    · rw [indicator_of_notMem hx] at h ⊢
      have : ‖(criticalFactorialSource S b x : ℂ)‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [this]; norm_num

/-- **Translation rule.** `paperFT (f(· - x)) t = e^{itx} paperFT f t`. -/
theorem paperFT_comp_sub_right (f : ℝ → ℂ) (x t : ℝ) :
    paperFT (fun y => f (y - x)) t = Complex.exp (Complex.I * t * x) * paperFT f t := by
  unfold paperFT
  rw [← integral_const_mul]
  have h := integral_sub_right_eq_self (μ := volume)
    (fun y => f y * Complex.exp (Complex.I * (t : ℂ) * ((y + x : ℝ) : ℂ))) x
  simp only [sub_add_cancel] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show Complex.I * (t : ℂ) * ((y + x : ℝ) : ℂ) = Complex.I * t * x + Complex.I * t * y by
    push_cast; ring, Complex.exp_add]
  ring

private theorem normSq_add_sub_mul (a e : ℂ) :
    ‖a + e * a‖ ^ 2 - ‖a - e * a‖ ^ 2 = 4 * (‖a‖ ^ 2 * e.re) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  have : (a * (starRingEnd ℂ) (e * a)).re = Complex.normSq a * e.re := by
    rw [map_mul, show a * ((starRingEnd ℂ) e * (starRingEnd ℂ) a) =
      (a * (starRingEnd ℂ) a) * (starRingEnd ℂ) e by ring, Complex.mul_conj, Complex.re_ofReal_mul,
      Complex.conj_re]
  rw [this]; ring

/-- **Spectral form of the critical autocorrelation.** For every shift `x`,
`∫ g(y) g(y - x) dy = (1/2π) ∫ ‖ĝ(t)‖² cos(tx) dt`. -/
theorem criticalFactorialSource_autocorrelation_eq_spectral (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    ∫ y, criticalFactorialSource S b y * criticalFactorialSource S b (y - x) =
      1 / (2 * Real.pi) * ∫ t : ℝ,
        ‖paperFT (fun y => (criticalFactorialSource S b y : ℂ)) t‖ ^ 2 * Real.cos (t * x) := by
  set g := criticalFactorialSource S b
  set u : ℝ → ℂ := fun y => (g y : ℂ)
  set w : ℝ → ℂ := fun y => u (y - x)
  obtain ⟨hu1, hu2⟩ := integrable_criticalFactorialSource S b
  have hum : AEStronglyMeasurable u volume := hu1.aestronglyMeasurable
  have hw1 : Integrable w := hu1.comp_sub_right x
  have hwm : AEStronglyMeasurable w volume := hw1.aestronglyMeasurable
  have hw2 : MemLp w 2 := (memLp_two_iff_integrable_sq_norm hwm).mpr
    (((memLp_two_iff_integrable_sq_norm hum).mp hu2).comp_sub_right x)
  have hp1 : Integrable (u + (1 : ℂ) • w) := hu1.add (hw1.smul _)
  have hp2 : MemLp (u + (1 : ℂ) • w) 2 := hu2.add (hw2.const_smul _)
  have hm1 : Integrable (u + (-1 : ℂ) • w) := hu1.add (hw1.smul _)
  have hm2 : MemLp (u + (-1 : ℂ) • w) 2 := hu2.add (hw2.const_smul _)
  have hPp := RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hp1 hp2
  have hPm := RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hm1 hm2
  have hIp := RHTower.KernelStrip.integrable_norm_sq_paperFT hp1 hp2
  have hIm := RHTower.KernelStrip.integrable_norm_sq_paperFT hm1 hm2
  have hFp (t : ℝ) : paperFT (u + (1 : ℂ) • w) t =
      paperFT u t + Complex.exp (Complex.I * t * x) * paperFT u t := by
    rw [RHTower.WeilSpectral.paperFT_add_smul_real hu1 hw1, paperFT_comp_sub_right, one_mul]
  have hFm (t : ℝ) : paperFT (u + (-1 : ℂ) • w) t =
      paperFT u t - Complex.exp (Complex.I * t * x) * paperFT u t := by
    rw [RHTower.WeilSpectral.paperFT_add_smul_real hu1 hw1, paperFT_comp_sub_right]; ring
  have hspec (t : ℝ) : ‖paperFT (u + (1 : ℂ) • w) t‖ ^ 2 - ‖paperFT (u + (-1 : ℂ) • w) t‖ ^ 2 =
      4 * (‖paperFT u t‖ ^ 2 * Real.cos (t * x)) := by
    rw [hFp, hFm, normSq_add_sub_mul,
      show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hphys (y : ℝ) : ‖(u + (1 : ℂ) • w) y‖ ^ 2 - ‖(u + (-1 : ℂ) • w) y‖ ^ 2 =
      4 * (g y * g (y - x)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, u, w, neg_one_mul]
    rw [← Complex.ofReal_add, ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  have hsq1 := (memLp_two_iff_integrable_sq_norm hp1.aestronglyMeasurable).mp hp2
  have hsq2 := (memLp_two_iff_integrable_sq_norm hm1.aestronglyMeasurable).mp hm2
  have hL : ∫ t : ℝ, 4 * (‖paperFT u t‖ ^ 2 * Real.cos (t * x)) =
      2 * Real.pi * ∫ y, 4 * (g y * g (y - x)) := by
    rw [← integral_congr_ae (Eventually.of_forall hspec), integral_sub hIp hIm, hPp, hPm,
      ← mul_sub, ← integral_sub hsq1 hsq2, integral_congr_ae (Eventually.of_forall hphys)]
  rw [integral_const_mul, integral_const_mul] at hL
  have hpi : 0 < Real.pi := Real.pi_pos
  have hI : ∫ t : ℝ, ‖paperFT u t‖ ^ 2 * Real.cos (t * x) = 2 * Real.pi * ∫ y, g y * g (y - x) := by
    linarith
  rw [hI]
  field_simp

/-- `|∫_1^T cos u / u du| ≤ 3` for `T ≥ 1`, by one integration by parts. -/
theorem abs_integral_cos_div_le {T : ℝ} (hT : 1 ≤ T) :
    |∫ u in (1 : ℝ)..T, Real.cos u / u| ≤ 3 := by
  have hpos : ∀ x ∈ uIcc (1 : ℝ) T, 0 < x := fun x hx => by
    rw [uIcc_of_le hT] at hx; linarith [hx.1]
  have hu : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt Real.sin (Real.cos x) x :=
    fun x _ => Real.hasDerivAt_sin x
  have hcont : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (uIcc 1 T) :=
    (continuousOn_id.pow 2).inv₀ (fun x hx => pow_ne_zero 2 (hpos x hx).ne') |>.neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcont.intervalIntegrable) (Real.continuous_cos.intervalIntegrable _ _)
  have heq : ∫ u in (1 : ℝ)..T, Real.cos u / u = ∫ u in (1 : ℝ)..T, u⁻¹ * Real.cos u :=
    intervalIntegral.integral_congr fun u _ => by ring
  rw [heq, hibp]
  have hint : |∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * Real.sin x| ≤ 1 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hT
      (g := fun x : ℝ => (x ^ 2)⁻¹) (f := fun x : ℝ => -(x ^ 2)⁻¹ * Real.sin x)
      (Eventually.of_forall fun x hx => by
        have hx0 : 0 < x := lt_trans one_pos hx.1
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity)]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one x))
      ((continuousOn_id.pow 2).inv₀ (fun x hx => pow_ne_zero 2 (hpos x hx).ne')).intervalIntegrable
    have hval : ∫ x in (1 : ℝ)..T, (x ^ 2)⁻¹ = 1 - T⁻¹ := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -x⁻¹)
        (f' := fun x : ℝ => (x ^ 2)⁻¹) (fun x hx => by
          have h := (hasDerivAt_inv (hpos x hx).ne').neg
          rw [neg_neg] at h
          exact h)
        ((continuousOn_id.pow 2).inv₀ (fun x hx => pow_ne_zero 2 (hpos x hx).ne')).intervalIntegrable
      rw [h]; simp; ring
    rw [Real.norm_eq_abs] at hb
    have hT0 : 0 < T⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have h1 : |T⁻¹ * Real.sin T| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by linarith))]
    exact (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one T)).trans (inv_le_one_of_one_le₀ hT)
  have h2 : |(1 : ℝ)⁻¹ * Real.sin 1| ≤ 1 := by
    rw [inv_one, one_mul]; exact Real.abs_sin_le_one 1
  calc |T⁻¹ * Real.sin T - 1⁻¹ * Real.sin 1 - ∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * Real.sin x| ≤
        |T⁻¹ * Real.sin T| + |(1 : ℝ)⁻¹ * Real.sin 1| +
          |∫ x in (1 : ℝ)..T, -(x ^ 2)⁻¹ * Real.sin x| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ 3 := by linarith

private theorem one_sub_cos_div_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (1 - Real.cos u) / u :=
  div_nonneg (by linarith [Real.cos_le_one u]) hu

private theorem one_sub_cos_div_le {u : ℝ} (hu : 0 ≤ u) : (1 - Real.cos u) / u ≤ u / 2 := by
  rcases hu.lt_or_eq with hu | rfl
  · rw [div_le_iff₀ hu]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := u)]
  · simp

private theorem intervalIntegrable_one_sub_cos_div (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => (1 - Real.cos u) / u) volume 0 T := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => T / 2) intervalIntegrable_const
    ((by fun_prop : Measurable fun u : ℝ => (1 - Real.cos u) / u).aestronglyMeasurable) ?_
  rw [uIoc_of_le hT]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_div_nonneg hu.1.le)]
  exact (one_sub_cos_div_le hu.1.le).trans (by linarith [hu.2])

/-- `∫_0^T (1 - cos u)/u du ≥ log T - 3` for `T ≥ 1`. -/
theorem log_sub_three_le_integral_one_sub_cos_div {T : ℝ} (hT : 1 ≤ T) :
    Real.log T - 3 ≤ ∫ u in (0 : ℝ)..T, (1 - Real.cos u) / u := by
  have hi0 := intervalIntegrable_one_sub_cos_div 1 zero_le_one
  have hiT := intervalIntegrable_one_sub_cos_div T (by linarith)
  have hi1T : IntervalIntegrable (fun u : ℝ => (1 - Real.cos u) / u) volume 1 T :=
    (hi0.symm.trans hiT)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1T]
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..1, (1 - Real.cos u) / u :=
    intervalIntegral.integral_nonneg zero_le_one fun u hu => one_sub_cos_div_nonneg hu.1
  have hpos : ∀ x ∈ uIcc (1 : ℝ) T, 0 < x := fun x hx => by
    rw [uIcc_of_le hT] at hx; linarith [hx.1]
  have hinv : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 T :=
    (continuousOn_const.div continuousOn_id fun x hx => (hpos x hx).ne').intervalIntegrable
  have hcos : IntervalIntegrable (fun u : ℝ => Real.cos u / u) volume 1 T :=
    (Real.continuous_cos.continuousOn.div continuousOn_id fun x hx => (hpos x hx).ne').intervalIntegrable
  have hsplit : ∫ u in (1 : ℝ)..T, (1 - Real.cos u) / u =
      (∫ u in (1 : ℝ)..T, 1 / u) - ∫ u in (1 : ℝ)..T, Real.cos u / u := by
    rw [← intervalIntegral.integral_sub hinv hcos]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [hsplit, integral_one_div_of_pos one_pos (by linarith), div_one]
  have := abs_integral_cos_div_le hT
  have := neg_abs_le (∫ u in (1 : ℝ)..T, Real.cos u / u)
  have := le_abs_self (∫ u in (1 : ℝ)..T, Real.cos u / u)
  linarith

private theorem cos_abs_mul (t x : ℝ) : Real.cos (|t| * x) = Real.cos (t * x) := by
  rcases abs_choice t with h | h <;> rw [h]
  rw [neg_mul, Real.cos_neg]

private theorem one_sub_cos_mul_div_le (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1 - Real.cos (t * x)) / x ≤ t ^ 2 * x / 2 := by
  rcases hx.lt_or_eq with hx | rfl
  · rw [div_le_iff₀ hx]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t * x)]
  · simp

private theorem intervalIntegrable_one_sub_cos_mul_div (t : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1 - Real.cos (t * x)) / x) volume 0 1 := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => t ^ 2 / 2) intervalIntegrable_const
    ((by fun_prop : Measurable fun x : ℝ => (1 - Real.cos (t * x)) / x).aestronglyMeasurable) ?_
  rw [uIoc_of_le zero_le_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hnn : 0 ≤ (1 - Real.cos (t * x)) / x := div_nonneg (by linarith [Real.cos_le_one (t * x)]) hx.1.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  refine (one_sub_cos_mul_div_le t hx.1.le).trans ?_
  have := sq_nonneg t
  nlinarith [hx.2]

/-- Rescaling: `∫_0^1 (1 - cos(tx))/x dx = ∫_0^{|t|} (1 - cos u)/u du` for `t ≠ 0`. -/
theorem integral_one_sub_cos_mul_div_eq {t : ℝ} (ht : t ≠ 0) :
    ∫ x in (0 : ℝ)..1, (1 - Real.cos (t * x)) / x = ∫ u in (0 : ℝ)..|t|, (1 - Real.cos u) / u := by
  have hc : 0 < |t| := abs_pos.mpr ht
  have hpt : ∀ x : ℝ, (1 - Real.cos (t * x)) / x = |t| * ((1 - Real.cos (|t| * x)) / (|t| * x)) := by
    intro x
    rw [cos_abs_mul]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  rw [intervalIntegral.integral_congr fun x _ => hpt x, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun u => (1 - Real.cos u) / u) hc.ne', smul_eq_mul,
    mul_zero, mul_one, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Logarithmic growth of the Lévy symbol.** For `|t| ≥ 1`,
`∫_{x>0} (1 - cos(tx)) ω(x) dx ≥ e^{-1/2} (log|t| - 3)`. -/
theorem ofReal_log_sub_le_lintegral_one_sub_cos_mul_archLevySinhWeight {t : ℝ} (ht : 1 ≤ |t|) :
    ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (Real.log |t| - 3)) ≤
      ∫⁻ x in Ioi 0, ENNReal.ofReal ((1 - Real.cos (t * x)) *
        BiScaleUncertainty.archLevySinhWeight x) := by
  have ht0 : t ≠ 0 := abs_pos.mp (lt_of_lt_of_le one_pos ht)
  set c : ℝ := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hint := intervalIntegrable_one_sub_cos_mul_div t
  have hintOn : IntegrableOn (fun x : ℝ => c * ((1 - Real.cos (t * x)) / x)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint).const_mul c
  have hval : ∫ x in Ioc (0 : ℝ) 1, c * ((1 - Real.cos (t * x)) / x) =
      c * ∫ u in (0 : ℝ)..|t|, (1 - Real.cos u) / u := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_one_sub_cos_mul_div_eq ht0]
  have hlow := log_sub_three_le_integral_one_sub_cos_div ht
  calc ENNReal.ofReal (c * (Real.log |t| - 3)) ≤
        ENNReal.ofReal (∫ x in Ioc (0 : ℝ) 1, c * ((1 - Real.cos (t * x)) / x)) := by
        rw [hval]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlow hc.le)
    _ = ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (c * ((1 - Real.cos (t * x)) / x)) :=
        ofReal_integral_eq_lintegral_ofReal hintOn
          (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
            mul_nonneg hc.le (div_nonneg (by linarith [Real.cos_le_one (t * x)]) hx.1.le))
    _ ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - Real.cos (t * x)) *
          BiScaleUncertainty.archLevySinhWeight x) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hω := BiScaleUncertainty.exp_neg_half_div_le_archLevySinhWeight hx.1 hx.2
        have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
        calc c * ((1 - Real.cos (t * x)) / x) = (1 - Real.cos (t * x)) * (c / x) := by ring
          _ ≤ (1 - Real.cos (t * x)) * BiScaleUncertainty.archLevySinhWeight x :=
              mul_le_mul_of_nonneg_left hω h1
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-- Autocorrelation `ac(x) = ∫ g(y) g(y - x) dy` of a critical source. -/
def criticalAutocorrelation (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, criticalFactorialSource S b y * criticalFactorialSource S b (y - x)

/-- Lévy jump energy `∫_{x>0} (ac(0) - ac(x)) ω(x) dx` of a critical source. -/
def criticalLevyEnergy (S : Finset ℕ) (b : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi 0, ENNReal.ofReal ((criticalAutocorrelation S b 0 - criticalAutocorrelation S b x) *
    BiScaleUncertainty.archLevySinhWeight x)

/-- Spectral density `‖ĝ(t)‖²` of a critical source. -/
def criticalSpectralDensity (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ‖paperFT (fun y => (criticalFactorialSource S b y : ℂ)) t‖ ^ 2

/-- The spectral density is integrable. -/
theorem integrable_criticalSpectralDensity (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (criticalSpectralDensity S b) := by
  obtain ⟨h1, h2⟩ := integrable_criticalFactorialSource S b
  exact RHTower.KernelStrip.integrable_norm_sq_paperFT h1 h2

/-- The spectral density is continuous. -/
theorem continuous_criticalSpectralDensity (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (criticalSpectralDensity S b) :=
  ((RHTower.WeilHerglotz.continuous_paperFT_real (integrable_criticalFactorialSource S b).1).norm).pow 2

/-- **Plancherel.** `∫ ‖ĝ‖² = 2π ∫ g²`. -/
theorem integral_criticalSpectralDensity (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ t, criticalSpectralDensity S b t = 2 * Real.pi * ∫ y, criticalFactorialSource S b y ^ 2 := by
  obtain ⟨h1, h2⟩ := integrable_criticalFactorialSource S b
  unfold criticalSpectralDensity
  rw [RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp h1 h2]
  congr 2
  funext y
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Spectral form of the jump.** `ac(0) - ac(x) = (1/2π) ∫ ‖ĝ(t)‖² (1 - cos(tx)) dt`. -/
theorem criticalAutocorrelation_jump_eq_spectral (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalAutocorrelation S b 0 - criticalAutocorrelation S b x =
      1 / (2 * Real.pi) * ∫ t, criticalSpectralDensity S b t * (1 - Real.cos (t * x)) := by
  have hi := integrable_criticalSpectralDensity S b
  have hc := continuous_criticalSpectralDensity S b
  have hic : Integrable fun t => criticalSpectralDensity S b t * Real.cos (t * x) := by
    refine hi.mono' (by fun_prop : Continuous fun t =>
      criticalSpectralDensity S b t * Real.cos (t * x)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have h0 : 0 ≤ criticalSpectralDensity S b t := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right h0 (Real.abs_cos_le_one _)
  have h0 := criticalFactorialSource_autocorrelation_eq_spectral S b 0
  have hx := criticalFactorialSource_autocorrelation_eq_spectral S b x
  simp only [mul_zero, Real.cos_zero, mul_one] at h0
  unfold criticalAutocorrelation
  unfold criticalSpectralDensity at hi hic ⊢
  rw [h0, hx, ← mul_sub, ← integral_sub hi hic]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring

/-- **High-band lower bound of the critical Lévy energy.** For `R ≥ 1`, the Lévy energy dominates
`e^{-1/2} (log R - 3)` times the spectral mass `(1/2π) ∫_{|t|>R} ‖ĝ‖²`. Tonelli exchanges the
jump integral with the spectral integral of `‖ĝ(t)‖² (1 - cos(tx))`. -/
theorem criticalLevyEnergy_ge_highBand (S : Finset ℕ) (b : ℕ → ℝ) {R : ℝ} (hR : 1 ≤ R) :
    ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) *
      ENNReal.ofReal (1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, criticalSpectralDensity S b t) ≤
    criticalLevyEnergy S b := by
  set m := criticalSpectralDensity S b
  set ω := BiScaleUncertainty.archLevySinhWeight
  set K := ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3))
  have hm0 (t : ℝ) : 0 ≤ m t := sq_nonneg _
  have hmi := integrable_criticalSpectralDensity S b
  have hmc := continuous_criticalSpectralDensity S b
  have hpi : 0 < Real.pi := Real.pi_pos
  set F : ℝ → ℝ → ℝ≥0∞ := fun x t =>
    ENNReal.ofReal (ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))))
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal ((criticalAutocorrelation S b 0 -
      criticalAutocorrelation S b x) * ω x) = ∫⁻ t, F x t := by
    intro x hx
    rw [criticalAutocorrelation_jump_eq_spectral]
    have hω := (BiScaleUncertainty.archLevySinhWeight_pos hx).le
    have hint : Integrable fun t => ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))) := by
      refine ((hmi.const_mul 2).const_mul (ω x / (2 * Real.pi))).mono'
        (by fun_prop : Continuous fun t => ω x / (2 * Real.pi) *
          (m t * (1 - Real.cos (t * x)))).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
      have h2 : 1 - Real.cos (t * x) ≤ 2 := by linarith [Real.neg_one_le_cos (t * x)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hm0 t; positivity)]
      change ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))) ≤ ω x / (2 * Real.pi) * (2 * m t)
      have := hm0 t
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by
      have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
      have := hm0 t
      show 0 ≤ ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x)))
      positivity)]
    congr 1
    rw [integral_const_mul]; ring
  have hmeas : AEMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aemeasurable ?_
    change Measurable fun p : ℝ × ℝ => ENNReal.ofReal (ω p.1 / (2 * Real.pi) *
      (m p.2 * (1 - Real.cos (p.2 * p.1))))
    refine Measurable.ennreal_ofReal ?_
    exact ((BiScaleUncertainty.measurable_archLevySinhWeight.comp measurable_fst).div_const _).mul
      ((hmc.measurable.comp measurable_snd).mul (measurable_const.sub
        (Real.continuous_cos.measurable.comp (measurable_snd.mul measurable_fst))))
  have hinner (t : ℝ) : (Icc (-R) R)ᶜ.indicator (fun t => ENNReal.ofReal (m t / (2 * Real.pi)) * K) t ≤
      ∫⁻ x in Ioi 0, F x t := by
    by_cases ht : t ∈ (Icc (-R) R)ᶜ
    · rw [indicator_of_mem ht]
      have hF : ∀ x, F x t = ENNReal.ofReal (m t / (2 * Real.pi)) *
          ENNReal.ofReal ((1 - Real.cos (t * x)) * ω x) := by
        intro x
        simp only [F]
        rw [← ENNReal.ofReal_mul (by have := hm0 t; positivity)]
        congr 1; ring
      rw [lintegral_congr fun x => hF x, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      have hRt : R < |t| := by
        by_contra hle
        exact ht (abs_le.mp (not_lt.mp hle))
      have h1 : 1 ≤ |t| := hR.trans hRt.le
      refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (ofReal_log_sub_le_lintegral_one_sub_cos_mul_archLevySinhWeight h1)
      have := Real.log_le_log (by linarith) hRt.le
      have := Real.exp_pos (-(1 / 2 : ℝ))
      nlinarith
    · rw [indicator_of_notMem ht]; exact zero_le
  have hIc : IntegrableOn m (Icc (-R) R)ᶜ := hmi.integrableOn
  calc K * ENNReal.ofReal (1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, m t) =
        K * ∫⁻ t in (Icc (-R) R)ᶜ, ENNReal.ofReal (m t / (2 * Real.pi)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hIc.div_const _)
          (Eventually.of_forall fun t => by have := hm0 t; positivity), integral_div]
        congr 2; ring
    _ = ∫⁻ t, (Icc (-R) R)ᶜ.indicator (fun t => ENNReal.ofReal (m t / (2 * Real.pi)) * K) t := by
        rw [lintegral_indicator measurableSet_Icc.compl, lintegral_mul_const' _ _
          ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ ∫⁻ t, ∫⁻ x in Ioi 0, F x t := lintegral_mono hinner
    _ = ∫⁻ x in Ioi 0, ∫⁻ t, F x t := (lintegral_lintegral_swap hmeas).symm
    _ = criticalLevyEnergy S b := by
        unfold criticalLevyEnergy
        exact (setLIntegral_congr_fun measurableSet_Ioi hpt).symm

/-- **Critical mass floor.** `∫ g² ≥ A ∑ b_n²` with the weighted Riesz constant `A`. -/
theorem integral_criticalFactorialSource_sq_ge (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialWeightedPhaseLower * ∑ n ∈ S, b n ^ 2 ≤ ∫ y, criticalFactorialSource S b y ^ 2 := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ))
  have hcorr := criticalFactorialSource_correlation_eq S b (r := 1) le_rfl
  simp only [Real.log_one, sub_zero, Real.sqrt_one, inv_one, one_mul] at hcorr
  have hsq : (fun y => criticalFactorialSource S b y ^ 2) =
      fun y => criticalFactorialSource S b y * criticalFactorialSource S b y := funext fun y => sq _
  rw [hsq, hcorr]
  have hlow := factorialPhaseCombination_weighted_lower S (fun n => (b n : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hlow
  refine hlow.trans ?_
  have hBc : Continuous B := continuous_factorialPhaseCombination S _
  set C := 2 * ∑ n ∈ S, |b n|
  have hBb (v : ℝ) : ‖B v‖ ≤ C := by
    calc ‖B v‖ ≤ ∑ n ∈ S, ‖(b n : ℂ) * (factorialPhaseProfile (n + 1) v : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, 2 * |b n| := Finset.sum_le_sum fun n _ => by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          nlinarith [abs_factorialPhaseProfile_le (n + 1) v, abs_nonneg (b n)]
      _ = C := by rw [← Finset.mul_sum]
  have hreal (v : ℝ) : ‖B v‖ = |(B v).re| := by
    calc ‖B v‖ = ‖(((B v).re : ℝ) : ℂ)‖ := by
          rw [show (((B v).re : ℝ) : ℂ) = B v from factorialPhaseCombination_ofReal_re S b v]
      _ = |(B v).re| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hrc (q : ℝ) : ContinuousOn (fun v : ℝ => v ^ q) (Ioi 1) :=
    continuousOn_id.rpow_const fun v hv => Or.inl (ne_of_gt (lt_trans one_pos hv))
  have hi4 : IntegrableOn (fun v : ℝ => v ^ (-4 : ℝ) * ‖B v‖ ^ 2) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (a := -4) (by norm_num) zero_lt_one).mul_const (C ^ 2)).mono'
      (((hrc _).mul (hBc.norm.pow 2).continuousOn).aestronglyMeasurable measurableSet_Ioi) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := lt_trans one_pos hv
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hBb v) 2)
        (Real.rpow_nonneg hv0.le _)
  have hi2 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ) * (B v).re * (B v).re) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) zero_lt_one).mul_const (C ^ 2)).mono'
      ((((hrc _).mul (Complex.continuous_re.comp hBc).continuousOn).mul
        (Complex.continuous_re.comp hBc).continuousOn).aestronglyMeasurable measurableSet_Ioi) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := lt_trans one_pos hv
      have hre : |(B v).re| ≤ C := (Complex.abs_re_le_norm _).trans (hBb v)
      rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _), abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hv0.le _)
      nlinarith [abs_nonneg (B v).re]
  refine setIntegral_mono_on hi4 hi2 measurableSet_Ioi fun v hv => ?_
  have hv1 : 1 ≤ v := le_of_lt hv
  have hv0 : 0 < v := lt_trans one_pos hv
  have hw : v ^ (-4 : ℝ) ≤ v ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  rw [hreal, sq_abs, mul_assoc, ← sq]
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

/-- Slope `e^{-1/2} A/2` of the logarithmic growth of the critical Lévy energy. -/
def criticalArchLogSlope : ℝ :=
  Real.exp (-(1 / 2 : ℝ)) * (factorialWeightedPhaseLower / 2)

/-- Offset `3 + log(1/η)` of the logarithmic growth of the critical Lévy energy. -/
def criticalArchLogOffset : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff factorialWeightedPhaseLower factorialLowFreqConstant)

/-- The logarithmic slope is positive. -/
theorem criticalArchLogSlope_pos : 0 < criticalArchLogSlope := by
  unfold criticalArchLogSlope
  have := factorialWeightedPhaseLower_pos
  positivity

/-- **Critical high-scale archimedean coercivity.** For every finite family supported on scales
`n + 1 ≥ M ≥ 2` and every real coefficient vector,
`Lévy(g_b) ≥ e^{-1/2} (A/2) (log M - 3 - log(1/η)) ∑ b_n²`, uniformly in the number, size and
positions of the scales. -/
theorem ofReal_le_criticalLevyEnergy (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1) :
    ENNReal.ofReal (criticalArchLogSlope * (Real.log M - criticalArchLogOffset) *
      ∑ n ∈ S, b n ^ 2) ≤ criticalLevyEnergy S b := by
  set A := factorialWeightedPhaseLower
  set D := factorialLowFreqConstant
  set η := lowFreqRelativeCutoff A D
  set E := ∑ n ∈ S, b n ^ 2
  have hA : 0 < A := factorialWeightedPhaseLower_pos
  have hD : 0 < D := factorialLowFreqConstant_pos
  have hη : 0 < η := lowFreqRelativeCutoff_pos hA hD
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - criticalArchLogOffset = Real.log R - 3 := by
    unfold criticalArchLogOffset
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]; ring
  rw [hlogR]
  rcases le_or_gt (Real.log R - 3) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have := criticalArchLogSlope_pos
      have : criticalArchLogSlope * (Real.log R - 3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this.le hneg
      nlinarith
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  have hhigh := criticalLevyEnergy_ge_highBand S b hR1
  have hmi := integrable_criticalSpectralDensity S b
  have hlowband : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, criticalSpectralDensity S b t ≤ A / 2 * E := by
    have hpt : ∀ t ∈ Icc (-R) R, criticalSpectralDensity S b t ≤ 2 * D ^ 2 / M * E := by
      intro t ht
      refine norm_sq_paperFT_criticalFactorialSource_le S b hM hS ?_
      have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
      calc |t| ≤ R := abs_le.mpr ht
        _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
    have hint : (∫ t in Icc (-R) R, criticalSpectralDensity S b t) ≤ (2 * R) * (2 * D ^ 2 / M * E) := by
      calc (∫ t in Icc (-R) R, criticalSpectralDensity S b t) ≤
            ∫ _t in Icc (-R) R, 2 * D ^ 2 / M * E :=
            setIntegral_mono_on hmi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc hpt
        _ = (2 * R) * (2 * D ^ 2 / M * E) := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    calc 1 / (2 * Real.pi) * (∫ t in Icc (-R) R, criticalSpectralDensity S b t) ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) := mul_le_mul_of_nonneg_left hint hpi.le
      _ = (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E / (M : ℝ)) := by ring
      _ ≤ (A / 2) * E := low_band_plancherel_energy_le_half_arch hD hE hM
  have hmass := integral_criticalFactorialSource_sq_ge S b
  have htot := integral_criticalSpectralDensity S b
  have hsplit := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmi
  have hhighmass : A / 2 * E ≤ 1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, criticalSpectralDensity S b t := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : 1 / (2 * Real.pi) * ∫ t, criticalSpectralDensity S b t = ∫ y, criticalFactorialSource S b y ^ 2 := by
      rw [htot]; field_simp
    rw [← hsplit, mul_add] at h1
    linarith
  refine le_trans ?_ hhigh
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  rw [show criticalArchLogSlope * (Real.log R - 3) * E =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) * (A / 2 * E) by unfold criticalArchLogSlope; ring,
    ENNReal.ofReal_mul hc0]
  gcongr

end

end GaloisForLFunctions.ArithmeticPositivityTheory
