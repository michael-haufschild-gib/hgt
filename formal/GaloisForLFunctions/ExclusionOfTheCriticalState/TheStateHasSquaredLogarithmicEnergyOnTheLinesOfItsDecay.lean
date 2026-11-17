import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateEquationHoldsOnTheZeroFreePartOfTheStrip
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadIsAHardyTransform
import GaloisForLFunctions.ExclusionOfTheCriticalState.LogarithmicEnergiesInterpolateBetweenVerticalLines

/-!
# The state has a squared logarithmic energy on the lines of its decay

On a line `Re p = s`, `κ < s < 1/2`, to the right of the centred zeros the state equation reads
`L F(p) A(p) = R(p)` with the multiplier `A = 2θ'(0) + g + N(1/2 + ·) - 1/(· - 1/2)`.

* The Gamma symbol dominates: `Re (2θ'(0) + g(s + it)) ≥ 2θ'(t) + g(s) ≥ log(|t| + 4) - C`, since
  `2 - 2cosh(sx)cos(tx) ≥ (2 - 2cos(tx)) + (2 - 2cosh(sx))` under the Lévy measure, while the
  regular part `N` of `ζ'/ζ` is sublogarithmic. Hence `|A(s + it)| ≥ log(|t| + 4)/2 - K`.
* Every term of `R` is square integrable on the line: `L F(p - 8)` by Plancherel as soon as
  `∫ F² e^{-bu} < ∞` for some `b > 16 - 2s`, the shifted head term as a Hardy function, the prime
  tail by Cauchy–Schwarz over the prime powers and Plancherel for the truncated profiles.

Therefore `∫ log(|t| + 4)² |L F(s + it)|² dt < ∞`: on the lines where the state decays its
transform carries two logarithms, one more than the Gamma energy of the domain provides.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The symbol grows logarithmically on every line of the strip -/

theorem integrableOn_levySymbol_integrand {s : ℝ} (hs : s < 1 / 2) {z : ℂ} (hz : |z.re| ≤ s) :
    IntegrableOn (fun x : ℝ => (archLevyDensity x : ℂ) * (2 - cexp (-(z * x)) - cexp (z * x)))
      (Ioi 0) := by
  obtain ⟨g, hg, hbound⟩ := exists_levySymbol_dominator hs (P := max 1 ‖z‖) (le_max_left _ _)
  refine Integrable.mono' hg ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun x hx => hbound x hx z hz (le_max_right _ _)))
  exact ((Complex.measurable_ofReal.comp measurable_archLevyDensity').mul
    (by fun_prop : Continuous fun x : ℝ =>
      (2 : ℂ) - cexp (-(z * (x : ℂ))) - cexp (z * (x : ℂ))).measurable).aestronglyMeasurable

theorem re_levySymbol_integrand (z : ℂ) (x : ℝ) :
    ((archLevyDensity x : ℂ) * (2 - cexp (-(z * x)) - cexp (z * x))).re =
      archLevyDensity x *
        (2 - (Real.exp (-(z.re * x)) + Real.exp (z.re * x)) * Real.cos (z.im * x)) := by
  have h1 : (z * (x : ℂ)).re = z.re * x := by simp
  have h2 : (z * (x : ℂ)).im = z.im * x := by simp
  have h3 : ((2 : ℂ)).re = 2 := by simp
  rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.sub_re, Complex.exp_re, Complex.exp_re,
    Complex.neg_re, Complex.neg_im, h1, h2, h3, Real.cos_neg]
  ring

/-- The real part of the symbol is the integral of the real part of its integrand. -/
theorem re_levySymbol_eq_integral {s : ℝ} (hs : s < 1 / 2) {z : ℂ} (hz : |z.re| ≤ s) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
        (2 - (Real.exp (-(z.re * x)) + Real.exp (z.re * x)) * Real.cos (z.im * x))) (Ioi 0) ∧
      (levySymbol z).re = ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        (2 - (Real.exp (-(z.re * x)) + Real.exp (z.re * x)) * Real.cos (z.im * x)) := by
  have i := integrableOn_levySymbol_integrand hs hz
  have h1 := Complex.reCLM.integrable_comp i
  have h2 := Complex.reCLM.integral_comp_comm i
  simp only [Complex.reCLM_apply, re_levySymbol_integrand] at h1 h2
  exact ⟨h1, h2.symm⟩

/-- `Re g(s + it) ≥ Re g(it) + Re g(s)`: under the Lévy measure
`2 - 2cosh(sx)cos(tx) ≥ (2 - 2cos(tx)) + (2 - 2cosh(sx))`. -/
theorem re_levySymbol_add_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (t : ℝ) :
    (levySymbol ((t : ℂ) * I)).re + (levySymbol (s : ℂ)).re ≤
      (levySymbol ((s : ℂ) + (t : ℂ) * I)).re := by
  have a1 : ((t : ℂ) * I).re = 0 := by simp
  have b1 : ((t : ℂ) * I).im = t := by simp
  have a3 : ((s : ℂ) + (t : ℂ) * I).re = s := by simp
  have b3 : ((s : ℂ) + (t : ℂ) * I).im = t := by simp
  obtain ⟨i1, e1⟩ := re_levySymbol_eq_integral hs (z := (t : ℂ) * I)
    (by rw [a1, abs_zero]; exact hs0)
  obtain ⟨i2, e2⟩ := re_levySymbol_eq_integral hs (z := (s : ℂ))
    (by rw [Complex.ofReal_re, abs_of_nonneg hs0])
  obtain ⟨i3, e3⟩ := re_levySymbol_eq_integral hs (z := (s : ℂ) + (t : ℂ) * I)
    (by rw [a3, abs_of_nonneg hs0])
  rw [a1, b1] at i1 e1
  rw [Complex.ofReal_re, Complex.ofReal_im] at i2 e2
  rw [a3, b3] at i3 e3
  rw [e1, e2, e3, ← integral_add i1 i2]
  refine setIntegral_mono_on (i1.add i2) i3 measurableSet_Ioi fun x hx => ?_
  have hω := (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
  have hE : 2 ≤ Real.exp (-(s * x)) + Real.exp (s * x) := by
    linarith [Real.add_one_le_exp (s * x), Real.add_one_le_exp (-(s * x))]
  have hc := Real.cos_le_one (t * x)
  have hprod := mul_nonneg hω (mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hc))
  simp only [zero_mul, neg_zero, Real.exp_zero, Real.cos_zero]
  nlinarith

/-- **The symbol grows logarithmically on every line of the strip.** For `0 ≤ s < 1/2`,
`Re (2θ'(0) + g(s + it)) ≥ log(|t| + 4) - (10 + 2 log 4) + g(s)`. -/
theorem log_sub_le_re_symbol {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (t : ℝ) :
    Real.log (|t| + 4) - (10 + 2 * Real.log 4) + (levySymbol (s : ℂ)).re ≤
      (2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol ((s : ℂ) + (t : ℂ) * I)).re := by
  have h1 := re_levySymbol_add_le hs0 hs t
  have h2 := congrArg Complex.re (levySymbol_mul_I t)
  have h3 : (2 * (gammaHardyPhaseRate 0 : ℂ)).re = 2 * gammaHardyPhaseRate 0 := by simp
  have h4 : (2 * (gammaHardyPhaseRate t : ℂ)).re = 2 * gammaHardyPhaseRate t := by simp
  rw [Complex.add_re, h3, h4] at h2
  rw [Complex.add_re, h3]
  have h5 := WeilWorkPBAP.joint_gamma_lower_log t
  rw [gammaBracket_eq_two_mul_gammaHardyPhaseRate] at h5
  have h6 : Real.log (|t| + 4) ≤ Real.log 4 + Real.log (2 + |t|) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < |t| + 4)
      (show |t| + 4 ≤ 4 * (2 + |t|) by linarith [abs_nonneg t])
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  linarith

/-! ### A sublinear power is at most half the variable plus a constant -/

theorem exists_mul_rpow_le_half_add {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → C * x ^ θ ≤ x / 2 + K := by
  have h1θ : 0 < 1 - θ := by linarith
  refine ⟨C * (2 * C) ^ (1 / (1 - θ)), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsplit : x = x ^ θ * x ^ (1 - θ) := by
    rw [← Real.rpow_add hx0, add_sub_cancel, Real.rpow_one]
  have hθpos : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  have hK : 0 ≤ C * (2 * C) ^ (1 / (1 - θ)) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  rcases le_or_gt (2 * C) (x ^ (1 - θ)) with h | h
  · have h2 : x ^ θ * (2 * C) ≤ x := by
      calc x ^ θ * (2 * C) ≤ x ^ θ * x ^ (1 - θ) := mul_le_mul_of_nonneg_left h hθpos
        _ = x := hsplit.symm
    linarith
  · have hxle : x ≤ (2 * C) ^ (1 / (1 - θ)) := by
      have h2 : x = (x ^ (1 - θ)) ^ (1 / (1 - θ)) := by
        rw [← Real.rpow_mul hx0.le, mul_one_div_cancel h1θ.ne', Real.rpow_one]
      rw [h2]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) h.le (one_div_nonneg.mpr h1θ.le)
    have hle : x ^ θ ≤ x := by
      calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ.le
        _ = x := Real.rpow_one x
    have h3 := mul_le_mul_of_nonneg_left (hle.trans hxle) hC
    linarith

/-! ### The transform of a decaying profile on a line -/

/-- The damped or tilted copy `e^{σu} F` is integrable and square integrable as soon as
`∫ F² e^{-bu} < ∞` with `-2σ < b`. -/
theorem integrable_exp_min_mul_of_decay {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b σ : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hσ : -(2 * σ) < b) :
    (Integrable fun u : ℝ => Real.exp (σ * min u 0) * F u) ∧
      Integrable fun u : ℝ => (Real.exp (σ * min u 0) * F u) ^ 2 := by
  have hHm : Measurable fun u : ℝ => Real.exp (σ * min u 0) * F u :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.min continuous_const))).measurable.mul hFm
  refine ⟨?_, ?_⟩
  · refine (integrable_abs_mul_exp_neg_of_decay hFm hsupp hb (m := -σ) (by linarith)).mono'
      hHm.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rcases le_or_gt 0 u with hu | hu
    · rw [hsupp u hu]
      simp
    · have e : Real.exp (σ * u) = Real.exp (-(-σ * u)) := by
        congr 1
        ring
      rw [min_eq_left hu.le, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), e]
      exact le_of_eq (mul_comm _ _)
  · refine hb.mono' (hHm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rcases le_or_gt 0 u with hu | hu
    · rw [hsupp u hu]
      simp
    · have hprod := mul_neg_of_pos_of_neg (show 0 < 2 * σ + b by linarith) hu
      have he : Real.exp (σ * u) ^ 2 ≤ Real.exp (-(b * u)) := by
        rw [sq, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [min_eq_left hu.le, Real.norm_of_nonneg (sq_nonneg _)]
      calc (Real.exp (σ * u) * F u) ^ 2 = F u ^ 2 * Real.exp (σ * u) ^ 2 := by ring
        _ ≤ F u ^ 2 * Real.exp (-(b * u)) := mul_le_mul_of_nonneg_left he (sq_nonneg _)

/-- **Plancherel on a line of decay.** If `∫ F² e^{-bu} < ∞`, the transform is square integrable
on every line `Re z = σ` with `-2σ < b`. -/
theorem integrable_norm_sq_laplace_line_of_decay {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b σ : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hσ : -(2 * σ) < b) :
    Integrable fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨hi, h2⟩ := integrable_exp_min_mul_of_decay hFm hsupp hb hσ
  refine (integrable_norm_sq_paperFT_cx hi h2).congr (Eventually.of_forall fun t => ?_)
  show ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 =
    ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  rw [negativeHalfLineLaplace_add_mul_I_eq_paperFT hsupp σ t]

/-- The head term is square integrable on every line `Re p = σ < 0`. -/
theorem integrable_norm_sq_levyHeadTerm_line {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {σ : ℝ} (hσ : σ < 0) :
    Integrable fun t : ℝ => ‖levyHeadTerm G ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hm := (isHalfPlaneHardy_levyHeadTerm hG).memLp (-σ) (by linarith)
  have hint := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  have h2π : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine (integrable_comp_mul_left_iff
    (fun t : ℝ => ‖levyHeadTerm G ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) h2π).mp
    (hint.congr (Eventually.of_forall fun ξ => ?_))
  show ‖levyHeadTerm G (-rayLine (-σ) ξ)‖ ^ 2 =
    ‖levyHeadTerm G ((σ : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I)‖ ^ 2
  have e : -rayLine (-σ) ξ = (σ : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I := by
    unfold rayLine
    push_cast
    ring
  rw [e]

/-! ### The prime tail on a line -/

/-- The profile of one term of the prime tail on the line `Re p = s`: the part of `F` beyond
`-ℓ`, damped by `e^{s(u + ℓ)}`. -/
def tailProfile (F : ℝ → ℝ) (s ℓ : ℝ) (u : ℝ) : ℝ :=
  if u < -ℓ then Real.exp (s * (u + ℓ)) * F u else 0

theorem measurable_tailProfile {F : ℝ → ℝ} (hFm : Measurable F) (s ℓ : ℝ) :
    Measurable (tailProfile F s ℓ) := by
  show Measurable fun u : ℝ => if u < -ℓ then Real.exp (s * (u + ℓ)) * F u else 0
  exact Measurable.ite measurableSet_Iio
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (s * (u + ℓ))).measurable.mul hFm)
    measurable_const

theorem abs_tailProfile_le {F : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (ℓ u : ℝ) :
    |tailProfile F s ℓ u| ≤ |F u| := by
  unfold tailProfile
  split_ifs with h
  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs (by linarith)))
  · rw [abs_zero]
    exact abs_nonneg _

theorem sq_tailProfile_le {F : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (ℓ u : ℝ) :
    tailProfile F s ℓ u ^ 2 ≤ Real.exp (-(8 * ℓ)) * (F u ^ 2 * Real.exp (-(8 * u))) := by
  have h0 : 0 ≤ Real.exp (-(8 * ℓ)) * (F u ^ 2 * Real.exp (-(8 * u))) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  unfold tailProfile
  split_ifs with h
  · have e1 : Real.exp (s * (u + ℓ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs (by linarith))
    have e2 : 1 ≤ Real.exp (-(8 * ℓ)) * Real.exp (-(8 * u)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have e3 : Real.exp (s * (u + ℓ)) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le e1
    calc (Real.exp (s * (u + ℓ)) * F u) ^ 2 = Real.exp (s * (u + ℓ)) ^ 2 * F u ^ 2 := by ring
      _ ≤ 1 * F u ^ 2 := mul_le_mul_of_nonneg_right e3 (sq_nonneg _)
      _ ≤ Real.exp (-(8 * ℓ)) * Real.exp (-(8 * u)) * F u ^ 2 :=
          mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
      _ = _ := by ring
  · rw [zero_pow two_ne_zero]
    exact h0

theorem integrable_tailProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {s : ℝ}
    (hs : 0 ≤ s) (ℓ : ℝ) : Integrable (tailProfile F s ℓ) :=
  hF.integrable.abs.mono' (measurable_tailProfile hF.meas s ℓ).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact abs_tailProfile_le hs ℓ u)

theorem integrable_sq_tailProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {s : ℝ}
    (hs : 0 ≤ s) (ℓ : ℝ) : Integrable fun u => tailProfile F s ℓ u ^ 2 :=
  (hF.exponential.const_mul (Real.exp (-(8 * ℓ)))).mono'
    ((measurable_tailProfile hF.meas s ℓ).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_tailProfile_le hs ℓ u)

/-- One term of the prime tail on the line `Re p = s` is a unimodular multiple of the Fourier
transform of the truncated profile. -/
theorem norm_stateTail_factor_eq (F : ℝ → ℝ) (s ℓ t : ℝ) :
    ‖cexp (((s : ℂ) + (t : ℂ) * I) * (ℓ : ℂ)) *
        ∫ u in Iio (-ℓ), (F u : ℂ) * cexp (((s : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ =
      ‖paperFT (cx (tailProfile F s ℓ)) (t : ℂ)‖ := by
  have h : cexp (((s : ℂ) + (t : ℂ) * I) * (ℓ : ℂ)) *
        ∫ u in Iio (-ℓ), (F u : ℂ) * cexp (((s : ℂ) + (t : ℂ) * I) * (u : ℂ)) =
      cexp (((t * ℓ : ℝ) : ℂ) * I) * paperFT (cx (tailProfile F s ℓ)) (t : ℂ) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_const_mul]
    show _ = cexp (((t * ℓ : ℝ) : ℂ) * I) *
      ∫ u : ℝ, cx (tailProfile F s ℓ) u * cexp (I * (t : ℂ) * (u : ℂ))
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show cexp (((s : ℂ) + (t : ℂ) * I) * (ℓ : ℂ)) * (Iio (-ℓ)).indicator
        (fun u : ℝ => (F u : ℂ) * cexp (((s : ℂ) + (t : ℂ) * I) * (u : ℂ))) u =
      cexp (((t * ℓ : ℝ) : ℂ) * I) *
        (((tailProfile F s ℓ u : ℝ) : ℂ) * cexp (I * (t : ℂ) * (u : ℂ)))
    unfold tailProfile
    by_cases hu : u < -ℓ
    · have e : cexp (((s : ℂ) + (t : ℂ) * I) * (ℓ : ℂ)) *
          cexp (((s : ℂ) + (t : ℂ) * I) * (u : ℂ)) =
          cexp (((t * ℓ : ℝ) : ℂ) * I) *
            (cexp ((s * (u + ℓ) : ℝ) : ℂ) * cexp (I * (t : ℂ) * (u : ℂ))) := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [Set.indicator_apply, if_pos (show u ∈ Iio (-ℓ) from hu), if_pos hu,
        Complex.ofReal_mul, Complex.ofReal_exp]
      linear_combination (F u : ℂ) * e
    · rw [Set.indicator_apply, if_neg (show u ∉ Iio (-ℓ) from hu), if_neg hu]
      simp
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Plancherel for the truncated profile: its transform has mass at most `2π e^{-8ℓ} W₈`. -/
theorem lintegral_norm_sq_paperFT_tailProfile_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {s : ℝ} (hs : 0 ≤ s) (ℓ : ℝ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (‖paperFT (cx (tailProfile F s ℓ)) (t : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi *
        (Real.exp (-(8 * ℓ)) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hi := integrable_tailProfile hF hs ℓ
  have h2 := integrable_sq_tailProfile hF hs ℓ
  have hP := integrable_norm_sq_paperFT_cx hi h2
  rw [← ofReal_integral_eq_lintegral_ofReal hP (Eventually.of_forall fun t => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpl : (∫ t : ℝ, ‖paperFT (cx (tailProfile F s ℓ)) (t : ℂ)‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, tailProfile F s ℓ u ^ 2 := by
    have h := KernelStrip.integral_norm_sq_paperFT_of_memLp (hi.ofReal (𝕜 := ℂ))
      (memLp_cx_of_sq hi h2)
    have h' : (∫ r : ℝ, ‖paperFT (cx (tailProfile F s ℓ)) r‖ ^ 2) =
        2 * Real.pi * ∫ u : ℝ, ‖((tailProfile F s ℓ u : ℝ) : ℂ)‖ ^ 2 := h
    rw [h']
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun u => by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  rw [hpl]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_const_mul]
  exact integral_mono h2 (hF.exponential.const_mul _) fun u => sq_tailProfile_le hs ℓ u

theorem summable_vonMangoldtAtom_mul_exp_neg_one_log :
    Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) :=
  summable_vonMangoldt_div_threeHalves.congr fun n => by
    rw [vonMangoldtAtom_mul_exp_eq]
    norm_num

theorem mul_eq_rpow_half_mul_rpow_half {v q E₁ E₂ : ℝ} (hv : 0 ≤ v) (hq : 0 ≤ q)
    (h1 : 0 ≤ E₁) (hE : E₁ * E₂ = 1) :
    v * q = (v * E₁) ^ (1 - 1 / 2 : ℝ) * (v * E₂ * q ^ 2) ^ (1 / 2 : ℝ) := by
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (mul_nonneg hv h1),
    show v * E₁ * (v * E₂ * q ^ 2) = (v * q) ^ 2 by linear_combination (v ^ 2 * q ^ 2) * hE,
    Real.sqrt_sq (mul_nonneg hv hq)]

theorem ennreal_sq_half_mul_half (x y : ENNReal) :
    (x ^ (1 - 1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) ^ 2 = x * y := by
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The prime tail is square integrable on every line `Re p = s ≥ 0`.** Cauchy–Schwarz over
the prime powers with the weights `Λ(n) n^{-3/2}`, then Plancherel for each truncated profile,
whose mass beyond `-log n` is at most `n^{-8} ∫ F² e^{-8u}`. -/
theorem integrable_norm_sq_stateTail_line {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun t : ℝ => ‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hcont : Continuous fun t : ℝ => stateTail F ((s : ℂ) + (t : ℂ) * I) :=
    (differentiableOn_stateTail_strip hF).continuousOn.comp_continuous (by fun_prop) fun t => by
      have hre : ((s : ℂ) + (t : ℂ) * I).re = s := by simp
      show -4 < ((s : ℂ) + (t : ℂ) * I).re
      rw [hre]
      linarith
  refine ⟨(hcont.norm.pow 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => sq_nonneg _)).mpr ?_⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hsum := summable_vonMangoldtAtom_mul_exp_neg_one_log
  have hv0 : ∀ n : ℕ, 0 ≤ vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) := fun n =>
    mul_nonneg (vonMangoldtAtom_nonneg n) (Real.exp_pos _).le
  have hA0 : (∑' n : ℕ, ENNReal.ofReal
      (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hv0 hsum]
    exact ENNReal.ofReal_lt_top
  -- pointwise Cauchy–Schwarz over the prime powers
  have hpt : ∀ t : ℝ, ENNReal.ofReal (‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (∑' n : ℕ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) *
        ∑' n : ℕ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
          ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) := by
    intro t
    have hS : ‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ₑ ≤
        ∑' n : ℕ, ENNReal.ofReal
            (vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) ^ (1 - 1 / 2 : ℝ) *
          ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
            ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) ^ (1 / 2 : ℝ) := by
      unfold stateTail
      refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun n => ?_))
      have hE : Real.exp (-(1 * Real.log n)) * Real.exp (1 * Real.log n) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [← ofReal_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (vonMangoldtAtom_nonneg n), norm_stateTail_factor_eq,
        ENNReal.ofReal_rpow_of_nonneg (hv0 n) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n)
          (Real.exp_pos _).le) (sq_nonneg _)) (by norm_num),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hv0 n) _)]
      congr 1
      exact mul_eq_rpow_half_mul_rpow_half (vonMangoldtAtom_nonneg n) (norm_nonneg _)
        (Real.exp_pos _).le hE
    have hCS := lintegral_rpow_mul_rpow_le (Measure.count : Measure ℕ)
      (a₀ := fun n : ℕ => ENNReal.ofReal (vonMangoldtAtom n * Real.exp (-(1 * Real.log n))))
      (a₁ := fun n : ℕ => ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
        ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2))
      measurable_from_nat.aemeasurable measurable_from_nat.aemeasurable (τ := 1 / 2)
      (by norm_num) (by norm_num)
    rw [lintegral_count, lintegral_count, lintegral_count] at hCS
    have h2 := pow_le_pow_left' (hS.trans hCS) 2
    rw [ennreal_sq_half_mul_half] at h2
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    exact h2
  -- Plancherel for each truncated profile
  have hn : ∀ n : ℕ, (∫⁻ t : ℝ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
      ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi * W *
        (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) := by
    intro n
    have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hc : 0 ≤ vonMangoldtAtom n * Real.exp (1 * Real.log n) :=
      mul_nonneg (vonMangoldtAtom_nonneg n) (Real.exp_pos _).le
    calc (∫⁻ t : ℝ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
          ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2))
        = ∫⁻ t : ℝ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n)) *
            ENNReal.ofReal (‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) :=
          lintegral_congr fun t => ENNReal.ofReal_mul hc
      _ = ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n)) *
            ∫⁻ t : ℝ, ENNReal.ofReal
              (‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n)) *
            ENNReal.ofReal (2 * Real.pi * (Real.exp (-(8 * Real.log n)) * W)) := by
          rw [hW]
          exact mul_le_mul' le_rfl (lintegral_norm_sq_paperFT_tailProfile_le hF hs _)
      _ = ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
            (2 * Real.pi * (Real.exp (-(8 * Real.log n)) * W))) := (ENNReal.ofReal_mul hc).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi * W *
            (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have he : Real.exp (1 * Real.log n) * Real.exp (-(8 * Real.log n)) ≤
              Real.exp (-(1 * Real.log n)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith)
          have h0 : 0 ≤ 2 * Real.pi * W * vonMangoldtAtom n :=
            mul_nonneg (mul_nonneg (by positivity) hW0) (vonMangoldtAtom_nonneg n)
          calc vonMangoldtAtom n * Real.exp (1 * Real.log n) *
                (2 * Real.pi * (Real.exp (-(8 * Real.log n)) * W))
              = 2 * Real.pi * W * vonMangoldtAtom n *
                  (Real.exp (1 * Real.log n) * Real.exp (-(8 * Real.log n))) := by ring
            _ ≤ 2 * Real.pi * W * vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) :=
                mul_le_mul_of_nonneg_left he h0
            _ = _ := by ring
  have hmeas : ∀ n : ℕ, AEMeasurable (fun t : ℝ => ENNReal.ofReal
      (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
        ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2)) volume := fun n =>
    (continuous_const.mul ((continuous_paperFT_cx
      (integrable_tailProfile hF hs _)).norm.pow 2)).measurable.ennreal_ofReal.aemeasurable
  calc (∫⁻ t : ℝ, ENNReal.ofReal (‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ ^ 2))
      ≤ ∫⁻ t : ℝ, (∑' n : ℕ, ENNReal.ofReal
            (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) *
          ∑' n : ℕ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
            ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) :=
        lintegral_mono fun t => hpt t
    _ = (∑' n : ℕ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) *
          ∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (1 * Real.log n) *
            ‖paperFT (cx (tailProfile F s (Real.log n))) (t : ℂ)‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ hA0.ne, lintegral_tsum hmeas]
    _ ≤ (∑' n : ℕ, ENNReal.ofReal (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) *
          ∑' n : ℕ, ENNReal.ofReal (2 * Real.pi * W *
            (vonMangoldtAtom n * Real.exp (-(1 * Real.log n)))) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hn)
    _ < ⊤ := by
        refine ENNReal.mul_lt_top hA0 ?_
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun n => mul_nonneg (mul_nonneg (by positivity) hW0) (hv0 n)) (hsum.mul_left _)]
        exact ENNReal.ofReal_lt_top

/-! ### The squared logarithmic energy -/

theorem norm_sq_div_add_half_le (c : ℂ) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    ‖c / ((s : ℂ) + (t : ℂ) * I + 1 / 2)‖ ^ 2 ≤ 4 * ‖c‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
  have hre : ((s : ℂ) + (t : ℂ) * I + 1 / 2).re = s + 1 / 2 := by simp
  have him : ((s : ℂ) + (t : ℂ) * I + 1 / 2).im = t := by simp
  have hn : ‖(s : ℂ) + (t : ℂ) * I + 1 / 2‖ ^ 2 = (s + 1 / 2) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hq : (1 + t ^ 2) / 4 ≤ (s + 1 / 2) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t, sq_nonneg s]
  have hpos : 0 < (s + 1 / 2) ^ 2 + t ^ 2 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (1 + t ^ 2) / 4) hq
  have h1 : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  rw [norm_div, div_pow, hn, div_le_iff₀ hpos]
  calc ‖c‖ ^ 2 = 4 * ‖c‖ ^ 2 * (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) / 4) := by
        field_simp
    _ ≤ 4 * ‖c‖ ^ 2 * (1 + t ^ 2)⁻¹ * ((s + 1 / 2) ^ 2 + t ^ 2) :=
        mul_le_mul_of_nonneg_left hq (by positivity)

/-- The absorption inequality: a multiplier of size at least `L/2 - K` and a right side of four
terms give `L² x² ≤ 32 Σ yᵢ² + 8 K² x²`. -/
theorem sq_mul_le_of_half_sub_le {L K x A y₁ y₂ y₃ y₄ : ℝ} (hL : 0 ≤ L) (hx : 0 ≤ x)
    (hA : L / 2 - K ≤ A) (hR : x * A ≤ y₁ + y₂ + y₃ + y₄) :
    L ^ 2 * x ^ 2 ≤ 32 * (y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2) + 8 * K ^ 2 * x ^ 2 := by
  have h0 := mul_le_mul_of_nonneg_left hA hx
  have h1 : L * x ≤ 2 * (y₁ + y₂ + y₃ + y₄) + 2 * K * x := by nlinarith
  have h2 : (L * x) ^ 2 ≤ (2 * (y₁ + y₂ + y₃ + y₄) + 2 * K * x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hL hx) h1 2
  nlinarith [sq_nonneg (2 * (y₁ + y₂ + y₃ + y₄) - 2 * K * x), sq_nonneg (y₁ - y₂),
    sq_nonneg (y₁ - y₃), sq_nonneg (y₁ - y₄), sq_nonneg (y₂ - y₃), sq_nonneg (y₂ - y₄),
    sq_nonneg (y₃ - y₄)]

/-- **The multiplier of the state is at least half a logarithm.** On a line `Re p = s`,
`κ < s < 1/2`, the Gamma symbol contributes `log(|t| + 4) - C` and the regular part of `ζ'/ζ`
is sublogarithmic. -/
theorem exists_half_log_sub_le_norm_stripMultiplier {κ s : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hs : s < 1 / 2) :
    ∃ K : ℝ, ∀ t : ℝ,
      Real.log (|t| + 4) / 2 - K ≤ ‖stripMultiplier ((s : ℂ) + (t : ℂ) * I)‖ := by
  have hs0 : 0 ≤ s := hκ.trans hκs.le
  obtain ⟨C, hC, hN⟩ := exists_norm_zetaRegularLogDeriv_le_rpow hκ hzero
    (a := 1 / 2 + (κ + s) / 2) (b := 2) (s₀ := 1 / 2 + s) (by linarith) (by linarith)
    (by linarith) (by norm_num)
  have hθ : (2 - (1 / 2 + s)) / (2 - (1 / 2 + (κ + s) / 2)) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨K₁, hK₁⟩ := exists_mul_rpow_le_half_add hC hθ
  refine ⟨10 + 2 * Real.log 4 + |(levySymbol (s : ℂ)).re| + K₁ + (1 / 2 - s)⁻¹, fun t => ?_⟩
  have h1 := log_sub_le_re_symbol hs0 hs t
  have hL := one_le_log_abs_add_four t
  have h2 : ‖zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))‖ ≤
      Real.log (|t| + 4) / 2 + K₁ := by
    have h := hN t
    rw [show ((1 / 2 + s : ℝ) : ℂ) + (t : ℂ) * I = 1 / 2 + ((s : ℂ) + (t : ℂ) * I) by
      push_cast
      ring] at h
    exact h.trans (hK₁ _ hL)
  have h3 : ‖((s : ℂ) + (t : ℂ) * I - 1 / 2)⁻¹‖ ≤ (1 / 2 - s)⁻¹ := by
    rw [norm_inv]
    refine inv_anti₀ (by linarith) ?_
    have h := Complex.abs_re_le_norm ((s : ℂ) + (t : ℂ) * I - 1 / 2)
    have hre : ((s : ℂ) + (t : ℂ) * I - 1 / 2).re = s - 1 / 2 := by simp
    rw [hre, abs_of_neg (by linarith)] at h
    linarith
  have h5 : (stripMultiplier ((s : ℂ) + (t : ℂ) * I)).re =
      (2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol ((s : ℂ) + (t : ℂ) * I)).re +
        (zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))).re -
        (((s : ℂ) + (t : ℂ) * I - 1 / 2)⁻¹).re := by
    unfold stripMultiplier
    rw [Complex.sub_re, Complex.add_re]
  have h6 := (le_abs_self _).trans
    (Complex.abs_re_le_norm (stripMultiplier ((s : ℂ) + (t : ℂ) * I)))
  have h7 := (abs_le.mp (Complex.abs_re_le_norm
    (zetaRegularLogDeriv (1 / 2 + ((s : ℂ) + (t : ℂ) * I))))).1
  have h8 := (abs_le.mp (Complex.abs_re_le_norm (((s : ℂ) + (t : ℂ) * I - 1 / 2)⁻¹))).2
  have h9 := neg_abs_le (levySymbol (s : ℂ)).re
  linarith

/-- **The state has a squared logarithmic energy on the lines of its decay.** If every centred
zero has `Re z ≤ κ`, `κ < s < 1/2` and `∫ F² e^{-bu} < ∞` for some `b > 16 - 2s`, then
`∫ log(|t| + 4)² |L F(s + it)|² dt < ∞`. -/
theorem integrable_log_sq_mul_norm_sq_laplace_line {κ s : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκs : κ < s) (hs : s < 1 / 2)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hbs : 16 - 2 * s < b) :
    Integrable fun t : ℝ => Real.log (|t| + 4) ^ 2 *
      ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hs0 : 0 ≤ s := hκ.trans hκs.le
  have hG := criticalHalfLineEnergyDomain_exp_min_mul hd (σ := 2) (by norm_num)
  have ha := criticalAliasCoefficient_positive hW
  -- the transform and the terms of the right side on the line
  have I0 := integrable_norm_sq_laplace_line_of_decay hd.meas hd.support hb (σ := s)
    (by linarith)
  have I8 := integrable_norm_sq_laplace_line_of_decay hd.meas hd.support hb (σ := s - 8)
    (by linarith)
  have IJ := integrable_norm_sq_levyHeadTerm_line hG (σ := s - 2) (by linarith)
  have IT := integrable_norm_sq_stateTail_line hd hs0
  have IR : Integrable fun t : ℝ => (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq
  obtain ⟨K, hA⟩ := exists_half_log_sub_le_norm_stripMultiplier hκ hzero hκs hs
  have hD : Integrable fun t : ℝ =>
      32 * (criticalAliasCoefficient W₀ ^ 2 *
          ‖negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 +
        ‖levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u)
          (((s - 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 +
        ‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 +
        4 * ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖ ^ 2 * (1 + t ^ 2)⁻¹) +
      8 * K ^ 2 * ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    (((((I8.const_mul (criticalAliasCoefficient W₀ ^ 2)).add IJ).add IT).add
      (IR.const_mul (4 * ‖negativeHalfLineLaplace (cx F) (-(1 / 2))‖ ^ 2))).const_mul 32).add
      (I0.const_mul (8 * K ^ 2))
  refine hD.mono' (((Real.measurable_log.comp
    (continuous_abs.measurable.add_const 4)).pow_const 2).aestronglyMeasurable.mul
      I0.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hre : ((s : ℂ) + (t : ℂ) * I).re = s := by simp
  have heq := laplace_mul_stripMultiplier_eq hκ hzero hW hthreshold hF hb
    (p := (s : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hκs) (by rw [hre]; exact hs)
    (by rw [hre]; linarith)
  rw [show (s : ℂ) + (t : ℂ) * I - 8 = ((s - 8 : ℝ) : ℂ) + (t : ℂ) * I by
      push_cast
      ring,
    show (s : ℂ) + (t : ℂ) * I - 2 = ((s - 2 : ℝ) : ℂ) + (t : ℂ) * I by
      push_cast
      ring] at heq
  have hR : ‖negativeHalfLineLaplace (cx F) ((s : ℂ) + (t : ℂ) * I)‖ *
      ‖stripMultiplier ((s : ℂ) + (t : ℂ) * I)‖ ≤
      criticalAliasCoefficient W₀ *
          ‖negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        ‖levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u)
          (((s - 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        ‖stateTail F ((s : ℂ) + (t : ℂ) * I)‖ +
        ‖negativeHalfLineLaplace (cx F) (-(1 / 2)) / ((s : ℂ) + (t : ℂ) * I + 1 / 2)‖ := by
    rw [← norm_mul, heq]
    have n1 := norm_sub_le
      (-((criticalAliasCoefficient W₀ : ℂ) *
          negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)) -
        levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u)
          (((s - 2 : ℝ) : ℂ) + (t : ℂ) * I) + stateTail F ((s : ℂ) + (t : ℂ) * I))
      (negativeHalfLineLaplace (cx F) (-(1 / 2)) / ((s : ℂ) + (t : ℂ) * I + 1 / 2))
    have n2 := norm_add_le
      (-((criticalAliasCoefficient W₀ : ℂ) *
          negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)) -
        levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u)
          (((s - 2 : ℝ) : ℂ) + (t : ℂ) * I))
      (stateTail F ((s : ℂ) + (t : ℂ) * I))
    have n3 := norm_sub_le
      (-((criticalAliasCoefficient W₀ : ℂ) *
          negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)))
      (levyHeadTerm (fun u => Real.exp (2 * min u 0) * F u)
          (((s - 2 : ℝ) : ℂ) + (t : ℂ) * I))
    have n4 : ‖-((criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I))‖ =
        criticalAliasCoefficient W₀ *
          ‖negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    linarith
  have h := sq_mul_le_of_half_sub_le (by linarith [one_le_log_abs_add_four t]) (norm_nonneg _)
    (hA t) hR
  have h4 := norm_sq_div_add_half_le (negativeHalfLineLaplace (cx F) (-(1 / 2))) hs0 t
  have e : (criticalAliasCoefficient W₀ *
      ‖negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)‖) ^ 2 =
      criticalAliasCoefficient W₀ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) (((s - 8 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by ring
  rw [e] at h
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
