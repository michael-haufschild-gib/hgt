import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# Gamma and polar normalization of the Suzuki critical tangent

The digamma recurrence transports the primary Gamma mass from `5/4` to `1/4`.
The resulting decaying exponential and the causal growing pole combine into
the complete hyperbolic polar term of the Weil quadratic form.
-/

open MeasureTheory Set Filter Topology Zeta23
open GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

private theorem digamma_five_quarters :
    (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re =
      (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re + 4 := by
  have hp : ∀ n : ℕ, ((1 / 4 : ℝ) : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := congrArg Complex.re (Complex.digamma_apply_add_one ((1 / 4 : ℝ) : ℂ) hp)
  norm_num at h ⊢
  exact h

private theorem primary_tangent_eq_levy_sub {t : ℝ} (ht : 0 < t) :
    2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) =
      archLevySinhWeight t - 2 * Real.exp (-t / 2) := by
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht, archLevyDensity]
  have he : Real.exp (-(5 / 2 : ℝ) * t) = Real.exp (-t / 2) * Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd : 1 - Real.exp (-2 * t) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  rw [he]
  apply (div_eq_iff hd).mpr
  rw [sub_mul, mul_assoc 2 (Real.exp (-t / 2) / (1 - Real.exp (-2 * t))),
    div_mul_cancel₀ _ hd]
  ring

private theorem integrable_decay :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2)) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) (0 : ℝ)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  change Real.exp ((-1 / 2) * t) = Real.exp (-t / 2)
  congr 1
  ring

private theorem integral_decay :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t / 2)) = 2 := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp ((-1 / 2) * t) := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    _ = 2 := by
      simpa using integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) (0 : ℝ)

private theorem correlation_exp_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (a : ℝ) :
    IntegrableOn (fun t => Real.exp (a * t) * autocorr f t) (Ioi 0) := by
  exact (((show Continuous (fun t : ℝ => Real.exp (a * t)) by fun_prop).mul
    (continuous_autocorr hf hfc)).integrable_of_hasCompactSupport
      (hasCompactSupport_autocorr hfc).mul_left).integrableOn

/-- The raw primary and growing-pole tangent equals the complete archimedean Weil form. -/
theorem suzukiCriticalWeil_normalization {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    -(((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
      ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) -
      2 * ∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t) =
    EF.gammaBracket 0 * autocorr f 0 + biScaleLevyEnergy f +
      4 * ∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2) := by
  have hm : IntegrableOn (fun t => Real.exp (-t / 2) * autocorr f t) (Ioi 0) := by
    apply (correlation_exp_integrable hf hfc (-(1 / 2))).congr_fun _ measurableSet_Ioi
    intro t _
    change Real.exp (-(1 / 2) * t) * autocorr f t = Real.exp (-t / 2) * autocorr f t
    congr 2
    ring
  have hp : IntegrableOn (fun t => Real.exp (t / 2) * autocorr f t) (Ioi 0) := by
    apply (correlation_exp_integrable hf hfc (1 / 2)).congr_fun _ measurableSet_Ioi
    intro t _
    change Real.exp ((1 / 2) * t) * autocorr f t = Real.exp (t / 2) * autocorr f t
    congr 2
    ring
  have hD : IntegrableOn (fun t => (autocorr f 0 - autocorr f t) *
      (2 * Real.exp (-t / 2))) (Ioi 0) := by
    apply ((integrable_decay.const_mul (2 * autocorr f 0)).sub (hm.const_mul 2)).congr
    filter_upwards with t
    change 2 * autocorr f 0 * Real.exp (-t / 2) -
      2 * (Real.exp (-t / 2) * autocorr f t) = _
    ring
  have hJ := integrableOn_biScaleLevyIntegrand hf hfc
  have hK : (∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
      (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) =
      biScaleLevyEnergy f - (4 * autocorr f 0 -
        2 * ∫ t in Ioi 0, Real.exp (-t / 2) * autocorr f t) := by
    calc
      _ = ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) * archLevySinhWeight t -
          (autocorr f 0 - autocorr f t) * (2 * Real.exp (-t / 2)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [primary_tangent_eq_levy_sub ht]
        ring
      _ = biScaleLevyEnergy f - ∫ t in Ioi 0,
          (autocorr f 0 - autocorr f t) * (2 * Real.exp (-t / 2)) :=
        integral_sub hJ hD
      _ = _ := by
        congr 1
        have he : (fun t : ℝ => (autocorr f 0 - autocorr f t) * (2 * Real.exp (-t / 2))) =
            fun t => (2 * autocorr f 0) * Real.exp (-t / 2) -
              2 * (Real.exp (-t / 2) * autocorr f t) := by funext t; ring
        rw [he, integral_sub (integrable_decay.const_mul _) (hm.const_mul _),
          integral_const_mul, integral_const_mul, integral_decay]
        ring
  have hpolar : 4 * (∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2)) =
      2 * (∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t) +
      2 * (∫ t in Ioi 0, Real.exp (-t / 2) * autocorr f t) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hp.const_mul 2) (hm.const_mul 2)]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.cosh_eq, neg_div]
    ring
  have hg := gammaBracket_eq_re_digamma 0
  simp only [zero_div, Complex.ofReal_zero, zero_mul, add_zero] at hg
  rw [hK, hpolar, digamma_five_quarters, hg]
  ring

end
end RHTower

#print axioms RHTower.suzukiCriticalWeil_normalization
