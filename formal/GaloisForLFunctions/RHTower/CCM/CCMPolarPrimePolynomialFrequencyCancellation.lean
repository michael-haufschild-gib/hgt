import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinPolynomialCancellation
import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation


/-!
# Uniform polynomial-frequency prime-polar cancellation

The exact completed-error Stieltjes identity retains the aperture endpoint.
The actual PNT source and its absolute primitive then control all frequencies
in every fixed polynomial band, uniformly as the aperture grows.
-/

open MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower

private theorem stieltjesPairing_sub_const (a : ℝ) {F : ℝ → ℂ}
    (hF : Continuous F) (C : ℂ) :
    criticalMellinStieltjesPairing a (fun h => F h - C) =
      criticalMellinStieltjesPairing a F - C * criticalMellinStieltjesPairing a (fun _ => 1) := by
  have h1 : IntegrableOn (fun h : ℝ => F h * (2 * Real.cosh (h / 2) : ℂ))
      (Ioc 0 (2 * a)) volume :=
    (hF.mul (by fun_prop)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun h : ℝ => C * (2 * Real.cosh (h / 2) : ℂ))
      (Ioc 0 (2 * a)) volume :=
    (by fun_prop : Continuous (fun h : ℝ => C * (2 * Real.cosh (h / 2) : ℂ))).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  unfold criticalMellinStieltjesPairing
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  rw [integral_sub h1 h2, integral_const_mul, Finset.sum_sub_distrib]
  have hs : (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      (criticalMellinAtomWeight k : ℂ) * C) =
      C * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (criticalMellinAtomWeight k : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hs]
  ring

/-- The literal Fourier test retains the terminal completed error in the
Stieltjes estimate. Prime powers and the aperture endpoint are unchanged. -/
theorem norm_criticalMellinStieltjesPairing_cexp_le_completedError
    {a : ℝ} (ha : 0 ≤ a) (ξ : ℝ) :
    ‖criticalMellinStieltjesPairing a
      (fun h => Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I))‖ ≤
      |criticalMellinCompletedError (2 * a)| +
        |ξ| * ∫ h in (0 : ℝ)..2 * a, |criticalMellinCompletedError h| := by
  let F : ℝ → ℂ := fun h => Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I)
  let F' : ℝ → ℂ := fun h => F h * ((ξ : ℂ) * Complex.I)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hF' : Continuous F' := by dsimp [F']; exact hF.mul continuous_const
  have hd : ∀ h : ℝ, HasDerivAt F (F' h) h := by
    intro h
    simpa only [F, F', id_eq, mul_one] using
      (((hasDerivAt_id h).const_mul ξ).ofReal_comp.mul_const Complex.I).cexp
  have hh : 0 ≤ 2 * a := by positivity
  have hparts := criticalMellinStieltjesPairing_integrationByParts ha
    (F := fun h => F h - F (2 * a)) (F' := F')
    (fun h _ => (hd h).sub_const (F (2 * a))) (hF'.intervalIntegrable _ _) (by simp)
  rw [stieltjesPairing_sub_const a hF, criticalMellinStieltjesPairing_one ha,
    ← intervalIntegral.integral_of_le hh] at hparts
  have heq : criticalMellinStieltjesPairing a F =
      F (2 * a) * (criticalMellinCompletedError (2 * a) : ℂ) -
        ∫ h in (0 : ℝ)..2 * a, (criticalMellinCompletedError h : ℂ) * F' h := by
    linear_combination hparts
  have hFn : ∀ h, ‖F h‖ = 1 := fun h => Complex.norm_exp_ofReal_mul_I (ξ * h)
  have hF'n : ∀ h, ‖F' h‖ = |ξ| := by
    intro h
    dsimp [F']
    rw [norm_mul, hFn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, one_mul]
  have hdi :=
    (GaloisForLFunctions.RHTower.intervalIntegrable_criticalMellinCompletedError_on_Icc hh).abs
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun h => (criticalMellinCompletedError h : ℂ) * F' h)
    (g := fun h => |ξ| * |criticalMellinCompletedError h|) hh
    (Eventually.of_forall fun h _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hF'n]
      exact le_of_eq (mul_comm _ _))
    (hdi.const_mul |ξ|)
  rw [intervalIntegral.integral_const_mul] at hi
  change ‖criticalMellinStieltjesPairing a F‖ ≤ _
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hFn, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact add_le_add le_rfl hi

/-- Uniform prime-polar cancellation on every fixed polynomial frequency
band, proved from the actual PNT source and its completed Stieltjes error. -/
theorem eventually_norm_criticalMellinStieltjesPairing_cexp_le_polynomialFrequency
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ξ : ℝ, |ξ| ≤ (2 * a) ^ m →
      ‖criticalMellinStieltjesPairing a
        (fun h => Complex.exp (((ξ * h : ℝ) : ℂ) * Complex.I))‖ ≤ ε * Real.exp a := by
  have hscale : Tendsto (fun a : ℝ => 2 * a) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hlim : Tendsto (fun a : ℝ => Real.exp (-a) *
      (|criticalMellinCompletedError (2 * a)| +
        (2 * a) ^ m * ∫ h in (0 : ℝ)..2 * a, |criticalMellinCompletedError h|))
      atTop (𝓝 0) := by
    have hl := ((tendsto_pow_mul_exp_neg_half_mul_abs_criticalMellinCompletedError 0).add
      (tendsto_pow_mul_exp_neg_half_mul_completedError_absolutePrimitive m)).comp hscale
    simp only [zero_add] at hl
    convert hl using 1
    ext a
    simp only [Function.comp_apply, pow_zero, one_mul,
      show -(2 * a) / 2 = -a by ring]
    ring
  filter_upwards [hlim.eventually_le_const hε, eventually_ge_atTop (0 : ℝ)] with a hs ha
  intro ξ hξ
  have hint0 : 0 ≤ ∫ h in (0 : ℝ)..2 * a, |criticalMellinCompletedError h| :=
    intervalIntegral.integral_nonneg (by positivity) (fun _ _ => abs_nonneg _)
  have hb := (norm_criticalMellinStieltjesPairing_cexp_le_completedError ha ξ).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hξ hint0))
  have hn := (mul_le_mul_of_nonneg_left hb (Real.exp_pos (-a)).le).trans hs
  have hm := mul_le_mul_of_nonneg_left hn (Real.exp_pos a).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hm
  simpa only [mul_comm ε] using hm

/-- The actual finite-aperture prime-polar multiplier is uniformly small
on every polynomial frequency band. -/
theorem eventually_abs_polarPrimeStieltjesSymbol_le_polynomialFrequency
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ξ : ℝ, |ξ| ≤ (2 * a) ^ m →
      |polarPrimeStieltjesSymbol a ξ| ≤ ε * Real.exp a := by
  filter_upwards [eventually_norm_criticalMellinStieltjesPairing_cexp_le_polynomialFrequency
    m (ε / 2) (by positivity), eventually_ge_atTop (0 : ℝ)] with a hb ha
  intro ξ hξ
  rw [← criticalMellinStieltjesPairing_cexp_re ha, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := (Complex.abs_re_le_norm _).trans (hb ξ hξ)
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  convert hm using 1 <;> first | rfl | ring

end RHTower
end
