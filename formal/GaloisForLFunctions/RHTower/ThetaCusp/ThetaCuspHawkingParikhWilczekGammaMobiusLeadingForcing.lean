import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusCurrent
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Leading-prime arithmetic forcing and exact Gamma connection defects

The complete Gamma/Möbius-log forcing has first-prime limit
`E(x)/Q(2*x) -> log(2)` and is eventually strictly positive in real part.
One fixed summable majorant controls the entire normalized series.

Relative to the original source its quotient tends to zero. Its differences
from the inverse and positive Gamma connection forcings, divided by
`exp(t)*q(t)`, tend respectively to `1/2` and `3/2` for every complex shift.
Thus neither raw differential forcing equals the arithmetic current. Inverse
gain transports the source-relative quotient exactly to the opposite end.
No small-ray bound on the unreflected current, Xi occurrence, or Ward balance
is assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace RHTower
open ArithmeticFunction Filter
noncomputable section


theorem pwGammaRaySource_ratio_scale {n x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    pwGammaRaySource (n * x) / pwGammaRaySource (2 * x) =
      pwGammaRaySource n / pwGammaRaySource 2 *
        (Real.exp (-(n - 2) * (x - 1)) : ℂ) := by
  unfold pwGammaRaySource GaloisForLFunctions.expShift
  simp only [Nat.cast_zero, add_zero, Real.exp_log (mul_pos hn hx),
    Real.exp_log (mul_pos two_pos hx), Real.exp_log hn, Real.exp_log two_pos]
  rw [Real.log_mul hn.ne' hx.ne', Real.log_mul two_ne_zero hx.ne']
  rw [← Complex.ofReal_div, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_add]
  congr 2
  ring

private def pwGammaForcingLeadingCoeff (n : ℕ) : ℂ :=
  ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
    pwGammaRaySource (n : ℝ) / pwGammaRaySource 2

private def pwGammaForcingNormalizedTerm (x : ℝ) (n : ℕ) : ℂ :=
  pwGammaForcingLeadingCoeff n * (Real.exp (-((n : ℝ) - 2) * (x - 1)) : ℂ)

private theorem pwGammaForcingLeadingCoeff_two :
    pwGammaForcingLeadingCoeff 2 = (Real.log 2 : ℂ) := by
  simp [pwGammaForcingLeadingCoeff, moebius_apply_prime Nat.prime_two,
    pwGammaRaySource_ne_zero]

private theorem pwGammaForcingLeadingCoeff_summable :
    Summable pwGammaForcingLeadingCoeff := by
  change Summable (fun n : ℕ =>
    ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
      pwGammaRaySource (n : ℝ) / pwGammaRaySource 2)
  simpa only [mul_one] using
    (pwGammaMobiusLogCurrent_summable (x := 1) zero_lt_one).div_const (pwGammaRaySource 2)

private theorem pwGammaForcingNormalizedTerm_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    pwGammaForcingNormalizedTerm x n =
      (((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((n : ℝ) * x)) / pwGammaRaySource (2 * x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaForcingNormalizedTerm, pwGammaForcingLeadingCoeff]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [mul_div_assoc, pwGammaRaySource_ratio_scale hnr hx]
    unfold pwGammaForcingNormalizedTerm pwGammaForcingLeadingCoeff
    ring

private theorem pwGammaForcingNormalizedTerm_bound {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    ‖pwGammaForcingNormalizedTerm x n‖ ≤ ‖pwGammaForcingLeadingCoeff n‖ := by
  rcases lt_or_ge n 2 with hn | hn
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;>
      simp [pwGammaForcingNormalizedTerm, pwGammaForcingLeadingCoeff]
  · have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [pwGammaForcingNormalizedTerm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have he : Real.exp (-((n : ℝ) - 2) * (x - 1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_one _)

private theorem pwGammaForcingNormalizedTerm_tendsto (n : ℕ) :
    Tendsto (fun x : ℝ => pwGammaForcingNormalizedTerm x n) atTop
      (nhds (if n = 2 then (Real.log 2 : ℂ) else 0)) := by
  by_cases hn2 : n = 2
  · subst n
    simp [pwGammaForcingNormalizedTerm, pwGammaForcingLeadingCoeff_two]
  · rw [if_neg hn2]
    rcases lt_or_ge n 2 with hn | hn
    · have hcases : n = 0 ∨ n = 1 := by omega
      rcases hcases with rfl | rfl <;>
        simp [pwGammaForcingNormalizedTerm, pwGammaForcingLeadingCoeff]
    · have hnr : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_le_of_ne hn (Ne.symm hn2))
      have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
        simpa only [sub_eq_add_neg, id_eq] using
          (tendsto_id.atTop_add (tendsto_const_nhds (x := (-1 : ℝ))))
      have he := Real.tendsto_exp_atBot.comp (hshift.const_mul_atTop_of_neg (by linarith :
        -((n : ℝ) - 2) < 0))
      simpa only [pwGammaForcingNormalizedTerm, Complex.ofReal_zero, mul_zero,
        Function.comp_apply] using
        he.ofReal.const_mul (pwGammaForcingLeadingCoeff n)

/-- The full Möbius-log forcing has the precise first-prime asymptotic. -/
theorem pwGammaMobiusLogCurrent_leading_prime :
    Tendsto (fun x : ℝ => pwGammaMobiusLogCurrent x / pwGammaRaySource (2 * x))
      atTop (nhds (Real.log 2 : ℂ)) := by
  have hsumlimit := tendsto_tsum_of_dominated_convergence
    pwGammaForcingLeadingCoeff_summable.norm pwGammaForcingNormalizedTerm_tendsto
    (show ∀ᶠ x : ℝ in atTop, ∀ n, ‖pwGammaForcingNormalizedTerm x n‖ ≤
      ‖pwGammaForcingLeadingCoeff n‖ from by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx n
        exact pwGammaForcingNormalizedTerm_bound hx n)
  have hvalue : (∑' n : ℕ, if n = 2 then (Real.log 2 : ℂ) else 0) = (Real.log 2 : ℂ) := by
    simp
  rw [hvalue] at hsumlimit
  refine hsumlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [pwGammaMobiusLogCurrent, ← tsum_div_const]
  exact tsum_congr (pwGammaForcingNormalizedTerm_eq hx)

theorem pwGammaMobiusLogCurrent_eventually_pos :
    ∀ᶠ x : ℝ in atTop, 0 < (pwGammaMobiusLogCurrent x).re := by
  have hreal := (Complex.reCLM.continuous.tendsto (Real.log 2 : ℂ)).comp
    pwGammaMobiusLogCurrent_leading_prime
  have hpos := hreal.eventually_const_lt (Real.log_pos one_lt_two)
  filter_upwards [hpos] with x hx
  change 0 < (pwGammaMobiusLogCurrent x / pwGammaRaySource (2 * x)).re at hx
  rw [pwGammaRaySource, Complex.div_ofReal_re] at hx
  exact (div_pos_iff_of_pos_right (Real.exp_pos _)).mp hx

theorem pwGammaRaySource_double_ratio {x : ℝ} (hx : 0 < x) :
    pwGammaRaySource (2 * x) / pwGammaRaySource x =
      ((Real.sqrt 2 * Real.exp (-x) : ℝ) : ℂ) := by
  rw [pwGammaRaySource_eq (mul_pos two_pos hx), pwGammaRaySource_eq hx,
    Real.sqrt_mul two_pos.le, ← Complex.ofReal_div]
  congr 1
  have he : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [(Real.sqrt_pos.mpr hx).ne', Real.exp_ne_zero]

/-- The retained arithmetic forcing is asymptotically smaller than its original source. -/
theorem pwGammaMobiusLogCurrent_source_quotient :
    Tendsto (fun x : ℝ => pwGammaMobiusLogCurrent x / pwGammaRaySource x)
      atTop (nhds (0 : ℂ)) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hdouble : Tendsto (fun x : ℝ => pwGammaRaySource (2 * x) / pwGammaRaySource x)
      atTop (nhds (0 : ℂ)) := by
    have h := hexp.ofReal.const_mul (Real.sqrt 2 : ℂ)
    simp only [Complex.ofReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [pwGammaRaySource_double_ratio hx, Complex.ofReal_mul]
  have h := pwGammaMobiusLogCurrent_leading_prime.mul hdouble
  simp only [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  field_simp [pwGammaRaySource_ne_zero]

private theorem pwGammaMobiusLogCurrent_log_quotient :
    Tendsto (fun t : ℝ => pwGammaMobiusLogCurrent (Real.exp t) /
      (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ)) atTop (nhds (0 : ℂ)) := by
  simpa only [Function.comp_def, pwGammaRaySource, Real.log_exp] using
    pwGammaMobiusLogCurrent_source_quotient.comp Real.tendsto_exp_atTop

private theorem pwGamma_negative_exp_limit :
    Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

private theorem pwGamma_hyperbolic_scaled_limits :
    Tendsto (fun t : ℝ => Real.sinh t / Real.exp t) atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto (fun t : ℝ => Real.cosh t / Real.exp t) atTop (nhds (1 / 2 : ℝ)) := by
  have htail := pwGamma_negative_exp_limit.div_atTop Real.tendsto_exp_atTop
  constructor
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).sub htail
    have h' := h.div_const 2
    simp only [sub_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Real.sinh_eq]
    field_simp [Real.exp_ne_zero]
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).add htail
    have h' := h.div_const 2
    simp only [add_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Real.cosh_eq]
    field_simp [Real.exp_ne_zero]

private theorem pwGamma_arithmetic_scaled_limit :
    Tendsto (fun t : ℝ => (pwGammaMobiusLogCurrent (Real.exp t) /
      (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ)) / (Real.exp t : ℂ))
      atTop (nhds (0 : ℂ)) := by
  have h := pwGammaMobiusLogCurrent_log_quotient.mul pwGamma_negative_exp_limit.ofReal
  simpa only [Complex.ofReal_zero, mul_zero, Real.exp_neg, Complex.ofReal_inv,
    div_eq_mul_inv] using h

/-- The exact inverse-connection defect survives with coefficient `1/2`, for every shift. -/
theorem pwGammaMobiusLogCurrent_inverse_forcing_defect (z : ℂ) :
    Tendsto (fun t : ℝ => (pwGammaMobiusLogCurrent (Real.exp t) -
      pwGammaInverseConnectionForcing z t) /
      ((Real.exp t : ℂ) * (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ)))
      atTop (nhds (1 / 2 : ℂ)) := by
  have hz := pwGamma_negative_exp_limit.ofReal.const_mul z
  have h := (pwGamma_arithmetic_scaled_limit.add
    pwGamma_hyperbolic_scaled_limits.1.ofReal).add hz
  simp only [Complex.ofReal_zero, mul_zero, zero_add, add_zero, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  have hq : (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ) ≠ 0 := by
    unfold GaloisForLFunctions.expShift
    exact_mod_cast Real.exp_ne_zero _
  have he : (Real.exp t : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero t
  unfold pwGammaInverseConnectionForcing
  rw [Real.exp_neg, Complex.ofReal_inv]
  field_simp
  ring

/-- The positive-connection defect has the different exact coefficient `3/2`. -/
theorem pwGammaMobiusLogCurrent_positive_forcing_defect (z : ℂ) :
    Tendsto (fun t : ℝ => (pwGammaMobiusLogCurrent (Real.exp t) -
      pwGammaConnectionForcing z t) /
      ((Real.exp t : ℂ) * (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ)))
      atTop (nhds (3 / 2 : ℂ)) := by
  have hsmall := pwGamma_negative_exp_limit.ofReal.const_mul (z - 1)
  have h := ((pwGamma_arithmetic_scaled_limit.add (tendsto_const_nhds (x := (1 : ℂ)))).add
    pwGamma_hyperbolic_scaled_limits.2.ofReal).add hsmall
  have hlim : (0 : ℂ) + 1 + ((1 / 2 : ℝ) : ℂ) + (z - 1) * (0 : ℝ) = 3 / 2 := by
    push_cast
    ring
  rw [hlim] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  have hq : (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ) ≠ 0 := by
    unfold GaloisForLFunctions.expShift
    exact_mod_cast Real.exp_ne_zero _
  have he : (Real.exp t : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero t
  unfold pwGammaConnectionForcing
  rw [Real.exp_neg, Complex.ofReal_inv]
  push_cast
  field_simp
  ring

theorem pwGammaMobiusLogCurrent_ne_inverse_forcing (z : ℂ) :
    (fun t : ℝ => pwGammaMobiusLogCurrent (Real.exp t)) ≠
      pwGammaInverseConnectionForcing z := by
  intro heq
  have h := pwGammaMobiusLogCurrent_inverse_forcing_defect z
  simp only [← heq, sub_self, zero_div] at h
  have hz : (1 / 2 : ℂ) = 0 := tendsto_nhds_unique h tendsto_const_nhds
  exact (div_ne_zero one_ne_zero two_ne_zero) hz

theorem pwGammaMobiusLogCurrent_ne_positive_forcing (z : ℂ) :
    (fun t : ℝ => pwGammaMobiusLogCurrent (Real.exp t)) ≠
      pwGammaConnectionForcing z := by
  intro heq
  have h := pwGammaMobiusLogCurrent_positive_forcing_defect z
  simp only [← heq, sub_self, zero_div] at h
  have hz : (3 / 2 : ℂ) = 0 := tendsto_nhds_unique h tendsto_const_nhds
  have hthree : (3 : ℂ) ≠ 0 := by exact_mod_cast (show (3 : ℝ) ≠ 0 by positivity)
  exact (div_ne_zero hthree two_ne_zero) hz

/-- The inverse gain transports a source-relative quotient exactly to the opposite end. -/
theorem pwLogInverseGainReflection_source_quotient (f : ℝ → ℂ) (t : ℝ) :
    pwLogInverseGainReflection f t / (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ) =
      f (-t) / (GaloisForLFunctions.expShift (1 / 2) 0 (-t) : ℂ) := by
  unfold pwLogInverseGainReflection
  rw [← pwGammaSource_gain_transport]
  ring

/-- At the reflected end the full arithmetic forcing remains smaller than the Gamma source. -/
theorem pwGammaMobiusLogCurrent_reflected_source_quotient :
    Tendsto (fun t : ℝ =>
      pwLogInverseGainReflection (fun u => pwGammaMobiusLogCurrent (Real.exp u)) t /
        (GaloisForLFunctions.expShift (1 / 2) 0 t : ℂ)) atBot (nhds (0 : ℂ)) := by
  simpa only [Function.comp_def, pwLogInverseGainReflection_source_quotient] using
    pwGammaMobiusLogCurrent_log_quotient.comp tendsto_neg_atBot_atTop

/-- Closed first-prime law and separation from both raw Gamma connection forcings. -/
theorem pwGammaMobiusForcing_leading_and_separation :
    Tendsto (fun x : ℝ => pwGammaMobiusLogCurrent x / pwGammaRaySource (2 * x))
      atTop (nhds (Real.log 2 : ℂ)) ∧
    (∀ᶠ x : ℝ in atTop, 0 < (pwGammaMobiusLogCurrent x).re) ∧
    ∀ z : ℂ,
      (fun t : ℝ => pwGammaMobiusLogCurrent (Real.exp t)) ≠ pwGammaInverseConnectionForcing z ∧
      (fun t : ℝ => pwGammaMobiusLogCurrent (Real.exp t)) ≠ pwGammaConnectionForcing z := by
  exact ⟨pwGammaMobiusLogCurrent_leading_prime, pwGammaMobiusLogCurrent_eventually_pos,
    fun z => ⟨pwGammaMobiusLogCurrent_ne_inverse_forcing z,
      pwGammaMobiusLogCurrent_ne_positive_forcing z⟩⟩

end
end RHTower
