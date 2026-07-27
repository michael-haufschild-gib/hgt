import GaloisForLFunctions.RHTower.VanDerCorputLocal

/-!
# A nonstationary square keeps half its mass

A pointwise envelope bound on an oscillatory function says nothing about how much `L²` mass its
main term carries: `cos` vanishes at its zeros, so no pointwise comparison survives there.  What
does survive is an averaged statement.  If the phase is nonstationary — `|φ'| ≥ lam > 0` with `φ'`
monotone — then

`∫ w cos²φ = (1/2) ∫ w + O(1/lam)`,

and the error is controlled by the endpoint values and the *variation* of the weight, never by its
integral.  So as soon as the oscillation is fast compared with the weight's variation, the
oscillating square retains a definite fraction of the plain mass.

This is the step that turns a Liouville–Green envelope into a relative `L²` mass.  The input it
needs — a floor on the phase speed together with its monotonicity — is exactly what the exterior
radial prolate speed supplies: `one_le_radialPSWFExteriorSpeed` gives the floor,
`antitoneOn_radialPSWFExteriorSpeed` the monotonicity, and the antitone direction is the primed
statement below.

The proof is the first-derivative test applied to the doubled phase `2φ`.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- **Nonstationary averaging of a square, increasing phase speed.**  The oscillating square differs
from half the plain mass by at most the amplitude budget divided by the phase-speed floor. -/
theorem abs_integral_weight_mul_cos_sq_sub_half_le
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {w w' φ φ' φ'' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hnn : ∀ x ∈ Icc a b, 0 ≤ φ'' x)
    (hbound : ∀ x ∈ Icc a b, lam ≤ |φ' x|) :
    |(∫ t in a..b, w t * Real.cos (φ t) ^ 2) - (1 / 2) * ∫ t in a..b, w t|
      ≤ (|w b| + |w a| + ∫ t in a..b, |w' t|) / lam := by
  have hwc : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Icc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  set Φ : ℝ → ℝ := fun t => 2 * φ t with hΦdef
  set A : ℝ → ℂ := fun t => ((w t : ℝ) : ℂ) with hAdef
  set A' : ℝ → ℂ := fun t => ((w' t : ℝ) : ℂ) with hA'def
  have hAd : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x := fun x hx => ((hw x hx).ofReal_comp)
  have hA'c : ContinuousOn A' (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hw'c
  have hΦd : ∀ x ∈ Icc a b, HasDerivAt Φ (2 * φ' x) x := fun x hx => (hφ x hx).const_mul 2
  have hΦ'd : ∀ x ∈ Icc a b, HasDerivAt (fun t => 2 * φ' t) (2 * φ'' x) x :=
    fun x hx => (hφ' x hx).const_mul 2
  have hΦ''c : ContinuousOn (fun t => 2 * φ'' t) (Icc a b) := continuousOn_const.mul hφ''c
  have hkey : ‖∫ t in a..b, A t * Complex.exp (Complex.I * Φ t)‖
      ≤ 4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖) / (2 * lam) := by
    refine firstDerivTestOn hab (by linarith) hΦd hΦ'd hΦ''c hAd hA'c ?_ ?_
    · intro x hx
      have := hnn x hx
      linarith
    · intro x hx
      have := hbound x hx
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith
  have hnormA : ∀ t : ℝ, ‖A t‖ = |w t| := fun t => by
    rw [hAdef, Complex.norm_real, Real.norm_eq_abs]
  have hnormA' : (∫ t in a..b, ‖A' t‖) = ∫ t in a..b, |w' t| :=
    intervalIntegral.integral_congr fun t _ => by
      rw [hA'def, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormA, hnormA, hnormA'] at hkey
  have hAEc : ContinuousOn (fun t => A t * Complex.exp (Complex.I * Φ t)) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hφc))))
  have hintc : IntervalIntegrable (fun t => A t * Complex.exp (Complex.I * Φ t)) volume a b :=
    (uIcc_of_le hab ▸ hAEc).intervalIntegrable
  have hre : (∫ t in a..b, A t * Complex.exp (Complex.I * Φ t)).re
      = ∫ t in a..b, w t * Real.cos (Φ t) := by
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hintc
    simp only [Complex.reCLM_apply] at hcomm
    rw [← hcomm]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp [hAdef, mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_ofReal_re]
  have habs : |∫ t in a..b, w t * Real.cos (Φ t)|
      ≤ 2 * ((|w b| + |w a| + ∫ t in a..b, |w' t|) / lam) := by
    have h1 : |∫ t in a..b, w t * Real.cos (Φ t)|
        ≤ ‖∫ t in a..b, A t * Complex.exp (Complex.I * Φ t)‖ := by
      rw [← hre]
      exact Complex.abs_re_le_norm _
    have h2 : 4 * (|w b| + |w a| + ∫ t in a..b, |w' t|) / (2 * lam)
        = 2 * ((|w b| + |w a| + ∫ t in a..b, |w' t|) / lam) := by
      field_simp
      ring
    rw [h2] at hkey
    exact h1.trans hkey
  have hsplit : (∫ t in a..b, w t * Real.cos (φ t) ^ 2)
      = (1 / 2) * (∫ t in a..b, w t) + (1 / 2) * ∫ t in a..b, w t * Real.cos (Φ t) := by
    have hcongr : ∀ t : ℝ, w t * Real.cos (φ t) ^ 2
        = (1 / 2 : ℝ) * w t + (1 / 2) * (w t * Real.cos (Φ t)) := by
      intro t
      rw [hΦdef, Real.cos_sq]
      ring
    have hi1 : IntervalIntegrable (fun t => (1 / 2 : ℝ) * w t) volume a b :=
      (uIcc_of_le hab ▸ (continuousOn_const.mul hwc)).intervalIntegrable
    have hcosc : ContinuousOn (fun t => Real.cos (Φ t)) (Icc a b) :=
      Real.continuous_cos.comp_continuousOn (continuousOn_const.mul hφc)
    have hi2 : IntervalIntegrable (fun t => (1 / 2 : ℝ) * (w t * Real.cos (Φ t))) volume a b :=
      (uIcc_of_le hab ▸ (continuousOn_const.mul (hwc.mul hcosc))).intervalIntegrable
    rw [show (fun t => w t * Real.cos (φ t) ^ 2)
        = fun t => (1 / 2 : ℝ) * w t + (1 / 2) * (w t * Real.cos (Φ t)) from funext hcongr,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit,
    show (1 / 2) * (∫ t in a..b, w t) + (1 / 2) * (∫ t in a..b, w t * Real.cos (Φ t))
        - (1 / 2) * ∫ t in a..b, w t = (1 / 2) * ∫ t in a..b, w t * Real.cos (Φ t) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  linarith [habs]

/-- **Nonstationary averaging of a square, decreasing phase speed.**  The same estimate when `φ'` is
nonincreasing — the case of a Liouville phase whose speed relaxes to its free value.  Obtained from
the increasing case by reflecting the phase, which the square does not see. -/
theorem abs_integral_weight_mul_cos_sq_sub_half_le'
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {w w' φ φ' φ'' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hnp : ∀ x ∈ Icc a b, φ'' x ≤ 0)
    (hbound : ∀ x ∈ Icc a b, lam ≤ |φ' x|) :
    |(∫ t in a..b, w t * Real.cos (φ t) ^ 2) - (1 / 2) * ∫ t in a..b, w t|
      ≤ (|w b| + |w a| + ∫ t in a..b, |w' t|) / lam := by
  have hmain := abs_integral_weight_mul_cos_sq_sub_half_le (φ := fun t => -φ t)
    (φ' := fun t => -φ' t) (φ'' := fun t => -φ'' t) hab hlam hw hw'c
    (fun x hx => (hφ x hx).neg) (fun x hx => (hφ' x hx).neg) hφ''c.neg
    (fun x hx => by linarith [hnp x hx])
    (fun x hx => by rw [abs_neg]; exact hbound x hx)
  simpa only [Real.cos_neg] using hmain

/-- **Relative mass retention.**  Once the amplitude budget is small compared with the plain mass,
the oscillating square keeps at least a quarter of it.  An envelope bound alone cannot give this,
because the oscillation vanishes at its zeros. -/
theorem quarter_integral_le_integral_weight_mul_cos_sq
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {w w' φ φ' φ'' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hnp : ∀ x ∈ Icc a b, φ'' x ≤ 0)
    (hbound : ∀ x ∈ Icc a b, lam ≤ |φ' x|)
    (hbudget : (|w b| + |w a| + ∫ t in a..b, |w' t|) / lam ≤ (1 / 4) * ∫ t in a..b, w t) :
    (1 / 4) * (∫ t in a..b, w t) ≤ ∫ t in a..b, w t * Real.cos (φ t) ^ 2 := by
  have hmain := abs_integral_weight_mul_cos_sq_sub_half_le' hab hlam hw hw'c hφ hφ' hφ''c hnp hbound
  linarith [neg_le_of_abs_le hmain]

end

end RHTower
