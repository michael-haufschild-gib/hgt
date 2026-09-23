import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Oscillatory integrals against a growing phase vanish

The mean value of `cos` is what survives a weak limit: a `C¹` weight tested against `cos (c ξ)`
tends to zero as the frequency grows, at rate `1/c`, by one integration by parts.  This is the
estimate that turns a pointwise oscillation `cos²(cξ) = (1 + cos(2cξ))/2` into its mean `1/2` after
integration against a test function, which is how a weak limit of oscillating densities is
computed.

The bound is explicit — boundary terms plus the total variation of the weight, all divided by the
frequency — so it gives the rate, not merely the limit.  The phase is arbitrary: the derivative of
the phase is carried by the weight, which is exactly the shape a change of variables produces.
-/

open MeasureTheory Filter Set intervalIntegral

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of `ξ' cos (c ξ)`. -/
theorem hasDerivAt_sin_comp_div {c φ : ℝ} (hc : c ≠ 0) {ξ ξ' : ℝ → ℝ}
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (c * ξ y + φ) / c) (ξ' x * Real.cos (c * ξ x + φ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * ξ y + φ) (c * ξ' x) x := by
    simpa using ((hξ x).const_mul c).add_const φ
  have h2 : HasDerivAt (fun y : ℝ => Real.sin (c * ξ y + φ))
      (Real.cos (c * ξ x + φ) * (c * ξ' x)) x := h1.sin
  have h3 := h2.div_const c
  have hval : Real.cos (c * ξ x + φ) * (c * ξ' x) / c = ξ' x * Real.cos (c * ξ x + φ) := by
    field_simp
  rwa [hval] at h3

/-- One integration by parts against an arbitrary phase. -/
theorem integral_mul_cos_comp_eq {a b c φ : ℝ} (hc : c ≠ 0) {g g' ξ ξ' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ') :
    ∫ x in a..b, g x * (ξ' x * Real.cos (c * ξ x + φ))
      = g b * (Real.sin (c * ξ b + φ) / c) - g a * (Real.sin (c * ξ a + φ) / c)
        - ∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c) := by
  have hξc : Continuous ξ := continuous_iff_continuousAt.mpr fun x => (hξ x).continuousAt
  have hintg' : IntervalIntegrable g' volume a b := hg'c.intervalIntegrable a b
  have hcv' : Continuous fun x : ℝ => ξ' x * Real.cos (c * ξ x + φ) := by
    exact hξ'c.mul (Real.continuous_cos.comp ((continuous_const.mul hξc).add continuous_const))
  have hintv' : IntervalIntegrable (fun x : ℝ => ξ' x * Real.cos (c * ξ x + φ)) volume a b :=
    hcv'.intervalIntegrable a b
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (u' := g') (v := fun y => Real.sin (c * ξ y + φ) / c)
    (v' := fun x => ξ' x * Real.cos (c * ξ x + φ))
    (fun x _ => hg x) (fun x _ => hasDerivAt_sin_comp_div hc hξ x) hintg' hintv'

/-- **An oscillatory integral vanishes at rate `1/c`.** -/
theorem abs_integral_mul_cos_comp_le {a b c φ : ℝ} (hab : a ≤ b) (hc : 0 < c)
    {g g' ξ ξ' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ') :
    |∫ x in a..b, g x * (ξ' x * Real.cos (c * ξ x + φ))|
      ≤ (|g a| + |g b| + ∫ x in a..b, |g' x|) / c := by
  have hξc : Continuous ξ := continuous_iff_continuousAt.mpr fun x => (hξ x).continuousAt
  have hcne : c ≠ 0 := ne_of_gt hc
  have hbnd : ∀ (w : ℝ) (y : ℝ), |w * (Real.sin (c * ξ y + φ) / c)| ≤ |w| / c := by
    intro w y
    rw [abs_mul, abs_div, abs_of_pos hc]
    calc |w| * (|Real.sin (c * ξ y + φ)| / c) ≤ |w| * (1 / c) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg w)
          exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hc.le
      _ = |w| / c := by rw [mul_one_div]
  have hcontv : Continuous fun x : ℝ => Real.sin (c * ξ x + φ) / c :=
    (Real.continuous_sin.comp ((continuous_const.mul hξc).add continuous_const)).div_const c
  have hintabs : IntervalIntegrable (fun x => |g' x|) volume a b :=
    hg'c.abs.intervalIntegrable a b
  have hintprod : IntervalIntegrable (fun x => g' x * (Real.sin (c * ξ x + φ) / c)) volume a b :=
    (hg'c.mul hcontv).intervalIntegrable a b
  have htail : |∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c)| ≤ (∫ x in a..b, |g' x|) / c := by
    have h1 : |∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c)|
        ≤ ∫ x in a..b, |g' x * (Real.sin (c * ξ x + φ) / c)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : ∫ x in a..b, |g' x * (Real.sin (c * ξ x + φ) / c)| ≤ ∫ x in a..b, |g' x| / c :=
      intervalIntegral.integral_mono_on hab hintprod.abs (hintabs.div_const c)
        fun x _ => hbnd (g' x) x
    have h3 : ∫ x in a..b, |g' x| / c = (∫ x in a..b, |g' x|) / c := by
      rw [intervalIntegral.integral_div]
    linarith [h1, h2, h3.le, h3.ge]
  rw [integral_mul_cos_comp_eq hcne hg hg'c hξ hξ'c]
  have hsplit : (|g a| + |g b| + ∫ x in a..b, |g' x|) / c
      = |g a| / c + |g b| / c + (∫ x in a..b, |g' x|) / c := by
    rw [add_div, add_div]
  rw [hsplit]
  calc |g b * (Real.sin (c * ξ b + φ) / c) - g a * (Real.sin (c * ξ a + φ) / c)
        - ∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c)|
      ≤ |g b * (Real.sin (c * ξ b + φ) / c) - g a * (Real.sin (c * ξ a + φ) / c)|
        + |∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c)| := abs_sub _ _
    _ ≤ (|g b * (Real.sin (c * ξ b + φ) / c)| + |g a * (Real.sin (c * ξ a + φ) / c)|)
        + |∫ x in a..b, g' x * (Real.sin (c * ξ x + φ) / c)| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ (|g b| / c + |g a| / c) + (∫ x in a..b, |g' x|) / c :=
        add_le_add (add_le_add (hbnd (g b) b) (hbnd (g a) a)) htail
    _ = |g a| / c + |g b| / c + (∫ x in a..b, |g' x|) / c := by ring

/-- The limit form, arbitrary phase. -/
theorem tendsto_integral_mul_cos_comp_atTop {a b φ : ℝ} (hab : a ≤ b) {g g' ξ ξ' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ') :
    Tendsto (fun c : ℝ => ∫ x in a..b, g x * (ξ' x * Real.cos (c * ξ x + φ))) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun c : ℝ =>
    (|g a| + |g b| + ∫ x in a..b, |g' x|) / c) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
    exact abs_integral_mul_cos_comp_le hab hc hg hg'c hξ hξ'c
  · exact Filter.Tendsto.const_div_atTop Filter.tendsto_id _


/-! ### The mean of a squared oscillation -/

/-- **`cos²` contributes its mean `1/2` to a weak limit.** -/
theorem tendsto_integral_mul_cos_sq_comp_atTop {a b φ : ℝ} (hab : a ≤ b) {g g' ξ ξ' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ') :
    Tendsto (fun c : ℝ => ∫ x in a..b, g x * (ξ' x * Real.cos (c * ξ x + φ) ^ (2 : ℕ))) atTop
      (𝓝 ((1 / 2) * ∫ x in a..b, g x * ξ' x)) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hξc : Continuous ξ := continuous_iff_continuousAt.mpr fun x => (hξ x).continuousAt
  have hsplit : ∀ c : ℝ, (∫ x in a..b, g x * (ξ' x * Real.cos (c * ξ x + φ) ^ (2 : ℕ)))
      = (1 / 2) * (∫ x in a..b, g x * ξ' x)
        + (1 / 2) * (∫ x in a..b, g x * (ξ' x * Real.cos (2 * c * ξ x + 2 * φ))) := by
    intro c
    have hint1 : IntervalIntegrable (fun x : ℝ => 1 / 2 * (g x * ξ' x)) volume a b :=
      ((continuous_const.mul (hgc.mul hξ'c))).intervalIntegrable a b
    have hint2 : IntervalIntegrable
        (fun x : ℝ => 1 / 2 * (g x * (ξ' x * Real.cos (2 * c * ξ x + 2 * φ)))) volume a b := by
      refine Continuous.intervalIntegrable ?_ a b
      exact continuous_const.mul (hgc.mul (hξ'c.mul (Real.continuous_cos.comp
        ((continuous_const.mul hξc).add continuous_const))))
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr fun x _ => ?_
    show g x * (ξ' x * Real.cos (c * ξ x + φ) ^ (2 : ℕ))
      = 1 / 2 * (g x * ξ' x) + 1 / 2 * (g x * (ξ' x * Real.cos (2 * c * ξ x + 2 * φ)))
    rw [show 2 * c * ξ x + 2 * φ = 2 * (c * ξ x + φ) from by ring, Real.cos_sq]
    ring
  have hdouble : Tendsto (fun c : ℝ => 2 * c) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) Filter.tendsto_id
  have hosc : Tendsto (fun c : ℝ => ∫ x in a..b, g x * (ξ' x * Real.cos (2 * c * ξ x + 2 * φ)))
      atTop (𝓝 0) :=
    (tendsto_integral_mul_cos_comp_atTop (φ := 2 * φ) hab hg hg'c hξ hξ'c).comp hdouble
  have hsum := (tendsto_const_nhds (x := (1 / 2) * ∫ x in a..b, g x * ξ' x) (f := atTop)).add
    (hosc.const_mul (1 / 2))
  rw [mul_zero, add_zero] at hsum
  exact hsum.congr fun c => (hsplit c).symm

/-! ### The linear phase -/

theorem abs_integral_mul_cos_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') :
    |∫ x in a..b, f x * Real.cos (c * x)|
      ≤ (|f a| + |f b| + ∫ x in a..b, |f' x|) / c := by
  have h := abs_integral_mul_cos_comp_le (g := f) (g' := f') (ξ := fun x => x)
    (ξ' := fun _ => 1) (φ := 0) hab hc hderiv hcont (fun x => hasDerivAt_id x) continuous_const
  simpa using h

theorem tendsto_integral_mul_cos_atTop {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') :
    Tendsto (fun c : ℝ => ∫ x in a..b, f x * Real.cos (c * x)) atTop (𝓝 0) := by
  have h := tendsto_integral_mul_cos_comp_atTop (g := f) (g' := f') (ξ := fun x => x)
    (ξ' := fun _ => 1) (φ := 0) hab hderiv hcont (fun x => hasDerivAt_id x) continuous_const
  simpa using h

end GaloisForLFunctions.HTGeometry
