import Mathlib

/-!
# A slowly varying weight against a mean-square asymptotic

The dual×dual term of Levinson's mollified mean square is the mean square of a Dirichlet polynomial
against the weight `|χ(σ₀+it)|² = (t/2π)^{2R/log T}`.  The weight is not constant, so the
mean-value theorem cannot be applied directly; but it is smooth and increasing, so one integration
by parts transfers the mean-value asymptotic through it, at the cost of `E·(2w(b) − w(a))` where `E`
is the mean-value error on every initial subinterval.

This is exactly the step that turns the constant `∑|c_n|²` into Young's `∫_0^(1 : ℕ) e^{2Rv}(…) dv`.
-/

open MeasureTheory intervalIntegral Set

noncomputable section

namespace RHTower

/-- **Weighted transfer of a mean-square asymptotic.** -/
theorem abs_integral_weighted_meanSquare_sub_le
    {a b M E : ℝ} (hab : a ≤ b) {w w' : ℝ → ℝ} {D : ℝ → ℂ}
    (hD : Continuous D)
    (hw : ∀ τ ∈ Set.uIcc a b, HasDerivAt w (w' τ) τ) (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hw'nn : ∀ τ ∈ Set.Icc a b, 0 ≤ w' τ) (hwa : 0 ≤ w a)
    (hmvt : ∀ u ∈ Set.Icc a b, |(∫ τ in a..u, ‖D τ‖ ^ 2) - (u - a) * M| ≤ E) :
    |(∫ τ in a..b, w τ * ‖D τ‖ ^ 2) - M * (∫ τ in a..b, w τ)|
      ≤ E * (w b + (w b - w a)) := by
  classical
  have hDsq : Continuous fun τ : ℝ => ‖D τ‖ ^ 2 := (hD.norm.pow 2)
  set V : ℝ → ℝ := fun u => ∫ τ in a..u, ‖D τ‖ ^ 2 with hV
  have hVd : ∀ u : ℝ, HasDerivAt V (‖D u‖ ^ 2) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hDsq.intervalIntegrable a u)
      (hDsq.stronglyMeasurableAtFilter _ _) hDsq.continuousAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun u => (hVd u).continuousAt
  have hVa : V a = 0 := by simp [hV]
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hwc : ContinuousOn w (Set.uIcc a b) := fun u hu => (hw u hu).continuousAt.continuousWithinAt
  have hw'i : IntervalIntegrable w' volume a b := hw'c.intervalIntegrable
  -- integration by parts against `V`
  have hparts : (∫ τ in a..b, w τ * ‖D τ‖ ^ 2)
      = w b * V b - w a * V a - ∫ τ in a..b, w' τ * V τ := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := w) (u' := w') (v := V) (v' := fun τ => ‖D τ‖ ^ 2)
      (fun x hx => hw x hx) (fun x _ => hVd x)
      hw'i (hDsq.intervalIntegrable a b)
    exact h
  -- integration by parts for the weight itself
  have hlin : ∀ x : ℝ, HasDerivAt (fun τ : ℝ => τ - a) 1 x := by
    intro x
    simpa using (hasDerivAt_id x).sub_const a
  have hpartsw : (∫ τ in a..b, w τ * 1)
      = w b * (b - a) - w a * (a - a) - ∫ τ in a..b, w' τ * (τ - a) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := w) (u' := w') (v := fun τ : ℝ => τ - a) (v' := fun _ : ℝ => (1 : ℝ))
      (fun x hx => hw x hx) (fun x _ => hlin x)
      hw'i intervalIntegrable_const
    exact h
  have hwint : (∫ τ in a..b, w τ) = w b * (b - a) - ∫ τ in a..b, w' τ * (τ - a) := by
    have hrw : (∫ τ in a..b, w τ * 1) = ∫ τ in a..b, w τ := by
      simp
    rw [hrw] at hpartsw
    simpa using hpartsw
  -- the difference is the weighted remainder
  have hdiff : (∫ τ in a..b, w τ * ‖D τ‖ ^ 2) - M * (∫ τ in a..b, w τ)
      = w b * (V b - (b - a) * M) - ∫ τ in a..b, w' τ * (V τ - (τ - a) * M) := by
    have hsplitpt : ∀ τ : ℝ, w' τ * (V τ - (τ - a) * M)
        = w' τ * V τ - M * (w' τ * (τ - a)) := by
      intro τ; ring
    have hsub : (∫ τ in a..b, w' τ * (V τ - (τ - a) * M))
        = (∫ τ in a..b, w' τ * V τ) - M * ∫ τ in a..b, w' τ * (τ - a) := by
      have hint1 : IntervalIntegrable (fun τ : ℝ => w' τ * V τ) volume a b :=
        (hw'c.mul hVc.continuousOn).intervalIntegrable
      have hint2 : IntervalIntegrable (fun τ : ℝ => M * (w' τ * (τ - a))) volume a b := by
        refine ContinuousOn.intervalIntegrable ?_
        exact continuousOn_const.mul (hw'c.mul (continuousOn_id.sub continuousOn_const))
      rw [intervalIntegral.integral_congr (fun τ _ => hsplitpt τ),
        intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul]
    rw [hparts, hwint, hsub, hVa]
    ring
  rw [hdiff]
  -- bound the two pieces
  have hwdiff : w b - w a = ∫ τ in a..b, w' τ :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hw x hx) hw'i).symm
  have hwmono : w a ≤ w b := by
    have hnn : (0 : ℝ) ≤ ∫ τ in a..b, w' τ :=
      intervalIntegral.integral_nonneg hab (fun x hx => hw'nn x hx)
    linarith [hwdiff, hnn]
  have hwb : 0 ≤ w b := le_trans hwa hwmono
  have hb1 : |w b * (V b - (b - a) * M)| ≤ w b * E := by
    rw [abs_mul, abs_of_nonneg hwb]
    refine mul_le_mul_of_nonneg_left ?_ hwb
    have := hmvt b (Set.right_mem_Icc.mpr hab)
    rw [show V b - (b - a) * M = (∫ τ in a..b, ‖D τ‖ ^ 2) - (b - a) * M from rfl]
    exact this
  have hb2 : |∫ τ in a..b, w' τ * (V τ - (τ - a) * M)| ≤ E * (w b - w a) := by
    have hint : IntervalIntegrable (fun τ : ℝ => w' τ * (V τ - (τ - a) * M)) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      exact hw'c.mul ((hVc.continuousOn).sub
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const))
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := (volume : Measure ℝ)) hab
      (f := fun τ : ℝ => w' τ * (V τ - (τ - a) * M))
    refine le_trans habs ?_
    have hpt : ∀ τ ∈ Set.Icc a b, |w' τ * (V τ - (τ - a) * M)| ≤ w' τ * E := by
      intro τ hτ
      rw [abs_mul, abs_of_nonneg (hw'nn τ hτ)]
      refine mul_le_mul_of_nonneg_left ?_ (hw'nn τ hτ)
      have := hmvt τ hτ
      rw [show V τ - (τ - a) * M = (∫ u in a..τ, ‖D u‖ ^ 2) - (τ - a) * M from rfl]
      exact this
    have hmono2 : (∫ τ in a..b, |w' τ * (V τ - (τ - a) * M)|) ≤ ∫ τ in a..b, w' τ * E := by
      refine intervalIntegral.integral_mono_on hab (hint.abs)
        ((hw'c.mul continuousOn_const).intervalIntegrable) hpt
    refine le_trans hmono2 ?_
    have hval : (∫ τ in a..b, w' τ * E) = (w b - w a) * E := by
      rw [intervalIntegral.integral_mul_const]
      congr 1
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hw x hx) hw'i
    rw [hval]
    exact le_of_eq (by ring)
  have htri := abs_sub (w b * (V b - (b - a) * M))
    (∫ τ in a..b, w' τ * (V τ - (τ - a) * M))
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hmvt a (Set.left_mem_Icc.mpr hab))
  calc |w b * (V b - (b - a) * M) - ∫ τ in a..b, w' τ * (V τ - (τ - a) * M)|
      ≤ |w b * (V b - (b - a) * M)| + |∫ τ in a..b, w' τ * (V τ - (τ - a) * M)| := htri
    _ ≤ w b * E + E * (w b - w a) := by linarith [hb1, hb2]
    _ = E * (w b + (w b - w a)) := by ring


/-! ## The modulus of `χ` on Levinson's abscissa, as a weight -/

/-- `|χ(σ₀+it)|² = (t/2π)^{2(1/2−σ₀)}`, written as a weight in the height with exponent `α`. -/
def chiModulusWeight (α t : ℝ) : ℝ := (t / (2 * Real.pi)) ^ α

theorem chiModulusWeight_pos {α t : ℝ} (ht : 0 < t) : 0 < chiModulusWeight α t := by
  unfold chiModulusWeight
  exact Real.rpow_pos_of_pos (by positivity) α

theorem hasDerivAt_chiModulusWeight {α t : ℝ} (ht : 0 < t) :
    HasDerivAt (chiModulusWeight α) (α / t * chiModulusWeight α t) t := by
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  have hq : (0 : ℝ) < t / (2 * Real.pi) := by positivity
  have hpath : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * Real.pi)
  have hbase : HasDerivAt (fun x : ℝ => x ^ α)
      (α * (t / (2 * Real.pi)) ^ (α - 1)) (t / (2 * Real.pi)) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hq))
  have hcomp := hbase.comp t hpath
  have hcomp' : HasDerivAt (fun x : ℝ => (x / (2 * Real.pi)) ^ α)
      (α * (t / (2 * Real.pi)) ^ (α - 1) * (1 / (2 * Real.pi))) t := hcomp
  have hval : α * (t / (2 * Real.pi)) ^ (α - 1) * (1 / (2 * Real.pi))
      = α / t * chiModulusWeight α t := by
    unfold chiModulusWeight
    rw [Real.rpow_sub hq, Real.rpow_one]
    field_simp
  exact hcomp'.congr_deriv hval

theorem deriv_chiModulusWeight_nonneg {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    0 ≤ α / t * chiModulusWeight α t := by
  have := chiModulusWeight_pos (α := α) ht
  positivity

theorem continuousOn_deriv_chiModulusWeight {α a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => α / t * chiModulusWeight α t) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun u : ℝ => α / u) t :=
    continuousAt_const.div continuousAt_id (ne_of_gt ht0)
  have h2 : ContinuousAt (chiModulusWeight α) t :=
    (hasDerivAt_chiModulusWeight ht0).continuousAt
  exact h1.mul h2

end RHTower

end
