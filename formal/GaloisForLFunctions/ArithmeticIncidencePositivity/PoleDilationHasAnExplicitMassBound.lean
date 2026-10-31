import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleMomentsHaveQuadraticDilationError
import GaloisForLFunctions.ArithmeticCriticalityTheory.NonnegativeConeZeroFormCriterion
import GaloisForLFunctions.RHTower.SeparatedBumpPrimeBlindPositivity

/-!
# Explicit dilation cost of the actual polar form

Exponential moments are uniformly Lipschitz in their real parameter on a
fixed compact support. Their product and physical dilation therefore have
an explicit bound in the squared source norm, including both source signs.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open RenormalizedArithmeticPotentialTheory ArithmeticCriticalityTheory

private theorem abs_exp_parameter_sub_le {q q' u : ℝ}
    (hq : |q| ≤ 1 / 2) (hq' : |q'| ≤ 1 / 2) (hu : |u| ≤ 1 / 2) :
    |Real.exp (q * u) - Real.exp (q' * u)| ≤
      (Real.exp 1 / 2) * |q - q'| := by
  have hd (a : ℝ) : HasDerivAt (fun a => Real.exp (a * u))
      (Real.exp (a * u) * u) a := by
    convert! (Real.hasDerivAt_exp (a * u)).comp a ((hasDerivAt_id a).mul_const u) using 1
    simp only [one_mul]
  have hb (a : ℝ) (ha : a ∈ Icc (-(1 / 2)) (1 / 2)) :
      ‖deriv (fun a => Real.exp (a * u)) a‖ ≤ Real.exp 1 / 2 := by
    rw [(hd a).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (a * u) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul (abs_le.mpr ha) hu (abs_nonneg u) (by norm_num)
      have hle := le_abs_self (a * u)
      rw [abs_mul] at hle
      linarith only [hmul, hle]
    exact (mul_le_mul hexp hu (abs_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun a _ => (hd a).differentiableAt)
    hb (convex_Icc _ _) (abs_le.mp hq') (abs_le.mp hq)
  simpa only [Real.norm_eq_abs] using h

/-- A pole parameter in the unit interval has moment bounded by absolute mass. -/
theorem abs_centered_exponentialMoment_le {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {q : ℝ} (hq : |q| ≤ 1 / 2) :
    |atomExponentialMoment f q| ≤ Real.exp 1 * ∫ u, |f u| := by
  have hi : Integrable (fun u => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hm : Integrable (fun u => f u * Real.exp (q * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  unfold atomExponentialMoment
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono hm.abs (hi.const_mul _) ?_)
  intro u
  change |f u * Real.exp (q * u)| ≤ Real.exp 1 * |f u|
  by_cases hfu : f u = 0
  · simp only [hfu, zero_mul, abs_zero, mul_zero, le_refl]
  have hu : |u| ≤ 1 / 2 := le_of_not_gt fun hu => hfu (hs u hu)
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm (|f u|)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul hq hu (abs_nonneg u) (by norm_num)
  have hle := le_abs_self (q * u)
  rw [abs_mul] at hle
  linarith only [hmul, hle]

/-- On a centered unit support, pole moments are uniformly Lipschitz in the parameter. -/
theorem abs_centered_exponentialMoment_sub_le {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {q q' : ℝ}
    (hq : |q| ≤ 1 / 2) (hq' : |q'| ≤ 1 / 2) :
    |atomExponentialMoment f q - atomExponentialMoment f q'| ≤
      (Real.exp 1 / 2) * |q - q'| * ∫ u, |f u| := by
  have hi : Integrable (fun u => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hm (a : ℝ) : Integrable (fun u => f u * Real.exp (a * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  rw [atomExponentialMoment, atomExponentialMoment, ← integral_sub (hm q) (hm q'),
    ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans
    (integral_mono ((hm q).sub (hm q')).abs (hi.const_mul _) ?_)
  intro u
  change |f u * Real.exp (q * u) - f u * Real.exp (q' * u)| ≤
    Real.exp 1 / 2 * |q - q'| * |f u|
  by_cases hfu : f u = 0
  · simp only [hfu, zero_mul, sub_zero, abs_zero, mul_zero, le_refl]
  have hu : |u| ≤ 1 / 2 := le_of_not_gt fun hu => hfu (hs u hu)
  rw [← mul_sub, abs_mul, mul_comm (|f u|)]
  exact mul_le_mul_of_nonneg_right (abs_exp_parameter_sub_le hq hq' hu) (abs_nonneg _)

/-- Physical dilation scales each actual exponential moment by its Jacobian. -/
theorem exponentialMoment_comp_mul (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (q : ℝ) :
    atomExponentialMoment (fun u => f (r * u)) q =
      r⁻¹ * atomExponentialMoment f (q / r) := by
  unfold atomExponentialMoment
  have heq : (fun u => f (r * u) * Real.exp (q * u)) =
      (fun v => f v * Real.exp ((q / r) * v)) ∘ (fun u => r * u) := by
    funext u
    simp only [Function.comp_apply]
    congr 2
    field_simp
  rw [heq]
  change (∫ u : ℝ, f (r * u) * Real.exp ((q / r) * (r * u))) =
    r⁻¹ * ∫ u : ℝ, f u * Real.exp ((q / r) * u)
  rw [Measure.integral_comp_mul_left (fun v => f v * Real.exp ((q / r) * v)) r,
    abs_of_pos (inv_pos.mpr hr), smul_eq_mul]

/-- The real polar contribution to the full Weil form. -/
def realPoleForm (f : ℝ → ℝ) : ℝ :=
  2 * atomExponentialMoment f (1 / 2) * atomExponentialMoment f (-(1 / 2))

theorem realPoleForm_eq_expMoments (f : ℝ → ℝ) :
    realPoleForm f = 2 * expHalfMoment f * expNegHalfMoment f := by
  have hp : atomExponentialMoment f (1 / 2) = expHalfMoment f := by
    unfold atomExponentialMoment expHalfMoment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      change f u * Real.exp ((1 / 2) * u) = f u * Real.exp (u / 2)
      rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  have hm : atomExponentialMoment f (-(1 / 2)) = expNegHalfMoment f := by
    unfold atomExponentialMoment expNegHalfMoment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      change f u * Real.exp (-(1 / 2) * u) = f u * Real.exp (-(u / 2))
      rw [show -(1 / 2 : ℝ) * u = -(u / 2) by ring]
  rw [realPoleForm, hp, hm]

/-- Both polar moments retain a uniform linear dilation cost in squared source mass. -/
theorem realPoleForm_dilation_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    |r * realPoleForm (fun u => f (r * u)) - realPoleForm f| ≤
      4 * Real.exp 2 * (r - 1) * ∫ u, f u ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let C := Real.exp 1
  let A := ∫ u, |f u|
  let q : ℝ := (1 / 2) / r
  let p := atomExponentialMoment f q
  let m := atomExponentialMoment f (-q)
  let p₀ := atomExponentialMoment f (1 / 2)
  let m₀ := atomExponentialMoment f (-(1 / 2))
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  have hC : 0 < C := Real.exp_pos _
  have hs0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hq0 : 0 ≤ q := div_nonneg (by norm_num) hr0.le
  have hq : q ≤ 1 / 2 := (div_le_iff₀ hr0).mpr (by linarith only [hr])
  have hqabs : |q| ≤ 1 / 2 := by rw [abs_of_nonneg hq0]; exact hq
  have hqd : |q - 1 / 2| ≤ (r - 1) / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq)]
    have hqr : q * r = 1 / 2 := div_mul_cancel₀ _ hr0.ne'
    apply le_of_not_gt
    intro hbad
    have hmul := mul_lt_mul_of_pos_right hbad hr0
    nlinarith only [sq_nonneg (r - 1), hqr, hmul]
  have hp : |p| ≤ C * A := abs_centered_exponentialMoment_le hf.continuous hfc hs hqabs
  have hm : |m| ≤ C * A := abs_centered_exponentialMoment_le hf.continuous hfc hs
    (by simpa only [abs_neg] using hqabs)
  have hp₀ : |p₀| ≤ C * A := abs_centered_exponentialMoment_le hf.continuous hfc hs (by norm_num)
  have hm₀ : |m₀| ≤ C * A := abs_centered_exponentialMoment_le hf.continuous hfc hs (by norm_num)
  have hdp : |p - p₀| ≤ (C / 4) * (r - 1) * A := by
    have h := abs_centered_exponentialMoment_sub_le hf.continuous hfc hs hqabs
      (by norm_num : |(1 / 2 : ℝ)| ≤ 1 / 2)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqd (by positivity)) hA).trans_eq (by ring))
  have hdm : |m - m₀| ≤ (C / 4) * (r - 1) * A := by
    have h := abs_centered_exponentialMoment_sub_le hf.continuous hfc hs
      (q := -q) (q' := -(1 / 2)) (by simpa only [abs_neg] using hqabs) (by norm_num)
    rw [neg_sub_neg, abs_sub_comm (1 / 2 : ℝ) q] at h
    exact h.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqd (by positivity)) hA).trans_eq (by ring))
  have hprod : |p * m - p₀ * m₀| ≤ C ^ 2 / 2 * (r - 1) * A ^ 2 := by
    rw [show p * m - p₀ * m₀ = (p - p₀) * m + p₀ * (m - m₀) by ring]
    calc
      _ ≤ |p - p₀| * |m| + |p₀| * |m - m₀| := by
        simpa only [abs_mul] using abs_add_le ((p - p₀) * m) (p₀ * (m - m₀))
      _ ≤ ((C / 4) * (r - 1) * A) * (C * A) +
          (C * A) * ((C / 4) * (r - 1) * A) := add_le_add
        (mul_le_mul hdp hm (abs_nonneg _) (by positivity))
        (mul_le_mul hp₀ hdm (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hprod₀ : |p₀ * m₀| ≤ C ^ 2 * A ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hp₀ hm₀ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hinv0 : 0 ≤ 2 / r := div_nonneg (by norm_num) hr0.le
  have hinv2 : 2 / r ≤ 2 := (div_le_iff₀ hr0).mpr (by linarith only [hr])
  have hcoef : |2 / r - 2| ≤ 2 * (r - 1) := by
    rw [abs_of_nonpos (by linarith only [hinv2])]
    have hqr : (2 / r) * r = 2 := div_mul_cancel₀ _ hr0.ne'
    apply le_of_not_gt
    intro hbad
    have hmul := mul_lt_mul_of_pos_right hbad hr0
    nlinarith only [sq_nonneg (r - 1), hqr, hmul]
  have hscale : r * realPoleForm (fun u => f (r * u)) = 2 / r * p * m := by
    rw [realPoleForm, exponentialMoment_comp_mul f hr0,
      exponentialMoment_comp_mul f hr0]
    change r * (2 * (r⁻¹ * p) * (r⁻¹ * atomExponentialMoment f (-(1 / 2) / r))) = _
    rw [neg_div]
    change r * (2 * (r⁻¹ * p) * (r⁻¹ * m)) = _
    field_simp
  rw [hscale]
  change |2 / r * p * m - 2 * p₀ * m₀| ≤ _
  have hwhole : |2 / r * p * m - 2 * p₀ * m₀| ≤
      3 * C ^ 2 * (r - 1) * A ^ 2 := by
    rw [show 2 / r * p * m - 2 * p₀ * m₀ =
      (2 / r) * (p * m - p₀ * m₀) + (2 / r - 2) * (p₀ * m₀) by ring]
    calc
      _ ≤ |2 / r| * |p * m - p₀ * m₀| + |2 / r - 2| * |p₀ * m₀| := by
        simpa only [abs_mul] using abs_add_le ((2 / r) * (p * m - p₀ * m₀))
          ((2 / r - 2) * (p₀ * m₀))
      _ ≤ 2 * (C ^ 2 / 2 * (r - 1) * A ^ 2) +
          (2 * (r - 1)) * (C ^ 2 * A ^ 2) := add_le_add
        (mul_le_mul (by rwa [abs_of_nonneg hinv0]) hprod (abs_nonneg _) (by norm_num))
        (mul_le_mul hcoef hprod₀ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hmass : A ^ 2 ≤ ∫ u, f u ^ 2 := by
    simpa only [one_mul] using _root_.RHTower.SeparatedBump.sq_integral_abs_le
      hf (δ := 1) hs (by norm_num)
  have hC2 : C ^ 2 = Real.exp 2 := by
    dsimp only [C]
    rw [sq, ← Real.exp_add]
    norm_num
  rw [hC2] at hwhole
  have hE : (0 : ℝ) ≤ ∫ u : ℝ, f u ^ 2 := integral_nonneg fun u => sq_nonneg (f u)
  exact hwhole.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans
    (by nlinarith only [mul_nonneg (mul_nonneg (Real.exp_pos (2 : ℝ)).le hs0) hE]))

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.realPoleForm_dilation_bound
