import Mathlib

/-!
# The exponential integral `E₁`

`E₁(c) = ∫_c^∞ e^{-u} du / u` for `c > 0`.  This is the profile appearing in the critical
prime-aperture law of `mobius-prime-aperture-differential-order-profile.md`, equation `(7)`.

The module records the facts the aperture law needs:

* integrability of `e^{-u}/u` and of `e^{-u} log(u/c)` on `(c, ∞)`;
* the logarithmic representation `∫_c^∞ e^{-u} log(u/c) du = E₁(c)`, obtained by one
  integration by parts on the half line.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace RHTower

/-- The exponential integral `E₁(c) = ∫_c^∞ e^{-u}/u du`. -/
def expIntegralOne (c : ℝ) : ℝ := ∫ u in Ioi c, Real.exp (-u) / u

/-! ### Elementary exponential bounds -/

theorem self_mul_exp_neg_le {u : ℝ} (_hu : 0 < u) :
    u * Real.exp (-u) ≤ 2 * Real.exp (-(1 / 2) * u) := by
  have hexp : u / 2 < Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have hpos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have hstep : u * Real.exp (-(u / 2)) ≤ 2 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ hpos]
    linarith
  have hsplit : Real.exp (-u) = Real.exp (-(u / 2)) * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrw : -(1 / 2 : ℝ) * u = -(u / 2) := by ring
  rw [hrw, hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le

theorem log_div_le_self {c u : ℝ} (hc : 0 < c) (hu : c ≤ u) :
    Real.log (u / c) ≤ u / c := by
  have hpos : 0 < u / c := div_pos (lt_of_lt_of_le hc hu) hc
  have := Real.log_le_sub_one_of_pos hpos
  linarith

theorem log_div_nonneg' {c u : ℝ} (hc : 0 < c) (hu : c ≤ u) :
    0 ≤ Real.log (u / c) := by
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hc]
  linarith

/-! ### Integrability -/

theorem integrableOn_exp_neg_div_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi c) volume := by
  have hbase : IntegrableOn (fun u : ℝ => c⁻¹ * Real.exp (-1 * u)) (Ioi c) volume :=
    (exp_neg_integrableOn_Ioi c one_pos).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-u) / u).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : 0 < u := lt_trans hc hu
    have hexp : 0 < Real.exp (-u) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show (-1 : ℝ) * u = -u by ring, div_le_iff₀ hupos]
    have hcu : c ≤ u := hu.le
    have hinv : 1 ≤ c⁻¹ * u := by
      rw [inv_mul_eq_div, le_div_iff₀ hc]
      linarith
    nlinarith [hexp]

theorem integrableOn_self_mul_exp_neg_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Ioi c) volume := by
  have hbase : IntegrableOn (fun u : ℝ => (2 : ℝ) * Real.exp (-(1 / 2) * u)) (Ioi c) volume :=
    (exp_neg_integrableOn_Ioi c (by norm_num)).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · exact (by fun_prop : Measurable fun u : ℝ => u * Real.exp (-u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := c))] with u hu
    have hupos : 0 < u := lt_trans hc hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact self_mul_exp_neg_le hupos

theorem integrableOn_exp_neg_mul_log_div_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log (u / c)) (Ioi c) volume := by
  have hbase : IntegrableOn (fun u : ℝ => c⁻¹ * (u * Real.exp (-u))) (Ioi c) volume :=
    (integrableOn_self_mul_exp_neg_Ioi hc).const_mul _
  refine Integrable.mono' hbase ?_ ?_
  · exact (by fun_prop :
      Measurable fun u : ℝ => Real.exp (-u) * Real.log (u / c)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : 0 < u := lt_trans hc hu
    have hlog0 : 0 ≤ Real.log (u / c) := log_div_nonneg' hc hu.le
    have hlogle : Real.log (u / c) ≤ u / c := log_div_le_self hc hu.le
    have hexp : 0 < Real.exp (-u) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-u) * Real.log (u / c) ≤ Real.exp (-u) * (u / c) :=
          mul_le_mul_of_nonneg_left hlogle hexp.le
      _ = c⁻¹ * (u * Real.exp (-u)) := by field_simp

/-! ### The logarithmic representation -/

/-- One integration by parts on the half line turns the logarithmic profile into `E₁`. -/
theorem integral_exp_neg_mul_log_div_Ioi {c : ℝ} (hc : 0 < c) :
    (∫ u in Ioi c, Real.exp (-u) * Real.log (u / c)) = expIntegralOne c := by
  have hderiv : ∀ u ∈ Ioi c,
      HasDerivAt (fun v : ℝ => -(Real.exp (-v) * Real.log (v / c)))
        (Real.exp (-u) * Real.log (u / c) - Real.exp (-u) / u) u := by
    intro u hu
    have hupos : 0 < u := lt_trans hc hu
    have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-u)) u := by
      have := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
      simpa [Function.comp_def] using this
    have hdiv : HasDerivAt (fun v : ℝ => v / c) (1 / c) u := by
      simpa using (hasDerivAt_id u).div_const c
    have h2 : HasDerivAt (fun v : ℝ => Real.log (v / c)) (1 / u) u := by
      have hne : u / c ≠ 0 := by positivity
      have hlog := (Real.hasDerivAt_log hne).comp u hdiv
      have hval : (u / c)⁻¹ * (1 / c) = 1 / u := by field_simp
      rw [Function.comp_def] at hlog
      rwa [hval] at hlog
    have hmul := (h1.mul h2).neg
    have hcalc : -(-Real.exp (-u) * Real.log (u / c) + Real.exp (-u) * (1 / u))
        = Real.exp (-u) * Real.log (u / c) - Real.exp (-u) / u := by
      field_simp
      ring
    rw [← hcalc]
    exact hmul
  have hcont : ContinuousWithinAt (fun v : ℝ => -(Real.exp (-v) * Real.log (v / c))) (Ici c) c := by
    have h1 : ContinuousAt (fun v : ℝ => Real.exp (-v)) c := by fun_prop
    have hdivne : c / c ≠ 0 := by
      rw [div_self (ne_of_gt hc)]
      norm_num
    have hinner : ContinuousAt (fun v : ℝ => v / c) c := by fun_prop
    have h2 : ContinuousAt (fun v : ℝ => Real.log (v / c)) c := by
      have hcomp := ContinuousAt.comp (g := Real.log) (f := fun v : ℝ => v / c)
        (Real.continuousAt_log hdivne) hinner
      simpa [Function.comp_def] using hcomp
    exact ((h1.mul h2).neg).continuousWithinAt
  have hint : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * Real.log (u / c) - Real.exp (-u) / u) (Ioi c) volume :=
    (integrableOn_exp_neg_mul_log_div_Ioi hc).sub (integrableOn_exp_neg_div_Ioi hc)
  have hlim : Tendsto (fun v : ℝ => -(Real.exp (-v) * Real.log (v / c))) atTop (nhds 0) := by
    have hbound : ∀ᶠ u : ℝ in atTop,
        ‖-(Real.exp (-u) * Real.log (u / c))‖ ≤ c⁻¹ * (u * Real.exp (-u)) := by
      filter_upwards [eventually_ge_atTop c] with u hu
      have hupos : 0 < u := lt_of_lt_of_le hc hu
      have hlog0 : 0 ≤ Real.log (u / c) := log_div_nonneg' hc hu
      have hlogle : Real.log (u / c) ≤ u / c := log_div_le_self hc hu
      have hexp : 0 < Real.exp (-u) := Real.exp_pos _
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (-u) * Real.log (u / c) ≤ Real.exp (-u) * (u / c) :=
            mul_le_mul_of_nonneg_left hlogle hexp.le
        _ = c⁻¹ * (u * Real.exp (-u)) := by field_simp
    refine squeeze_zero_norm' hbound ?_
    have hmain : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simpa using hmain.const_mul c⁻¹
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hFc : -(Real.exp (-c) * Real.log (c / c)) = 0 := by
    rw [div_self (ne_of_gt hc), Real.log_one, mul_zero, neg_zero]
  rw [hFc, sub_zero,
    integral_sub (integrableOn_exp_neg_mul_log_div_Ioi hc) (integrableOn_exp_neg_div_Ioi hc)]
    at hmain
  rw [expIntegralOne]
  linarith

end RHTower
