import GaloisForLFunctions.HTGeometry.InverseSqrtEndpointIntegral
import GaloisForLFunctions.RHTower.CCM.CCMFirstRowStationaryPhase

/-!
# The endpoint expansion of the Liouville–Green phase

The exterior phase is the integral of a smooth factor against the endpoint weight `(t-1)^{-1/2}`:

`xi_s(x) = int_1^x g_s(t) (t-1)^{-1/2} dt`,   `g_s(t) = sqrt(t²-s)/sqrt(t+1)`.

The weight integrates to `2 sqrt(x-1)`, so the leading behaviour is `2 g_s(1) sqrt(x-1)`, and the
error is controlled by the modulus of continuity of `g_s`.  That modulus is Lipschitz, because the
*square* of `g_s` is a rational function vanishing to first order at the endpoint and `g_s` is
bounded below there.

This is the second-order endpoint control that a bounded-factor bracket cannot supply.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- The smooth factor of the phase speed at the endpoint. -/
def xiEndpointFactor (s t : ℝ) : ℝ := Real.sqrt (t ^ 2 - s) / Real.sqrt (t + 1)

theorem xiEndpointFactor_one {s : ℝ} : xiEndpointFactor s 1 = Real.sqrt (1 - s) / Real.sqrt 2 := by
  rw [xiEndpointFactor]
  norm_num

/-- The phase speed factorises into a smooth factor and the endpoint weight. -/
theorem xiSpeed_eq_factor_div {s t : ℝ} (hs : s ≤ 1) (ht : 1 < t) :
    xiSpeed s t = xiEndpointFactor s t / Real.sqrt (t - 1) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h1 : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hfac : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
  have hm1 : (0 : ℝ) < t - 1 := by linarith
  have hp1 : (0 : ℝ) < t + 1 := by linarith
  have hts : (0 : ℝ) ≤ t ^ 2 - s := by nlinarith [h1, hs]
  rw [xiSpeed, Real.sqrt_div hts (t ^ 2 - 1), hfac, Real.sqrt_mul hm1.le, xiEndpointFactor]
  field_simp

/-- The smooth factor is Lipschitz at the endpoint, with an absolute constant. -/
theorem abs_xiEndpointFactor_sub_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (ht1 : 1 ≤ t) :
    |xiEndpointFactor s t - xiEndpointFactor s 1| ≤ 3 * (t - 1) := by
  have hp1 : (0 : ℝ) < t + 1 := by linarith
  have hts : (0 : ℝ) < t ^ 2 - s := by nlinarith
  set A : ℝ := xiEndpointFactor s t with hAdef
  set B : ℝ := xiEndpointFactor s 1 with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef, xiEndpointFactor]
    positivity
  have hA2 : A ^ 2 = (t ^ 2 - s) / (t + 1) := by
    rw [hAdef, xiEndpointFactor, div_pow, Real.sq_sqrt hts.le, Real.sq_sqrt hp1.le]
  have hB2 : B ^ 2 = (1 - s) / 2 := by
    rw [hBdef, xiEndpointFactor_one, div_pow, Real.sq_sqrt (by linarith),
      Real.sq_sqrt (by norm_num)]
  have hB : (1 : ℝ) / 2 ≤ B := by
    rw [hBdef, xiEndpointFactor_one]
    rw [le_div_iff₀ (by positivity)]
    have hhalf : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
    have hnn : (0 : ℝ) ≤ 1 / 2 * Real.sqrt 2 := by positivity
    have hsq : (1 / 2 * Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hval : Real.sqrt (1 / 2) = 1 / 2 * Real.sqrt 2 := by
      have h := Real.sqrt_sq hnn
      rwa [hsq] at h
    linarith [hhalf, hval.symm.le, hval.le]
  have hdiff : A ^ 2 - B ^ 2 = (t - 1) * (2 * t + 1 + s) / (2 * (t + 1)) := by
    rw [hA2, hB2]
    field_simp
    ring
  have hupper : A ^ 2 - B ^ 2 ≤ 3 / 2 * (t - 1) := by
    rw [hdiff, div_le_iff₀ (by positivity)]
    nlinarith [ht1, hs1, hs0]
  have hlower : -(3 / 2 * (t - 1)) ≤ A ^ 2 - B ^ 2 := by
    rw [hdiff, neg_le, ← neg_div, div_le_iff₀ (by positivity)]
    nlinarith [ht1, hs1, hs0]
  rw [abs_le]
  constructor
  · nlinarith [hlower, hA0, hB, ht1]
  · nlinarith [hupper, hA0, hB, ht1]

/-- The endpoint weight in square-root form. -/
theorem integral_inv_sqrt_sub_one {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, (Real.sqrt (t - 1))⁻¹) = 2 * Real.sqrt (x - 1) := by
  rw [← GaloisForLFunctions.HTGeometry.integral_rpow_neg_half_sub_one hx]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hx] at ht
  exact (GaloisForLFunctions.HTGeometry.rpow_neg_half_eq_inv_sqrt (by linarith [ht.1])).symm

theorem intervalIntegrable_inv_sqrt_sub_one {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Real.sqrt (t - 1))⁻¹) volume 1 x := by
  have hbase : IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 : ℝ) / 2)) volume 1 x := by
    have h0 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 (x - 1) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h := h0.comp_sub_right 1
    simpa using h
  refine hbase.congr ?_
  intro t ht
  rw [Set.uIoc_of_le hx] at ht
  exact GaloisForLFunctions.HTGeometry.rpow_neg_half_eq_inv_sqrt (by linarith [ht.1])

/-- The complementary endpoint integral. -/
theorem integral_sqrt_sub_one {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, Real.sqrt (t - 1)) = 2 / 3 * ((x - 1) * Real.sqrt (x - 1)) := by
  have hcont : ContinuousOn (fun u : ℝ => 2 / 3 * ((u - 1) * Real.sqrt (u - 1))) (Icc 1 x) := by
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => Real.sqrt (t - 1)) volume 1 x :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
      HasDerivWithinAt (fun u : ℝ => 2 / 3 * ((u - 1) * Real.sqrt (u - 1)))
        (Real.sqrt (t - 1)) (Ioi t) t := by
    intro t ht
    have hpos : (0 : ℝ) < t - 1 := by linarith [ht.1]
    have hne : t - 1 ≠ 0 := ne_of_gt hpos
    have hs : 0 < Real.sqrt (t - 1) := Real.sqrt_pos.mpr hpos
    have hinner : HasDerivAt (fun u : ℝ => u - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hsq : HasDerivAt (fun u : ℝ => Real.sqrt (u - 1))
        (1 / (2 * Real.sqrt (t - 1)) * 1) t := (Real.hasDerivAt_sqrt hne).comp t hinner
    have hprod := hinner.mul hsq
    have h := hprod.const_mul (2 / 3 : ℝ)
    have hval : (2 : ℝ) / 3 * (1 * Real.sqrt (t - 1) + (t - 1) * (1 / (2 * Real.sqrt (t - 1)) * 1))
        = Real.sqrt (t - 1) := by
      have hss : Real.sqrt (t - 1) * Real.sqrt (t - 1) = t - 1 := Real.mul_self_sqrt hpos.le
      field_simp
      linarith [hss]
    rw [hval] at h
    exact h.hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv hint
  simpa using h

/-- **The endpoint expansion.**  The phase equals its leading square-root term up to an error of
order `(x-1)^{3/2}`, with an absolute constant.  This is the second-order endpoint control that a
bounded-factor bracket cannot give. -/
theorem abs_xiEndpointPhase_sub_leading_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 ≤ x) :
    |xiEndpointPhase s x - 2 * xiEndpointFactor s 1 * Real.sqrt (x - 1)|
      ≤ 2 * ((x - 1) * Real.sqrt (x - 1)) := by
  have hint1 : IntervalIntegrable (xiSpeed s) volume 1 x := intervalIntegrable_xiSpeed hs0 hx
  have hint2 : IntervalIntegrable
      (fun t : ℝ => xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹) volume 1 x :=
    (intervalIntegrable_inv_sqrt_sub_one hx).const_mul _
  have hsplit : xiEndpointPhase s x - 2 * xiEndpointFactor s 1 * Real.sqrt (x - 1)
      = ∫ t in (1 : ℝ)..x, (xiSpeed s t - xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹) := by
    rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
      integral_inv_sqrt_sub_one hx, xiEndpointPhase]
    ring
  rw [hsplit]
  have hpt : ∀ t ∈ Icc (1 : ℝ) x,
      |xiSpeed s t - xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹| ≤ 3 * Real.sqrt (t - 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      norm_num [xiSpeed]
    · have hpos : (0 : ℝ) < t - 1 := by linarith
      have hs : 0 < Real.sqrt (t - 1) := Real.sqrt_pos.mpr hpos
      rw [xiSpeed_eq_factor_div (by linarith) h]
      have hcomb : xiEndpointFactor s t / Real.sqrt (t - 1)
          - xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹
          = (xiEndpointFactor s t - xiEndpointFactor s 1) / Real.sqrt (t - 1) := by
        field_simp
      rw [hcomb, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      have hlip := abs_xiEndpointFactor_sub_le hs0 hs1 ht.1
      have hval : 3 * Real.sqrt (t - 1) * Real.sqrt (t - 1) = 3 * (t - 1) := by
        rw [mul_assoc, Real.mul_self_sqrt hpos.le]
      linarith [hlip, hval]
  have hmono : (∫ t in (1 : ℝ)..x,
        |xiSpeed s t - xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹|)
      ≤ ∫ t in (1 : ℝ)..x, 3 * Real.sqrt (t - 1) :=
    intervalIntegral.integral_mono_on hx (hint1.sub hint2).abs
      (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
  rw [intervalIntegral.integral_const_mul, integral_sqrt_sub_one hx] at hmono
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f :=
    fun t : ℝ => xiSpeed s t - xiEndpointFactor s 1 * (Real.sqrt (t - 1))⁻¹) hx
  linarith [habs, hmono]


end GaloisForLFunctions.RHTower
