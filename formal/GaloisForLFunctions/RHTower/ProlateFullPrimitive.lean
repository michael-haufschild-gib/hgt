import GaloisForLFunctions.RHTower.ProlateEndpointEnergy
import GaloisForLFunctions.RHTower.ProlateExactPrimitive

/-!
# The pole-uniform primitive across the whole compact range

The exterior estimate covers the range beyond the matching point and the energy bound covers the
endpoint interval.  The endpoint interval is only `9/(8c²)` wide and the normalized profile is at
most `2 sqrt c` there, so its contribution is `O(c^{-3/2})` — smaller than the exterior
contribution, not merely comparable.

Adding them gives the primitive over the whole compact range with one constant.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- The endpoint-interval contribution, bounded by the width times the sup. -/
theorem abs_integral_endpoint_interval_le {s c b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1)
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ 2 - 1) * DDR u + 2 * u * DR u
      - (s * c ^ 2 - c ^ 2 * u ^ 2) * R u = 0)
    (hb1 : 1 ≤ b) (hb2 : b ≤ dunsterEndpointCrossing c) :
    |∫ x in (1 : ℝ)..b, Real.sqrt c * R x| ≤ 2 * Real.sqrt c * (b - 1) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hc)
  have hpt : ∀ x ∈ Set.uIoc (1 : ℝ) b, ‖Real.sqrt c * R x‖ ≤ 2 * Real.sqrt c := by
    intro x hx
    rw [Set.uIoc_of_le hb1] at hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx.1
    have hx2 : x ≤ dunsterEndpointCrossing c := le_trans hx.2 hb2
    have h := abs_radialProlate_le_two_endpoint hs0 hs1 hc hR1 hR hDR hode hx1 hx2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hsc]
    nlinarith [h, hsc.le, abs_nonneg (R x)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - 1)] at h
  exact h

/-- **The pole-uniform primitive over the whole compact range.**  This is `(17)` for the exact
radial mode: the primitive of the normalized profile from the endpoint is `O(c^-1)`, uniformly in
the endpoint of integration. -/
theorem abs_integral_sqrt_mul_radialProlate_full_le
    {s c X : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1)
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ 2 - 1) * DDR u + 2 * u * DR u
      - (s * c ^ 2 - c ^ 2 * u ^ 2) * R u = 0)
    (hX1 : 1 ≤ X) (hX2 : X ≤ 2) :
    |∫ x in (1 : ℝ)..X, Real.sqrt c * R x|
      ≤ (9 / 4 + (8 * radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / 3
          + 2 * (648 * 64))) / c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have hsc1 : (1 : ℝ) ≤ Real.sqrt c := Real.one_le_sqrt.mpr (by linarith)
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hK : 0 ≤ radialProlateUniformTransferConstant := radialProlateUniformTransferConstant_nonneg
  have hC : 0 ≤ lgBesselCommonEnvelopeConstant := lgBesselCommonEnvelopeConstant_nonneg
  have hA1 : (1 : ℝ) < dunsterEndpointCrossing c := dunsterEndpointCrossing_gt_one hc0
  have hAsub : dunsterEndpointCrossing c - 1 = 9 / (8 * c ^ 2) := dunsterEndpointCrossing_sub_one
  set A : ℝ := dunsterEndpointCrossing c with hAdef
  have hRc : Continuous fun x : ℝ => Real.sqrt c * R x :=
    continuous_const.mul (continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt)
  -- the endpoint interval contributes at most `9/(4c)`
  have hendpoint : ∀ b : ℝ, 1 ≤ b → b ≤ A →
      |∫ x in (1 : ℝ)..b, Real.sqrt c * R x| ≤ 9 / (4 * c) := by
    intro b hb1 hb2
    have h := abs_integral_endpoint_interval_le hs0 hs1 hc hR1 hR hDR hode hb1 hb2
    have hwidth : b - 1 ≤ 9 / (8 * c ^ 2) := by linarith [hb2, hAsub]
    have hstep : 2 * Real.sqrt c * (b - 1) ≤ 2 * Real.sqrt c * (9 / (8 * c ^ 2)) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    have hval : 2 * Real.sqrt c * (9 / (8 * c ^ 2)) ≤ 9 / (4 * c) := by
      have he : 2 * Real.sqrt c * (9 / (8 * c ^ 2)) = 9 * Real.sqrt c / (4 * c ^ 2) := by
        field_simp
        ring
      rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
      have hscc : Real.sqrt c ≤ c := by nlinarith [hsc1, hss, hc0]
      nlinarith [hscc, hc0]
    linarith [h, hstep, hval]
  rcases le_or_gt X A with hXA | hXA
  · have h := hendpoint X hX1 hXA
    have hpos : (0 : ℝ) ≤ 8 * radialProlateUniformTransferConstant
        * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64) := by
      have : (0 : ℝ) ≤ 8 * radialProlateUniformTransferConstant
          * lgBesselCommonEnvelopeConstant / 3 := by positivity
      linarith
    have hmono : (9 : ℝ) / (4 * c) ≤ 9 / 4 / c := le_of_eq (by rw [div_div])
    have hsplitc : (9 / 4 + (8 * radialProlateUniformTransferConstant
        * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64))) / c
        = 9 / 4 / c + (8 * radialProlateUniformTransferConstant
          * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64)) / c := by
      field_simp
    rw [hsplitc]
    have hnn : (0 : ℝ) ≤ (8 * radialProlateUniformTransferConstant
        * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64)) / c := by positivity
    linarith [h, hmono, hnn]
  · have hint1 : IntervalIntegrable (fun x : ℝ => Real.sqrt c * R x) volume 1 A :=
      hRc.intervalIntegrable 1 A
    have hint2 : IntervalIntegrable (fun x : ℝ => Real.sqrt c * R x) volume A X :=
      hRc.intervalIntegrable A X
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have h1 := hendpoint A (le_of_lt hA1) le_rfl
    have h2 := abs_integral_sqrt_mul_radialProlate_le hs0 hs1 hc hR1 hR hDR hode
      (le_of_lt hXA) hX2
    have heq : (∫ x in (1 : ℝ)..X, Real.sqrt c * R x)
        = (∫ x in (1 : ℝ)..A, Real.sqrt c * R x) + ∫ x in A..X, Real.sqrt c * R x := by
      linarith [hsplit]
    rw [heq]
    refine le_trans (abs_add_le _ _) ?_
    have hmono : (9 : ℝ) / (4 * c) ≤ 9 / 4 / c := le_of_eq (by rw [div_div])
    have hsplitc : (9 / 4 + (8 * radialProlateUniformTransferConstant
        * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64))) / c
        = 9 / 4 / c + (8 * radialProlateUniformTransferConstant
          * lgBesselCommonEnvelopeConstant / 3 + 2 * (648 * 64)) / c := by
      field_simp
    rw [hsplitc]
    linarith [h1, h2, hmono]

end GaloisForLFunctions.RHTower
