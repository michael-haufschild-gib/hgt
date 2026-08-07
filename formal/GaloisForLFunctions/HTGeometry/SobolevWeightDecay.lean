import Mathlib

/-!
# Fractional Sobolev membership from Fourier decay of order one

A transform that is bounded and decays like `1/|ξ|` is square integrable against the weight
`(1 + ξ²)^s` exactly when `s < 1/2`.  The two bounds combine into the single majorant

`‖F ξ‖² ≤ (2M² + 2K²)/(1 + ξ²)`,

after which the weighted integrand is dominated by `(1 + ξ²)^{s-1}`, integrable on the line
precisely for `s < 1/2`.

This is the criterion a compactly supported bounded-variation profile meets: its transform is
bounded by the `L¹` norm and, after one integration by parts against the Stieltjes measure, by the
total variation over `2π|ξ|`.  The criterion is stated for the transform alone, so it applies to any
source supplying those two bounds.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Square integrability of a transform against the fractional Sobolev weight. -/
def MemSobolevWeight (s : ℝ) (F : ℝ → ℂ) : Prop :=
  Integrable fun ξ : ℝ => (1 + ξ ^ 2) ^ s * ‖F ξ‖ ^ 2

/-- **Two bounds give one majorant.**  A transform bounded by `M` everywhere and by `K/|ξ|` away
from the origin obeys `‖F ξ‖² ≤ (2M² + 2K²)/(1 + ξ²)`. -/
theorem normSq_le_of_bounded_of_decay {F : ℝ → ℂ} {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hbdd : ∀ ξ : ℝ, ‖F ξ‖ ≤ M) (hdec : ∀ ξ : ℝ, 1 ≤ |ξ| → ‖F ξ‖ * |ξ| ≤ K) (ξ : ℝ) :
    ‖F ξ‖ ^ 2 ≤ (2 * M ^ 2 + 2 * K ^ 2) / (1 + ξ ^ 2) := by
  have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_or_gt |ξ| 1 with hsmall | hbig
  · have hsq : ξ ^ 2 ≤ 1 := by
      have := abs_nonneg ξ
      nlinarith [sq_abs ξ]
    have hF := hbdd ξ
    have hF0 : 0 ≤ ‖F ξ‖ := norm_nonneg _
    nlinarith [sq_nonneg K, sq_nonneg M, sq_nonneg (‖F ξ‖)]
  · have habs : (1 : ℝ) ≤ |ξ| := le_of_lt hbig
    have hd := hdec ξ habs
    have hF0 : 0 ≤ ‖F ξ‖ := norm_nonneg _
    have hxi : (1 : ℝ) ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hprod : 0 ≤ ‖F ξ‖ * |ξ| := mul_nonneg hF0 (abs_nonneg ξ)
    have hsq : ‖F ξ‖ ^ 2 * ξ ^ 2 ≤ K ^ 2 := by
      have h1 : (‖F ξ‖ * |ξ|) ^ 2 ≤ K ^ 2 := by nlinarith [hprod, hd, hK]
      nlinarith [sq_abs ξ, h1]
    nlinarith [sq_nonneg M, hsq]

/-- The Sobolev weight against an order-one decay is integrable exactly below one half. -/
theorem integrable_sobolevWeight_decay {s : ℝ} (hs : s < 1 / 2) (C : ℝ) :
    Integrable fun ξ : ℝ => C * (1 + ξ ^ 2) ^ (s - 1) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 - 2 * s := by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hbase := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) hr
  have hcongr : (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(2 - 2 * s) / 2)) =
      fun ξ : ℝ => (1 + ξ ^ 2) ^ (s - 1) := by
    funext ξ
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [hcongr] at hbase
  exact hbase.const_mul C

/-- **Fractional Sobolev membership from decay.**  A measurable transform that is bounded and
decays at order one lies in every Sobolev weight below one half. -/
theorem memSobolevWeight_of_decay {s M K : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hM : 0 ≤ M) (hK : 0 ≤ K) {F : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable F volume)
    (hbdd : ∀ ξ : ℝ, ‖F ξ‖ ≤ M) (hdec : ∀ ξ : ℝ, 1 ≤ |ξ| → ‖F ξ‖ * |ξ| ≤ K) :
    MemSobolevWeight s F := by
  have hmajor := integrable_sobolevWeight_decay hs (2 * M ^ 2 + 2 * K ^ 2)
  have hmeas' : AEStronglyMeasurable (fun ξ : ℝ => (1 + ξ ^ 2) ^ s * ‖F ξ‖ ^ 2) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact (hmeas.norm.pow 2)
  refine Integrable.mono' hmajor hmeas' ?_
  filter_upwards with ξ
  have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  have hbound := normSq_le_of_bounded_of_decay hM hK hbdd hdec ξ
  have hw : (0 : ℝ) < (1 + ξ ^ 2) ^ s := Real.rpow_pos_of_pos hpos s
  have hnn : 0 ≤ (1 + ξ ^ 2) ^ s * ‖F ξ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hsplit : (1 + ξ ^ 2) ^ (s - 1) = (1 + ξ ^ 2) ^ s / (1 + ξ ^ 2) := by
    rw [Real.rpow_sub hpos, Real.rpow_one]
  rw [hsplit]
  calc (1 + ξ ^ 2) ^ s * ‖F ξ‖ ^ 2
      ≤ (1 + ξ ^ 2) ^ s * ((2 * M ^ 2 + 2 * K ^ 2) / (1 + ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound hw.le
    _ = (2 * M ^ 2 + 2 * K ^ 2) * ((1 + ξ ^ 2) ^ s / (1 + ξ ^ 2)) := by ring

end GaloisForLFunctions.HTGeometry
