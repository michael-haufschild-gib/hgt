/-
# q62 — Brolin build P2: uniform `L²` control of the finite Brolin potentials

Foundation for the uniform-integrability input of the Brolin equidistribution keystone
(`Q62BrolinEquidistribution.isRieszMeasureOfSmooth_gapAMu_of_greenApprox_integral_tendsto`).

The finite potential is `gₙ(z) = (2ⁿ)⁻¹ Σ_{r ∈ roots} log‖z − r‖`, the roots all in the escape disk
`closedBall 0 R`.  Vitali needs `{gₙ}` uniformly integrable on any ball `B`, which follows from a
**uniform `L²` bound** `‖gₙ‖_{L²(B)} ≤ C_B`.  Route:

* **`logsq_le_const_div` (this file, PROVEN).**  The pointwise `L²`-kernel domination
  `(log t)² ≤ C · t⁻¹` on `(0, S]` (`C = max 4 (S (log S)²)`), the exponent `−1 > −2 = −dim` that
  makes the log-kernel square Lebesgue-integrable on a planar ball.  Near `0` the bound comes from
  `Real.log_le_sub_one_of_pos` at `t^{−1/2}` (`−log t ≤ 2 t^{−1/2}`); on `[1, S]` from monotonicity.
* **single-kernel integrability** (next): `IntegrableOn (fun z => (log‖z − r‖)²) (ball 0 S)` via
  `integrableOn_ball_of_norm_le_rpow` (mathlib, `finrank ℝ ℂ = 2`) fed by `logsq_le_const_div`;
  translation-invariance (`z ↦ z − r`, `ball(−r,S) ⊆ ball(0,S+R)`) makes the `L²` bound uniform in
  `r` with the *single* constant `∫_{ball 0 (S+R)} (log‖u‖)²`.
* **multiset Minkowski**: `eLpNorm ((s.map g).sum) 2 ≤ (s.map (eLpNorm ∘ g)).sum` by `eLpNorm_add_le`
  induction; with `card roots = 2ⁿ` and the `(2ⁿ)⁻¹` normalisation gives `‖gₙ‖_{L²(B)} ≤ C_B`.
* **`L²`-bound ⟹ `UniformIntegrable _ 1`**: `uniformIntegrable_of` fed by Chebyshev
  (`∫_{|gₙ|≥C}|gₙ| ≤ ‖gₙ‖₂² / C`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory Metric Set

namespace Bottcher

/-- **`L²`-kernel domination.**  `(log t)² ≤ (max 4 (S (log S)²)) · t⁻¹` for `0 < t ≤ S`, `1 ≤ S`.
The decay exponent `−1` (`> −2 = −dim ℝ ℂ`) is what makes `(log‖· − r‖)²` Lebesgue-integrable on a
planar ball.  Near `0`: `Real.log_le_sub_one_of_pos` at `t^{−1/2}` gives `−log t ≤ 2 t^{−1/2}`, hence
`(log t)² ≤ 4 t⁻¹`.  On `[1, S]`: `(log t)² ≤ (log S)² ≤ S (log S)² · t⁻¹`. -/
theorem logsq_le_const_div {S : ℝ} (hS : 1 ≤ S) {t : ℝ} (ht : 0 < t) (htS : t ≤ S) :
    (Real.log t) ^ 2 ≤ (max 4 (S * (Real.log S) ^ 2)) * t⁻¹ := by
  rcases le_total t 1 with ht1 | ht1
  · have hs : 0 < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos ht _
    have h := Real.log_le_sub_one_of_pos hs
    rw [Real.log_rpow ht] at h
    have hlogneg : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    have hnl : -Real.log t ≤ 2 * t ^ (-(1 : ℝ) / 2) := by nlinarith [h]
    have hnl0 : 0 ≤ -Real.log t := by linarith
    have hsq : (-Real.log t) ^ 2 ≤ (2 * t ^ (-(1 : ℝ) / 2)) ^ 2 := by
      apply sq_le_sq' <;> nlinarith [hnl, hnl0, Real.rpow_pos_of_pos ht (-(1 : ℝ) / 2)]
    have hrw : (2 * t ^ (-(1 : ℝ) / 2)) ^ 2 = 4 * t⁻¹ := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul ht.le]
      norm_num; rw [Real.rpow_neg_one]
    have h4 : (Real.log t) ^ 2 ≤ 4 * t⁻¹ := by
      calc (Real.log t) ^ 2 = (-Real.log t) ^ 2 := by ring
        _ ≤ (2 * t ^ (-(1 : ℝ) / 2)) ^ 2 := hsq
        _ = 4 * t⁻¹ := hrw
    have hmax : (4 : ℝ) ≤ max 4 (S * (Real.log S) ^ 2) := le_max_left _ _
    have htpos : 0 < t⁻¹ := by positivity
    nlinarith [h4, hmax, htpos]
  · have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlogS : Real.log t ≤ Real.log S := Real.log_le_log ht htS
    have hsqle : (Real.log t) ^ 2 ≤ (Real.log S) ^ 2 := by
      nlinarith [hlogt, hlogS, Real.log_nonneg hS]
    have htinv : S⁻¹ ≤ t⁻¹ := inv_anti₀ ht htS
    have hSlog : (Real.log S) ^ 2 ≤ (S * (Real.log S) ^ 2) * t⁻¹ := by
      have hge : (S * (Real.log S) ^ 2) * t⁻¹ ≥ (S * (Real.log S) ^ 2) * S⁻¹ := by
        apply mul_le_mul_of_nonneg_left htinv; positivity
      have hcancel : (S * (Real.log S) ^ 2) * S⁻¹ = (Real.log S) ^ 2 := by field_simp
      linarith [hge, hcancel.ge]
    have hmax : S * (Real.log S) ^ 2 ≤ max 4 (S * (Real.log S) ^ 2) := le_max_right _ _
    have htpos : 0 < t⁻¹ := by positivity
    nlinarith [hsqle, hSlog, hmax, htpos]

end Bottcher
