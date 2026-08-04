import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The characteristic of a power series against its majorant

The Nevanlinna characteristic of an entire power series is bounded by the positive logarithm of the
majorant `S(r) = ∑ |a_n| r^n`, and hence by the maximum term times the central index.  This is the
bridge between value-distribution growth and the Wiman--Valiron quantities: a statement about
`T(r, f)` becomes a statement about `mu(r)` and `nu(r)`.
-/

open MeasureTheory Real Complex Metric

namespace GaloisForLFunctions.Nevanlinna

open GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The sum of a power series with everywhere-convergent coefficients is entire. -/
theorem analyticOnNhd_coeffFun (ha : EntireCoeffs a) :
    AnalyticOnNhd ℂ (coeffFun a) Set.univ :=
  ((differentiable_coeffFun ha).differentiableOn).analyticOnNhd isOpen_univ

/-- **The characteristic is below the positive logarithm of the majorant.** -/
theorem characteristic_coeffFun_le_posLog_coeffSum (ha : EntireCoeffs a) {r : ℝ} (hr : r ≠ 0) :
    ValueDistribution.characteristic (coeffFun a) ⊤ r ≤ Real.posLog (coeffSum a |r|) := by
  refine characteristic_top_le_posLog_of_bound (analyticOnNhd_coeffFun ha) ?_
  intro z hz
  have hznorm : ‖z‖ = |r| := by
    simpa using hz
  have hpos : 0 < ‖z‖ := by
    rw [hznorm]
    exact abs_pos.mpr hr
  have h := norm_coeffFun_le ha hpos
  rwa [hznorm] at h

/-- **The characteristic against the maximum term and the central index.**  Composing the majorant
bound with the corpus estimate `S(r) <= mu(r) (nu(s) + 1 + (r/s)/(1 - r/s))` expresses Nevanlinna
growth entirely in Wiman--Valiron quantities. -/
theorem characteristic_coeffFun_le_posLog_maxTerm_mul (ha : EntireCoeffs a) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ValueDistribution.characteristic (coeffFun a) ⊤ r
      ≤ Real.posLog (maxTerm a r
          * (((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s))) := by
  have habs : |r| = r := abs_of_pos hr
  have hbase := characteristic_coeffFun_le_posLog_coeffSum ha (ne_of_gt hr)
  rw [habs] at hbase
  refine le_trans hbase ?_
  refine Real.posLog_le_posLog ?_ (coeffSum_le_maxTerm_mul_centralIndex ha hr hrs hn₀)
  exact tsum_nonneg fun n => term_nonneg a hr n

/-- **The characteristic splits additively into the two Wiman--Valiron quantities.**  Applying
submultiplicativity of `log⁺` to the previous bound separates the maximum term from the central
index. -/
theorem characteristic_coeffFun_le_posLog_add (ha : EntireCoeffs a) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ValueDistribution.characteristic (coeffFun a) ⊤ r
      ≤ Real.posLog (maxTerm a r)
        + Real.posLog (((centralIndex a s : ℝ) + 1) + (r / s) / (1 - r / s)) :=
  le_trans (characteristic_coeffFun_le_posLog_maxTerm_mul ha hn₀ hr hrs) Real.posLog_mul

end GaloisForLFunctions.Nevanlinna
