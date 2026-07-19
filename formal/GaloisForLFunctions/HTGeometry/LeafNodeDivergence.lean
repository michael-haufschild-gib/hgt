import GaloisForLFunctions.HTGeometry.BoundedNodesDeterminate

/-!
# From two representatives of `s` to unbounded nodes

The node statements are phrased for the normalised sequence `k ↦ s_k / s₀`, while a representing
measure in the project's sense integrates `xᵏ` to `s_k` exactly.  Scaling by `(s₀)⁻¹` converts
one to
the other, and scaling by a nonzero finite constant is injective, so two distinct representatives of
`s` stay distinct after normalisation.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Scaling by a nonzero finite constant is injective on measures. -/
theorem smul_measure_ne {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) {nu1 nu2 : Measure ℝ}
    (hne : nu1 ≠ nu2) : c • nu1 ≠ c • nu2 := by
  intro heq
  refine hne ?_
  have hcong := congrArg (fun m : Measure ℝ => c⁻¹ • m) heq
  simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hct] using hcong

/-- The normalisation of a representing measure has the normalised moments. -/
theorem integral_pow_smul_normalise (h : PositiveMomentForm s) {nu : Measure ℝ}
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu) (k : ℕ) :
    (s 0)⁻¹ * s k = ∫ x, (x : ℝ) ^ k ∂((ENNReal.ofReal (s 0))⁻¹ • nu) := by
  rw [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (moment_zero_pos h).le, smul_eq_mul, (hnu k).2]

theorem integrable_pow_smul_normalise (h : PositiveMomentForm s) {nu : Measure ℝ}
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu) (k : ℕ) :
    Integrable (fun x : ℝ => (x : ℝ) ^ k) ((ENNReal.ofReal (s 0))⁻¹ • nu) := by
  refine ((hnu k).1).smul_measure (ENNReal.inv_ne_top.mpr ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact moment_zero_pos h

/-- **Two distinct representatives of `s` force a node outside any interval.** -/
theorem exists_node_outside_of_hasMoments_ne (h : PositiveMomentForm s) {B : ℝ} (hB : 0 < B)
    {nu1 nu2 : Measure ℝ} [IsFiniteMeasure nu1] [IsFiniteMeasure nu2]
    (h1 : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu1)
    (h2 : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu2)
    (hne : nu1 ≠ nu2) :
    ∃ n : ℕ, ∃ xi ∈ gaussNodes s n, xi ∉ Set.Icc (-B) B := by
  have hc0 : (ENNReal.ofReal (s 0))⁻¹ ≠ 0 := by
    simp [ENNReal.inv_eq_zero]
  have hct : (ENNReal.ofReal (s 0))⁻¹ ≠ ⊤ := by
    refine ENNReal.inv_ne_top.mpr ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact moment_zero_pos h
  haveI : IsFiniteMeasure ((ENNReal.ofReal (s 0))⁻¹ • nu1) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top (measure_lt_top _ _)
  haveI : IsFiniteMeasure ((ENNReal.ofReal (s 0))⁻¹ • nu2) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top (measure_lt_top _ _)
  exact exists_node_outside_of_measure_ne h hB
    (integral_pow_smul_normalise h h1) (integrable_pow_smul_normalise h h1)
    (integral_pow_smul_normalise h h2) (integrable_pow_smul_normalise h h2)
    (smul_measure_ne hc0 hct hne)

end HTGeometry
