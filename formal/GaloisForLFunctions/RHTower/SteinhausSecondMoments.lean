import GaloisForLFunctions.RHTower.SteinhausRateStrictMono

/-!
# The two second moments of the model

`∫ proj² dHaar = 1/2` (the variance of the circle projection) and
`∫₀¹ w_α² = (1−α)²/(1−2α)` for `α < 1/2`.  These are the constants of the sub-critical regime of
the card's trichotomy.
-/

open MeasureTheory Set

namespace HTGeometry

local instance phaseCirclePositiveMoments : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- **The variance of the circle projection is `1/2`.** -/
theorem integral_steinhausProjection_sq :
    (∫ x : PhaseCircle, steinhausProjection x ^ 2 ∂AddCircle.haarAddCircle) = 1 / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [integral_haar_eq_intervalIntegral]
  have hcongr : (∫ t in (0 : ℝ)..(2 * Real.pi), steinhausProjection ((t : ℝ) : PhaseCircle) ^ 2)
      = ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos t ^ 2 :=
    intervalIntegral.integral_congr fun t _ => by rw [steinhausProjection_coe]
  rw [hcongr, integral_cos_sq]
  simp
  field_simp

/-- **The second moment of the profile**, finite exactly below the critical index. -/
theorem integral_weightProfile_sq {α : ℝ} (hα : α < 1 / 2) :
    (∫ v in (0 : ℝ)..1, weightProfile α v ^ 2) = (1 - α) ^ 2 / (1 - 2 * α) := by
  have hne : (1 : ℝ) - 2 * α ≠ 0 := by linarith
  have hbase : (∫ v in (0 : ℝ)..1, v ^ (-(2 * α))) = 1 / (1 - 2 * α) := by
    rw [integral_rpow (Or.inl (by linarith))]
    have hexp : -(2 * α) + 1 = 1 - 2 * α := by ring
    rw [hexp, Real.one_rpow, Real.zero_rpow (by linarith)]
    ring
  have hsimp : (∫ v in (0 : ℝ)..1, weightProfile α v ^ 2)
      = (1 - α) ^ 2 * ∫ v in (0 : ℝ)..1, v ^ (-(2 * α)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hv
    rw [weightProfile, mul_pow, ← Real.rpow_natCast (v ^ (-α)) 2, ← Real.rpow_mul hv.1]
    congr 2
    push_cast
    ring
  rw [hsimp, hbase]
  field_simp

end

end HTGeometry
