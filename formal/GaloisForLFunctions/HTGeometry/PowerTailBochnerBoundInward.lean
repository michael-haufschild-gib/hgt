import GaloisForLFunctions.HTGeometry.PowerTailBochnerBound

/-!
# The inward tail of a power-dominated Bochner integral

The mirror of `PowerTailBochnerBound`.  The dominating majorant `C|t|^{-q}` is even, so reflection
carries the right ray's estimates to the left one verbatim; only the endpoint changes sign.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- The power tail's integral on the left ray. -/
theorem integral_powerTail_Iic {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    ∫ ξ in Iic (-t), |ξ| ^ (-p) = t ^ (1 - p) / (p - 1) := by
  rw [← integral_comp_neg_Ioi t fun η : ℝ => |η| ^ (-p)]
  simp only [abs_neg]
  exact integral_powerTail_Ioi ht hp

omit [NormedSpace ℝ X] in
/-- A profile dominated by a power tail below a negative radius is integrable there. -/
theorem integrableOn_of_powerTail_bound_Iic {f : ℝ → X} {C q x : ℝ} (hq : 1 < q) (hx : x < 0)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Iic x)))
    (hf : ∀ t ∈ Iic x, ‖f t‖ ≤ C * |t| ^ (-q)) :
    IntegrableOn f (Iic x) := by
  have hbase : IntegrableOn (fun ξ : ℝ => |ξ| ^ (-q)) (Iic x) volume := by
    have h := integrableOn_powerTail_Iic (t := -x) (p := q) (by linarith) hq
    rwa [neg_neg] at h
  refine Integrable.mono' (hbase.const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
  exact hf t ht

/-- **The inward tail of a power-dominated profile.** -/
theorem norm_integral_Iic_le_powerTail {f : ℝ → X} {C q x : ℝ} (hq : 1 < q) (hx : x < 0)
    (hf : ∀ t ∈ Iic x, ‖f t‖ ≤ C * |t| ^ (-q)) :
    ‖∫ t in Iic x, f t‖ ≤ C * ((-x) ^ (1 - q) / (q - 1)) := by
  have hbase : IntegrableOn (fun ξ : ℝ => |ξ| ^ (-q)) (Iic x) volume := by
    have h := integrableOn_powerTail_Iic (t := -x) (p := q) (by linarith) hq
    rwa [neg_neg] at h
  have hval : ∫ ξ in Iic x, |ξ| ^ (-q) = (-x) ^ (1 - q) / (q - 1) := by
    have h := integral_powerTail_Iic (t := -x) (p := q) (by linarith) hq
    rwa [neg_neg] at h
  have hle := MeasureTheory.norm_integral_le_of_norm_le (hbase.const_mul C)
    (by filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht using hf t ht)
  rwa [integral_const_mul, hval] at hle

end GaloisForLFunctions.HTGeometry
