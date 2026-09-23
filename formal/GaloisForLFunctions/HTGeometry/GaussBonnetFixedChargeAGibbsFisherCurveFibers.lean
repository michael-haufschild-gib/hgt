import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFisher

/-! # Exact fibers of the thermal two-rate Fisher readout
The critical rates inherited from the Gauss--Bonnet kernel make one observation
reciprocal-ambiguous. Two consecutive observations remove that ambiguity. -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The entire one-reading ambiguity follows from this exact factored difference. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_difference (t u : ℝ) :
    egbFixedChargeAGibbsTunableFisherCurve t - egbFixedChargeAGibbsTunableFisherCurve u =
      (25 / 36 : ℝ) * (t ^ (2 : ℕ) - u ^ (2 : ℕ)) * (1 - t ^ (2 : ℕ) * u ^ (2 : ℕ)) /
        ((1 + t ^ (2 : ℕ)) ^ (2 : ℕ) * (1 + u ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  have ht : 1 + t ^ (2 : ℕ) ≠ 0 := (show 0 < 1 + t ^ (2 : ℕ) by positivity).ne'
  have hu : 1 + u ^ (2 : ℕ) ≠ 0 := (show 0 < 1 + u ^ (2 : ℕ) by positivity).ne'
  unfold egbFixedChargeAGibbsTunableFisherCurve
  field_simp
  <;> ring

/-- A single Fisher value identifies the squared ratio only up to reciprocation. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_eq_iff (t u : ℝ) :
    egbFixedChargeAGibbsTunableFisherCurve t = egbFixedChargeAGibbsTunableFisherCurve u ↔
      t ^ (2 : ℕ) = u ^ (2 : ℕ) ∨ t ^ (2 : ℕ) * u ^ (2 : ℕ) = 1 := by
  have hd : (1 + t ^ (2 : ℕ)) ^ (2 : ℕ) * (1 + u ^ (2 : ℕ)) ^ (2 : ℕ) ≠ 0 := by positivity
  rw [← sub_eq_zero, egbFixedChargeAGibbsTunableFisherCurve_difference,
    div_eq_zero_iff]
  simp only [hd, or_false, mul_eq_zero]
  constructor
  · rintro ((hc | h) | h)
    · norm_num at hc
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (Or.inr (sub_eq_zero.mpr h))
    · exact Or.inr (by linarith)

/-- The pure slow endpoint is the only zero readout in the positive-slow chart. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_zero_iff (t : ℝ) :
    egbFixedChargeAGibbsTunableFisherCurve t = 0 ↔ t = 0 := by
  have h := egbFixedChargeAGibbsTunableFisherCurve_eq_iff t 0
  rw [egbFixedChargeAGibbsTunableFisherCurve_endpoints.1] at h
  norm_num at h
  exact h

/-- Two consecutive readouts recover the squared ratio, including the pure slow endpoint. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_pair_eq_iff (t u : ℝ) :
    (egbFixedChargeAGibbsTunableFisherCurve t = egbFixedChargeAGibbsTunableFisherCurve u ∧
      egbFixedChargeAGibbsTunableFisherCurve (t / 4) =
        egbFixedChargeAGibbsTunableFisherCurve (u / 4)) ↔ t ^ (2 : ℕ) = u ^ (2 : ℕ) := by
  rw [egbFixedChargeAGibbsTunableFisherCurve_eq_iff,
    egbFixedChargeAGibbsTunableFisherCurve_eq_iff]
  constructor
  · rintro ⟨h, hnext⟩
    rcases h with h | h
    · exact h
    · rcases hnext with hnext | hnext
      · nlinarith
      · have he : (t / 4) ^ (2 : ℕ) * (u / 4) ^ (2 : ℕ) = t ^ (2 : ℕ) * u ^ (2 : ℕ) / 256 := by ring
        rw [he, h] at hnext
        norm_num at hnext
  · intro h
    exact ⟨Or.inl h, Or.inl (by nlinarith)⟩

/-- One reading really is non-injective even among distinct positive source ratios. -/
theorem egbFixedChargeAGibbsTunableFisherCurve_reciprocal_ambiguity :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ t ^ (2 : ℕ) ≠ u ^ (2 : ℕ) ∧
      egbFixedChargeAGibbsTunableFisherCurve t = egbFixedChargeAGibbsTunableFisherCurve u := by
  refine ⟨2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  exact (egbFixedChargeAGibbsTunableFisherCurve_eq_iff _ _).2 (Or.inr (by norm_num))

end
end GaloisForLFunctions.HTGeometry
