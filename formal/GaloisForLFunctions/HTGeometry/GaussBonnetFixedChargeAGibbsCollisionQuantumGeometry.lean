import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionMomentVectors

/-!
# Projective geometry of the two collision modes

The existing quantum metric, Berry curvature, and projective Gram interfaces
now apply to explicit collision moment vectors. The spectral-mixture defect
is exactly their metric area and detects complex linear independence.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Projective tangent energy is the exact collision Hankel defect. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_projective_energy (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 0)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 1) =
      egbFixedChargeAGibbsCollisionHankelDefect n o β E := by
  have h := _root_.HTGeometry.projectiveGramTangentEnergy_eq_firstKrylovDeterminant
    (fun k => egbFixedChargeAGibbsCollisionExcess n (k + o + 1) β E)
    (egbFixedChargeAGibbsCollisionMomentVector n o β E)
    (fun i j => egbFixedChargeAGibbsCollisionMomentVector_inner n o i j β E)
  simpa only [egbFixedChargeAGibbsCollisionHankelDefect,
    Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- All Berry pairings vanish because this Hilbert realization has real coordinates. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_berry_zero (n o i j : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.berryCurvatureValue
      (egbFixedChargeAGibbsCollisionMomentVector n o β E i)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E j) = 0 := by
  rw [_root_.HTGeometry.berryCurvatureValue, egbFixedChargeAGibbsCollisionMomentVector_inner]
  simp

/-- The quantum metric area equals the temporal determinant without a curvature correction. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_metric_area (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.quantumMetricAreaValue
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 0)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 1) =
      egbFixedChargeAGibbsCollisionHankelDefect n o β E := by
  rw [_root_.HTGeometry.quantumMetricAreaValue_eq_projectiveGram_add_berry,
    egbFixedChargeAGibbsCollisionMomentVector_projective_energy,
    egbFixedChargeAGibbsCollisionMomentVector_berry_zero]
  ring

/-- The two moment vectors are complex-linearly independent exactly when both spectral sectors survive. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_independent_iff (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    LinearIndependent ℂ ![egbFixedChargeAGibbsCollisionMomentVector n o β E 0,
      egbFixedChargeAGibbsCollisionMomentVector n o β E 1] ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
        0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [← _root_.HTGeometry.quantumMetricArea_strict_iff_linearIndependent_pair,
    egbFixedChargeAGibbsCollisionMomentVector_metric_area,
    egbFixedChargeAGibbsCollisionMomentVector_berry_zero]
  simpa using egbFixedChargeAGibbsCollisionHankelDefect_pos_iff n o β E

/-- Metric-area collapse is exactly the disappearance of at least one temporal spectral sector. -/
theorem egbFixedChargeAGibbsCollisionMomentVector_metric_zero_iff (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.quantumMetricAreaValue
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 0)
      (egbFixedChargeAGibbsCollisionMomentVector n o β E 1) = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsCollisionMomentVector_metric_area]
  exact egbFixedChargeAGibbsCollisionHankelDefect_zero_iff n o β E

end
end GaloisForLFunctions.HTGeometry
