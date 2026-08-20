import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCurvedSuspensionHodgeTrace
import GaloisForLFunctions.RHTower.WindingNumber

/-!
# Loop-gauge applications in the RHTower corpus

Premise-free loop consequences independent of RH: a finite 't Hooft/deck charge classification and
an exact Wilson-trace resolution hierarchy for the two-orientation Gamma-six suspension.
-/

noncomputable section

namespace RHTower.LoopGaugeApplications

/-! ## 't Hooft/deck charge -/

/-- `2^k`-torsion disorder charge carried by a complex loop. -/
abbrev tHooftLoopCharge := RHTower.loopCharge

/-- The 't Hooft charge vanishes exactly when winding is divisible by its deck order. -/
theorem tHooftLoopCharge_eq_zero_iff
    (k : ℕ) (γ : ℝ → ℂ) (a b : ℝ) :
    tHooftLoopCharge k γ a b = 0 ↔
      (2 ^ k : ℤ) ∣ RHTower.windingNumber γ a b :=
  RHTower.loopCharge_eq_zero_iff k γ a b

/-! ## Wilson-trace resolution -/

/-- Ordinary trace loses the commutator, while grading, energy, and determinant recover the same
paired curvature. -/
theorem gammaSixWilson_trace_resolution_package (a : ℝ) :
    Matrix.trace
        (RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a *
            RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a -
          RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a *
            RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a) = 0 ∧
      RHTower.gradedMatrixTrace RHTower.sourceHorizontalGammaSixSuspensionGrading
        (RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a *
            RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a -
          RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a *
            RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a) =
        2 * (RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) ∧
      RHTower.sourceHorizontalGammaSixSuspensionTraceEnergy a =
        RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a ∧
      RHTower.sourceHorizontalGammaSixSuspensionTraceEnergy a =
        (Matrix.det (RHTower.sourceHorizontalGammaSixCurvedSuspension a)).re :=
  ⟨RHTower.trace_sourceHorizontalGammaSixSuspensionLeg_commutator a,
    RHTower.gradedMatrixTrace_sourceHorizontalGammaSixSuspensionLeg_commutator a,
    RHTower.sourceHorizontalGammaSixSuspensionTraceEnergy_eq_curvature a,
    RHTower.sourceHorizontalGammaSixSuspensionTraceEnergy_eq_re_det a⟩

/-- Ordinary Wilson trace is flat for every character although resolved curvature is positive
exactly away from the neutral character. -/
theorem gammaSixWilson_trace_blind_but_curvature_pos_iff (a : ℝ) :
    (Matrix.trace
          (RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a *
              RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a -
            RHTower.sourceHorizontalGammaSixReflectedSuspensionLeg a *
              RHTower.sourceHorizontalGammaSixForwardSuspensionLeg a) = 0 ∧
      0 < RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) ↔ a ≠ 0 :=
  RHTower.sourceHorizontalGammaSix_commutatorTraceFlat_but_curvature_pos_iff a

end RHTower.LoopGaugeApplications
