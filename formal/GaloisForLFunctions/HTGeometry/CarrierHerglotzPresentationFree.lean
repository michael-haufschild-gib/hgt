import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.RegularizedTransformGauge

/-!
# The Herglotz presentation of a pattern-free carrier

The packet argument delivers relation-freeness of a carrier's Cauchy transform at nodes in the
upper half-plane; the polynomial gauge lifts relation-freeness from a Cauchy transform to its
Herglotz presentation.  The two meet here.

The gauge needs no knowledge of how the carrier was produced, so the composition is direct: any
carrier avoiding every canonical finite pattern has a Herglotz presentation satisfying no algebraic
differential equation on the upper half-plane.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- Pattern relation-freeness, restated for the Cauchy transform in the form the gauge consumes. -/
theorem not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    (hfree : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    ¬ DifferentiallyAlgebraicOn
      (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily eta density))
      upperHalfPlane := by
  intro h
  obtain ⟨n, P, hP, hrel⟩ := h
  exact
    F.not_differentiallyAlgebraicOn_weightedBoundaryCarrierCauchy_of_allFinitePatterns_relationFree
      eta density hfree ⟨n, P, hP, fun z hz => hrel z hz⟩

/-- **The Herglotz presentation of a pattern-free carrier admits no differential relation.**  For
any mass constant, the normalized presentation `z * M + (1 + z ^ 2) * C` of a carrier avoiding every
canonical finite pattern satisfies no algebraic differential equation on the upper half-plane. -/
theorem not_differentiallyAlgebraicOn_herglotzPresentation_weightedBoundaryCarrier
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (density : Lp ℝ (⊤ : ENNReal) eta)
    [IsFiniteMeasure (weightedBoundaryCarrier F.base.toBoundaryFamily eta density)]
    (M : ℂ)
    (hfree : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) eta density p.coefficientDegree p.orders
          (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => z * M + (1 + z ^ 2) *
        cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily eta density) z)
      upperHalfPlane :=
  not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane _ M
    (F.not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier eta density hfree)

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
