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

/-- **A dense residual family of carriers is relation-free on the half-plane.**  The same dense
residual pattern-free family that the global statement uses, recorded with the half-plane predicate
the polynomial gauge consumes, so that the gauge applies to every member. -/
theorem countablePatterns_actualNevanlinna_notDifferentiallyAlgebraicOn_dense_residual
    (projectiveGeometry : ClassicalComplexProjectiveIncidenceGeometry)
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta] (heta : eta.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf eta hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let notDAOnCarrier : Set positiveChart := {w |
      ¬ DifferentiallyAlgebraicOn
        (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily eta
          (linftyOne eta + w.1.1))) upperHalfPlane}
    Dense notDAOnCarrier ∧ notDAOnCarrier ∈ residual positiveChart := by
  dsimp only
  obtain ⟨hdense, hres, _⟩ :=
    F.allFinitePatterns_positiveActualCarrier_relationFree_dense_residual
      (Γ := Unit)
      projectiveGeometry hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta heta
  refine ⟨hdense.mono ?_, Filter.mem_of_superset hres ?_⟩ <;>
    exact fun w hw =>
      F.not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier eta _ hw

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
