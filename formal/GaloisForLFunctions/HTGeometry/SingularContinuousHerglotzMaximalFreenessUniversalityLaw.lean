import GaloisForLFunctions.HTGeometry.BoundaryCarrierTranslationFreeness
import GaloisForLFunctions.HTGeometry.CarrierHerglotzPresentationFree
import GaloisForLFunctions.HTGeometry.CauchyHerglotzLocalGlobalHypertranscendenceUniversalityLaw
import GaloisForLFunctions.HTGeometry.NevanlinnaPositiveCarrierCapstone

/-!
# Singular-continuous Herglotz maximal-freeness universality

The all-finite-pattern positive Nevanlinna phase carries more simultaneous information than any
one of its existing projections records.  The same residual witness gives intrinsic freeness of
all translated finite jet patterns, upper-half-plane relation-freeness of the Cauchy transform and
every normalized Herglotz presentation, and singular-continuous probability solutions of the
original Hamburger moment problem.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- **Residual singular-continuous Herglotz maximal-freeness law.**  One dense residual positive
phase simultaneously retains intrinsic translated-jet freeness, Cauchy and Herglotz presentation
relation-freeness, and the singular-continuous Hamburger carrier structure. -/
theorem singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite)
    (hetaSC : eta ∈ projectiveSingularContinuousProbabilityLaws)
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ)
        (F.base.toBoundaryFamily.matrix.projectiveLabel ⁻¹' E) = 0) :
    let mu : Measure (OnePoint ℝ) := eta
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let universalPhase : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0} ∩
      {w | ¬ DifferentiallyAlgebraicOn
        (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
          (linftyOne mu + w.1.1))) upperHalfPlane}
    Dense universalPhase ∧ universalPhase ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        let density := linftyOne mu + w.1.1
        let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
        LinftyStrictlyPositive mu density ∧
          ∫ t, density t ∂mu = 1 ∧
          IsProbabilityMeasure carrier ∧ NoAtoms carrier ∧
          carrier ⟂ₘ (volume : Measure ℝ) ∧ HasHamburgerMoments s carrier ∧
          (w ∈ universalPhase →
            (∀ (hpositive : LinftyStrictlyPositive mu density)
                (hintegral : ∫ t, density t ∂mu = 1),
              MaximalTranslationDifferentialFree
                (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
                  mu density hpositive hintegral)) ∧
            (¬ DifferentiallyAlgebraicOn (cauchyTransform carrier) upperHalfPlane) ∧
            ∀ M : ℂ,
              ¬ DifferentiallyAlgebraicOn
                (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z)
                upperHalfPlane) := by
  dsimp only
  let mu : Measure (OnePoint ℝ) := eta
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let universalPhase : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0} ∩
    {w | ¬ DifferentiallyAlgebraicOn
      (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
        (linftyOne mu + w.1.1))) upperHalfPlane}
  letI : IsProbabilityMeasure mu := eta.prop
  have hrelationPhase :
      Dense {w : positiveChart | ∀
          (p : FiniteDifferentialPattern Unit)
          (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
          (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
          F.weightedBoundaryCarrierExpandedPatternRelationHolds
            (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
              p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
            ∀ col, coeff col = 0} ∧
        {w : positiveChart | ∀
          (p : FiniteDifferentialPattern Unit)
          (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
          (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
          F.weightedBoundaryCarrierExpandedPatternRelationHolds
            (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
              p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
            ∀ col, coeff col = 0} ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
          ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
    simpa [positiveChart, frozen, S, mu] using
      (F.allFinitePatterns_positiveActualCarrier_relationFree_dense_residual
        (Γ := Unit) hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf mu hetaInfinite)
  have hcauchyPhase :
      Dense {w : positiveChart | ¬ DifferentiallyAlgebraicOn
        (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
          (linftyOne mu + w.1.1))) upperHalfPlane} ∧
        {w : positiveChart | ¬ DifferentiallyAlgebraicOn
          (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
            (linftyOne mu + w.1.1))) upperHalfPlane} ∈ residual positiveChart := by
    simpa [positiveChart, frozen, S, mu] using
      (F.countablePatterns_actualNevanlinna_notDifferentiallyAlgebraicOn_dense_residual
        hCmin hnoCommon hCp hCc hupperMap
        zf hqf_inj hupperf nf mu hetaInfinite)
  have hphaseResidual : universalPhase ∈ residual positiveChart := by
    simpa only [universalPhase] using
      Filter.inter_mem hrelationPhase.2.1 hcauchyPhase.2
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  have hpositiveOpen : IsOpen positiveChart := Metric.isOpen_ball
  letI : BaireSpace positiveChart := hpositiveOpen.baireSpace
  refine ⟨dense_of_mem_residual hphaseResidual, hphaseResidual, ?_⟩
  intro w
  let density := linftyOne mu + w.1.1
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
  have hpositive : LinftyStrictlyPositive mu density := hrelationPhase.2.2 w |>.1
  have hintegral : ∫ t, density t ∂mu = 1 := hrelationPhase.2.2 w |>.2
  have hstructure := weightedBoundaryCarrier_singularContinuous_probability
    F.base.toBoundaryFamily eta hetaSC hnull density hpositive hintegral
  refine ⟨hpositive, hintegral, hstructure.1, hstructure.2.1,
    hstructure.2.2.1, hstructure.2.2.2, ?_⟩
  intro hw
  have hfree : ∀
      (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu density
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0 := by
    simpa only [universalPhase, Set.mem_inter_iff, Set.mem_setOf_eq] using hw.1
  have hmaximal :
      ∀ (hp : LinftyStrictlyPositive mu density)
          (hi : ∫ t, density t ∂mu = 1),
        MaximalTranslationDifferentialFree
          (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
            mu density hp hi) := by
    intro hp hi
    exact F.maximalTranslationDifferentialFree_weightedBoundaryProbabilityCarrier
      mu density hp hi hfree
  have hcauchy :
      ¬ DifferentiallyAlgebraicOn (cauchyTransform carrier) upperHalfPlane := by
    simpa only [carrier, density] using hw.2
  letI : IsProbabilityMeasure carrier := hstructure.1
  have hpresentation : ∀ M : ℂ,
      ¬ DifferentiallyAlgebraicOn
        (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z)
        upperHalfPlane := by
    intro M
    exact not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane
      carrier M hcauchy
  exact ⟨hmaximal, hcauchy, hpresentation⟩

/-- **Residual singular-continuous global Cauchy--Herglotz universality law.**  Every point of
the residual maximal-freeness phase has a globally hypertranscendental Cauchy transform, and every
normalized Herglotz presentation of the same carrier is globally hypertranscendental as well. -/
theorem
    singularContinuousCarrier_cauchyHerglotz_globalHypertranscendence_of_mem_universalPhase
    {ιf : Type} [Fintype ιf] [DecidableEq ιf]
    (hCmin : HasMinimalExponentialType F.c)
    (hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0))
    {p0 : ℂ} (hCp : F.c p0 = 0) {c0 : ℂ} (hCc : F.c c0 ≠ 0)
    (hupperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im)
    (zf : ιf → ℂ)
    (hqf_inj : Function.Injective (fun i => F.quotient (zf i)))
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (nf : ιf → ℕ)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (hetaInfinite : (eta : Measure (OnePoint ℝ)).support.Infinite)
    (hetaSC : eta ∈ projectiveSingularContinuousProbabilityLaws)
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ)
        (F.base.toBoundaryFamily.matrix.projectiveLabel ⁻¹' E) = 0) :
    let mu : Measure (OnePoint ℝ) := eta
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => F.quotient (zf i)) nf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let universalPhase : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0} ∩
      {w | ¬ DifferentiallyAlgebraicOn
        (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
          (linftyOne mu + w.1.1))) upperHalfPlane}
    ∀ w : positiveChart, w ∈ universalPhase →
      let density := linftyOne mu + w.1.1
      let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
      Hypertranscendental (cauchyTransform carrier) ∧
        ∀ M : ℂ, Hypertranscendental
          (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z) := by
  dsimp only
  let mu : Measure (OnePoint ℝ) := eta
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let universalPhase : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern Unit)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0} ∩
    {w | ¬ DifferentiallyAlgebraicOn
      (cauchyTransform (weightedBoundaryCarrier F.base.toBoundaryFamily mu
        (linftyOne mu + w.1.1))) upperHalfPlane}
  obtain ⟨_hdense, _hresidual, hall⟩ :=
    F.singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual
      hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta
        hetaInfinite hetaSC hnull
  intro w hw
  let density := linftyOne mu + w.1.1
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
  obtain ⟨_hpositive, _hintegral, hprobability, _hnoAtoms, _hsingular,
      _hmoments, hphase⟩ := hall w
  obtain ⟨_hmaximal, hcauchy, _hherglotz⟩ := hphase hw
  letI : IsProbabilityMeasure carrier := hprobability
  exact cauchyHerglotz_upperHalfPlane_globalHypertranscendence carrier hcauchy

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
