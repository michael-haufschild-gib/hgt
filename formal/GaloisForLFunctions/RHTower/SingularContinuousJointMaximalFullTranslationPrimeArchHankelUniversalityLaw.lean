import GaloisForLFunctions.HTGeometry.SingularContinuousHerglotzMaximalFreenessUniversalityLaw
import GaloisForLFunctions.RHTower.SingularContinuousTranslationPrimeArchHankelUniversalityLaw

/-!
# Joint maximal/full-translation singular-continuous prime--archimedean universality

The maximal intrinsic-translation Cauchy--Herglotz phase and the complete finite
translated-family phase are two residual subsets of the same positive Nevanlinna chart. Their
intersection is residual and dense. Thus one singular-continuous carrier simultaneously realizes
both analytic freeness regimes, while its strict Hamburger moment ray retains all
prime--archimedean RH, reconstruction, Sonin, and Hedenmalm classifiers.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily
open Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

/-- **Singular-continuous joint maximal/full-translation prime--archimedean Hankel universality
law.** The intersection of the maximal intrinsic-translation Herglotz phase and the countable
full-translation family phase is dense residual. Every carrier in that same joint phase has both
freeness payloads, while the common strict Hamburger ray retains the exact prime--archimedean,
reconstruction, Sonin, and Hedenmalm classifiers. -/
theorem singularContinuous_jointMaximalFullTranslation_primeArchHankelUniversality
    {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
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
    let maximalPhase : Set positiveChart := {w | ∀
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
    let fullPhase : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0}
    let jointPhase : Set positiveChart := maximalPhase ∩ fullPhase
    (Dense jointPhase ∧ jointPhase ∈ residual positiveChart ∧
      (∀ t u : ℝ, t ≠ u →
        (F.base.leaf (t : OnePoint ℝ) : Measure ℝ) ⟂ₘ
            (F.base.leaf (u : OnePoint ℝ) : Measure ℝ) ∧
          (((F.base.leaf (t : OnePoint ℝ) : Measure ℝ).toSignedMeasure -
              (F.base.leaf (u : OnePoint ℝ) : Measure ℝ).toSignedMeasure).totalVariation
                Set.univ = 2)) ∧
      ∀ w : positiveChart,
        let density := linftyOne mu + w.1.1
        let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
        LinftyStrictlyPositive mu density ∧
          ∫ t, density t ∂mu = 1 ∧
          IsProbabilityMeasure carrier ∧ NoAtoms carrier ∧
          carrier ⟂ₘ (volume : Measure ℝ) ∧
          MaximallySeparatedFromAbsolutelyContinuousProbabilities carrier ∧
          HasHamburgerMoments s carrier ∧
          (∀ n : ℕ,
            (HTGeometry.momentHankelMatrix s n).PosDef ∧
              0 < (HTGeometry.momentHankelMatrix s n).det) ∧
          (∀ d : ℕ,
            ¬ HTGeometry.FixedSpectralWidthLocalClosure d s ∧
              ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d s) ∧
          (¬ HTGeometry.HankelShiftInvariant s) ∧
          (∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
            (v : ℕ → E),
            (∀ i j, inner ℝ (v i) (v j) = s (i + j)) →
            ¬ ∀ i j,
              inner ℝ (v (i + 1)) (v (j + 1)) = inner ℝ (v i) (v j)) ∧
          (w ∈ jointPhase →
            (∀ (hpositive : LinftyStrictlyPositive mu density)
                (hintegral : ∫ t, density t ∂mu = 1),
              MaximalTranslationDifferentialFree
                (weightedBoundaryProbabilityCarrier F.base.toBoundaryFamily
                  mu density hpositive hintegral)) ∧
            (¬ DifferentiallyAlgebraicOn (cauchyTransform carrier) upperHalfPlane) ∧
            (∀ M : ℂ,
              ¬ DifferentiallyAlgebraicOn
                (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z)
                upperHalfPlane) ∧
            (∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
                (¬ FamilyDifferentiallyAlgebraicOn
                  (fun i z => cauchyTransform carrier (z + shift.1 i))
                  (commonUpperTranslationDomain shift)) ∧
                ∀ M : ℂ,
                  ¬ FamilyDifferentiallyAlgebraicOn
                    (fun i z => (z + shift.1 i) * M + (1 + (z + shift.1 i) ^ 2) *
                      cauchyTransform carrier (z + shift.1 i))
                    (commonUpperTranslationDomain shift)) ∧
            Hypertranscendental (cauchyTransform carrier) ∧
            ∀ M : ℂ, Hypertranscendental
              (fun z => z * M + (1 + z ^ 2) * cauchyTransform carrier z))) ∧
    (RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
          0 < alpha + beta + gamma + delta →
            ∀ n : ℕ,
              (HTGeometry.momentHankelMatrix
                (primeArchAdjoinedStrictHankelMixedClock
                  s scaleLog alpha beta gamma delta) n).PosDef) ∧
    (PrimeArchStrictHankelRayAdjoiningCone s ↔
      PrimeArchSourceMomentHankelExactReconstructionPhase) ∧
    (PrimeArchStrictHankelRayAdjoiningCone s ↔
      SoninAllNondegenerateApertureUnitCollarPhase) ∧
    ((PrimeArchStrictHankelRayAdjoiningCone s ∧ XiZerosSimple) ↔
      XiHedenmalmRHSimplicityUniversalCertificate) := by
  dsimp only
  let mu : Measure (OnePoint ℝ) := eta
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => F.quotient (zf i)) nf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let positiveChart : Set S := Metric.ball 0 1
  let maximalPhase : Set positiveChart := {w | ∀
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
  let fullPhase : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0}
  let jointPhase : Set positiveChart := maximalPhase ∩ fullPhase
  obtain ⟨_hmaxDense, hmaxResidual, hmaxAll⟩ :=
    F.singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual
      hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta
        hetaInfinite hetaSC hnull
  obtain ⟨hfull, hrh, hreconstruction, hsonin, hhedenmalm⟩ :=
    singularContinuousFullTranslation_primeArchHankelUniversality
      F hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta
        hetaInfinite hetaSC hnull
  obtain ⟨_hfullDense, hfullResidual, hleaf, hfullAll⟩ := hfull
  have hjointResidual : jointPhase ∈ residual positiveChart := by
    simpa only [jointPhase] using Filter.inter_mem hmaxResidual hfullResidual
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  have hpositiveOpen : IsOpen positiveChart := Metric.isOpen_ball
  letI : BaireSpace positiveChart := hpositiveOpen.baireSpace
  refine ⟨⟨dense_of_mem_residual hjointResidual, hjointResidual, hleaf, ?_⟩,
    hrh, hreconstruction, hsonin, hhedenmalm⟩
  intro w
  let density := linftyOne mu + w.1.1
  let carrier := weightedBoundaryCarrier F.base.toBoundaryFamily mu density
  obtain ⟨hpositive, hintegral, hprobability, hnoAtoms, hsingular,
      hmaximalTV, hmoments, hstrict, hnoFinite, hnoShift, hnoGram, hfullPhase⟩ := hfullAll w
  refine ⟨hpositive, hintegral, hprobability, hnoAtoms, hsingular,
    hmaximalTV, hmoments, hstrict, hnoFinite, hnoShift, hnoGram, ?_⟩
  intro hw
  have hwMaximal : w ∈ maximalPhase := hw.1
  have hwFull : w ∈ fullPhase := hw.2
  obtain ⟨_hpositiveMax, _hintegralMax, _hprobabilityMax, _hnoAtomsMax,
      _hsingularMax, _hmomentsMax, hmaximalPhase⟩ := hmaxAll w
  obtain ⟨hmaximal, hcauchy, hherglotz⟩ := hmaximalPhase hwMaximal
  obtain ⟨hfamilies, hglobalCauchy, hglobalHerglotz⟩ := hfullPhase hwFull
  exact ⟨hmaximal, hcauchy, hherglotz, hfamilies, hglobalCauchy, hglobalHerglotz⟩

end

end RHTower
