import GaloisForLFunctions.HTGeometry.SingularContinuousFullTranslationFamilyFreenessUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchUniversalStrictHankelRayAdjoiningUniversalityLaw
import GaloisForLFunctions.RHTower.XiPrimeArchHankelHedenmalmSimplicityUniversalityLaw
import GaloisForLFunctions.RHTower.XiSoninStrictHankelRayUniversalityLaw

/-!
# Singular-continuous translation/prime--archimedean Hankel universality

The residual Nevanlinna carrier theorem and the universal strict-Hankel-ray adjoining theorem have
one exact common interface: the prescribed Hamburger sequence.  Atomlessness makes its complete
Hankel ray strict.  Hence the same sequence carried by the residual singular-continuous,
translation-differentially free phase can be adjoined to the prime--archimedean cone without
changing its exact Riemann-hypothesis classifier.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily
open Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

/-- **Singular-continuous translation/prime--archimedean Hankel universality law.**  One dense
residual phase simultaneously supplies singular-continuous Hamburger carriers, mixed
differential-relation freeness for every finite translated Cauchy/Herglotz family, global
hypertranscendence, a strict Hankel ray with no bounded finite realization, and an exact
prime--archimedean RH classifier obtained by adjoining that same prescribed moment ray. -/
theorem singularContinuousFullTranslation_primeArchHankelUniversality
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
    let universalPhase : Set positiveChart := {w | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0}
    (Dense universalPhase ∧ universalPhase ∈ residual positiveChart ∧
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
          (w ∈ universalPhase →
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
  let universalPhase : Set positiveChart := {w | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    F.weightedBoundaryCarrierExpandedPatternRelationHolds
      (row := CarrierPatternRow p) mu (linftyOne mu + w.1.1)
        p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
      ∀ col, coeff col = 0}
  have hfull :=
    F.singularContinuousCarrier_fullTranslationFamilyFreeness_denseResidual
      hCmin hnoCommon hCp hCc hupperMap zf hqf_inj hupperf nf eta
        hetaInfinite hetaSC hnull
  let w0 : positiveChart := ⟨0, by simp [positiveChart]⟩
  obtain ⟨_, _, _, _, _, _, _, hstrict, _, _, _, _⟩ := hfull.2.2.2 w0
  have hsCone : RiemannHypothesis ↔ PrimeArchStrictHankelRayAdjoiningCone s := by
    simpa [PrimeArchStrictHankelRayAdjoiningCone] using
      (riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay
        s (fun n => (hstrict n).1))
  have hrhReconstruction :
      RiemannHypothesis ↔ PrimeArchSourceMomentHankelExactReconstructionPhase :=
    primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis.symm.trans
      primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningPhase.symm
  have hrhSonin :
      RiemannHypothesis ↔ SoninAllNondegenerateApertureUnitCollarPhase :=
      primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis.symm.trans
      primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase
  have hconeReconstruction := hsCone.symm.trans hrhReconstruction
  exact ⟨hfull, by
      simpa [PrimeArchStrictHankelRayAdjoiningCone] using hsCone,
    hconeReconstruction,
    hsCone.symm.trans hrhSonin,
    (and_congr hconeReconstruction Iff.rfl).trans
      primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate⟩

end

end RHTower
