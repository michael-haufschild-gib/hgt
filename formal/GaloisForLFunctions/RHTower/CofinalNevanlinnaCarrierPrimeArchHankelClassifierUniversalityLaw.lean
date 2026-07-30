import GaloisForLFunctions.HTGeometry.CofinalSingularContinuousCauchyHerglotzLocalGlobalUniversalityLaw
import GaloisForLFunctions.RHTower.SingularContinuousTranslationPrimeArchHankelUniversalityLaw

/-!
# Cofinal Nevanlinna carriers as prime--archimedean Hankel classifiers

Every point of the global cofinal Cholesky phase lies in the complete canonical Nevanlinna
carrier range, hence represents the prescribed Hamburger sequence. Atomlessness makes that
sequence a strict Hankel ray. Thus every carrier in the same dense residual phase carries both
the complete Cauchy--Herglotz freeness payload and exact prime--archimedean RH, reconstruction,
Sonin, and Hedenmalm classifiers.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily
open Filter MeasureTheory OnePoint Set Topology
open scoped ENNReal OnePoint Topology

noncomputable section

/-- **Cofinal Nevanlinna-carrier prime--archimedean Hankel-classifier universality law.** The
complete cofinal carrier phase is dense `G_delta` and residual; every member is simultaneously
singular-continuous, maximally translation free, Cauchy--Herglotz hypertranscendental, a strict
Hamburger Hankel realization, and a carrier of the exact prime--archimedean classifier family. -/
theorem cofinalNevanlinnaCarrier_primeArchHankelClassifierUniversality
    {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
    (inputs : F.MaximalTranslationInputs)
    (hC : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d univ) :
    Dense F.cofinalCholeskyResidualPhase ∧
      IsGδ F.cofinalCholeskyResidualPhase ∧
      F.cofinalCholeskyResidualPhase ∈
        residual F.base.toBoundaryFamily.carrierRange ∧
      ∀ nu : F.base.toBoundaryFamily.carrierRange,
        nu ∈ F.cofinalCholeskyResidualPhase →
          NullSingletonClass (nu.1 : Measure ℝ) ∧
          (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) ∧
          MaximalTranslationDifferentialFree nu.1 ∧
          (¬ DifferentiallyAlgebraicOn
            (cauchyTransform (nu.1 : Measure ℝ)) upperHalfPlane) ∧
          (∀ M : ℂ, ¬ DifferentiallyAlgebraicOn
            (fun z => z * M + (1 + z ^ 2) *
              cauchyTransform (nu.1 : Measure ℝ) z) upperHalfPlane) ∧
          Hypertranscendental (cauchyTransform (nu.1 : Measure ℝ)) ∧
          (∀ M : ℂ, Hypertranscendental
            (fun z => z * M + (1 + z ^ 2) *
              cauchyTransform (nu.1 : Measure ℝ) z)) ∧
          HasHamburgerMoments s (nu.1 : Measure ℝ) ∧
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
  obtain ⟨hdense, hgdelta, hresidual⟩ :=
    F.cofinalCholeskyResidualPhase_dense_gdelta_residual inputs
  refine ⟨hdense, hgdelta, hresidual, ?_⟩
  intro nu hnu
  obtain ⟨hnoAtoms, hsingular, hmaximal, hcauchy, hherglotz,
      hglobalCauchy, hglobalHerglotz⟩ :=
    F.cofinalCholeskyResidualPhase_singularContinuous_cauchyHerglotzLocalGlobalUniversality
      hC hD nu hnu
  obtain ⟨eta, heta⟩ := nu.property
  have hmoments : HasHamburgerMoments s (nu.1 : Measure ℝ) := by
    rw [← heta]
    exact F.base.toBoundaryFamily.barycenter_hasHamburgerMoments eta
  have hstrict :=
    strictHankelRay_of_atomlessProbability_hamburgerMoments
      (nu.1 : Measure ℝ) hmoments
  have hnoFinite :=
    noFiniteSpectralOrStateLocalClosure_of_strictHankelRay
      (fun n => (hstrict n).2)
  obtain ⟨hnoShift, hnoGram⟩ :=
    noShiftInvariantGramRealization_of_strictHankelRay
      (fun n => (hstrict n).1)
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
  exact ⟨hnoAtoms, hsingular, hmaximal, hcauchy, hherglotz,
    hglobalCauchy, hglobalHerglotz, hmoments, hstrict, hnoFinite,
    hnoShift, hnoGram,
    by simpa [PrimeArchStrictHankelRayAdjoiningCone] using hsCone,
    hconeReconstruction, hsCone.symm.trans hrhSonin,
    (and_congr hconeReconstruction Iff.rfl).trans
      primeArchSourceMomentHankelExactReconstructionPhase_and_xiZerosSimple_iff_hendenmalmUniversalCertificate⟩

end

end RHTower
