import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceMaximalTranslation
import GaloisForLFunctions.HTGeometry.ProjectiveLabelNullPreimage

/-!
# Global singular-continuous maximal-translation phase of the boundary carrier simplex

The finite-prefix and cofinal Cholesky theorems are already formalized in their native matrix and
Hilbert-space modules.  This file closes the remaining global category assembly on the exact
Nevanlinna carrier range: intersect the transported singular-continuous parameter phase with the
intrinsic maximal full-translation phase.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory OnePoint Set Topology
open scoped OnePoint Topology

noncomputable section

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- The full projective boundary face is the complete Nevanlinna carrier range. -/
theorem boundaryCarrierFace_univ :
    F.boundaryCarrierFace (Set.univ : Set (OnePoint ℝ)) = range F.barycenter := by
  ext nu
  constructor
  · rintro ⟨eta, _, rfl⟩
    exact ⟨eta, rfl⟩
  · rintro ⟨eta, rfl⟩
    refine ⟨eta, ?_, rfl⟩
    simp [probabilityLawsCarriedBy]

end NevanlinnaBoundaryFamily

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The exact cofinal-selection phase: singular-continuous parameter carriers with intrinsic
maximal translation-differential freeness. -/
def cofinalCholeskyResidualPhase : Set F.base.toBoundaryFamily.carrierRange :=
  F.base.toBoundaryFamily.singularContinuousParameterCarrierPhase ∩
    {nu | MaximalTranslationDifferentialFree nu.1}

/-- The maximal-translation locus is dense in the complete boundary carrier range. -/
theorem carrierRange_maximalTranslationPhase_dense
    (inputs : F.MaximalTranslationInputs) :
    Dense ({nu : F.base.toBoundaryFamily.carrierRange |
      MaximalTranslationDifferentialFree nu.1} :
        Set F.base.toBoundaryFamily.carrierRange) := by
  let BF := F.base.toBoundaryFamily
  rw [Subtype.dense_iff]
  have himage :
      ((↑) : BF.carrierRange → ProbabilityMeasure ℝ) ''
          {nu : BF.carrierRange | MaximalTranslationDifferentialFree nu.1} =
        {nu : ProbabilityMeasure ℝ | MaximalTranslationDifferentialFree nu} ∩
          range BF.barycenter := by
    ext nu
    simp [NevanlinnaBoundaryFamily.carrierRange]
  rw [himage, ← BF.boundaryCarrierFace_univ]
  have h := F.boundaryCarrierFace_subset_closure_maximalTranslationDifferentialFree
    inputs Set.univ isClosed_univ Set.infinite_univ
  simpa [BF, F.base.toBoundaryFamily.boundaryCarrierFace_univ] using h

/-- The maximal-translation locus is a relative `G_delta` on the complete carrier range, by the
parent relation-detector theorem. -/
theorem carrierRange_maximalTranslationPhase_isGdelta
    (inputs : F.MaximalTranslationInputs) :
    IsGδ ({nu : F.base.toBoundaryFamily.carrierRange |
      MaximalTranslationDifferentialFree nu.1} :
        Set F.base.toBoundaryFamily.carrierRange) := by
  exact isGδ_induced continuous_subtype_val inputs.phase_isGδ

/-- The singular-continuous maximal-translation phase is dense `G_delta`, hence residual, in the
entire canonical Nevanlinna carrier simplex. -/
theorem cofinalCholeskyResidualPhase_dense_gdelta_residual
    (inputs : F.MaximalTranslationInputs) :
    Dense F.cofinalCholeskyResidualPhase ∧
      IsGδ F.cofinalCholeskyResidualPhase ∧
      F.cofinalCholeskyResidualPhase ∈
        residual F.base.toBoundaryFamily.carrierRange := by
  let BF := F.base.toBoundaryFamily
  have hcompact : IsCompact (Set.univ : Set (ProbabilityMeasure (OnePoint ℝ))) :=
    isCompact_univ
  have hcarrierCompact : IsCompact (range BF.barycenter) := by
    simpa only [image_univ] using hcompact.image BF.barycenter_isClosedEmbedding.continuous
  letI : CompactSpace BF.carrierRange :=
    isCompact_iff_compactSpace.mp hcarrierCompact
  let singularPhase := BF.singularContinuousParameterCarrierPhase
  let maximalPhase : Set BF.carrierRange :=
    {nu | MaximalTranslationDifferentialFree nu.1}
  have hsingularG : IsGδ singularPhase := by
    simpa [singularPhase] using BF.singularContinuousParameterCarrierPhase_isGdelta
  have hsingularDense : Dense singularPhase := by
    simpa [singularPhase] using BF.singularContinuousParameterCarrierPhase_dense
  have hmaximalG : IsGδ maximalPhase := by
    simpa [maximalPhase, BF] using F.carrierRange_maximalTranslationPhase_isGdelta inputs
  have hmaximalDense : Dense maximalPhase := by
    simpa [maximalPhase, BF] using F.carrierRange_maximalTranslationPhase_dense inputs
  have hdense : Dense (singularPhase ∩ maximalPhase) :=
    Dense.inter_of_Gδ hsingularG hmaximalG hsingularDense hmaximalDense
  have hgdelta : IsGδ (singularPhase ∩ maximalPhase) :=
    hsingularG.inter hmaximalG
  refine ⟨?_, ?_, ?_⟩
  · simpa [cofinalCholeskyResidualPhase, singularPhase, maximalPhase, BF] using hdense
  · simpa [cofinalCholeskyResidualPhase, singularPhase, maximalPhase, BF] using hgdelta
  · apply residual_of_dense_Gδ
    · simpa [cofinalCholeskyResidualPhase, singularPhase, maximalPhase, BF] using hgdelta
    · simpa [cofinalCholeskyResidualPhase, singularPhase, maximalPhase, BF] using hdense

/-- Under the real-analytic lower-row hypothesis from the card, every point of the global phase is
an atomless real-Lebesgue-singular carrier and is maximally translation free. -/
theorem cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation
    (hC : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d univ)
    (nu : F.base.toBoundaryFamily.carrierRange)
    (hnu : nu ∈ F.cofinalCholeskyResidualPhase) :
    NullSingletonClass (nu.1 : Measure ℝ) ∧
      (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) ∧
      MaximalTranslationDifferentialFree nu.1 := by
  have hsingular :=
    F.base.toBoundaryFamily.singularContinuousParameterCarrierPhase_isSingularContinuous_of_analytic
      hC hD nu hnu.1
  exact ⟨hsingular.1, hsingular.2, hnu.2⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
