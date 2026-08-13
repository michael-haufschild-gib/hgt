import GaloisForLFunctions.HTGeometry.NevanlinnaCarrierDenominatorRow
import GaloisForLFunctions.HTGeometry.NevanlinnaEntryConjugation
import GaloisForLFunctions.HTGeometry.NevanlinnaTransferMinimalType
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceMaximalTranslation

/-!
# The complete classical input packet of the constructed carrier family

Every field of `MaximalTranslationInputs` is discharged unconditionally for the constructed
classical analytic Nevanlinna carrier family: minimal exponential type of the `c` entry is
M. Riesz's theorem in transfer form; the denominator row has no common zero; `c` has a real zero
and is regular at `i`; and the Weyl-disc pole maps the lower half-plane into the upper one by the
entry conjugation symmetry.  Consequently the dense residual maximal-translation phase on every
infinite closed boundary face holds for the constructed family with no hypothesis beyond a
positive moment form with bounded kernel at `0` and unit mass.
-/

open Filter MeasureTheory Topology
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

noncomputable section

/-- **M. Riesz for the carrier family**: the `c` entry has minimal exponential type. -/
theorem analyticNevCarrierFamily_minimalExponentialType (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    GaloisForLFunctions.HTGeometry.HasMinimalExponentialType
      (analyticNevCarrierFamily h h0b h0).c :=
  nevBinf_hasMinimalExponentialType h h0b

/-- **The complete classical input packet for the constructed carrier family.** -/
def analyticNevCarrierFamilyMaximalTranslationInputs (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).MaximalTranslationInputs where
  minimalExponentialType := analyticNevCarrierFamily_minimalExponentialType h h0b h0
  noCommonZero := analyticNevCarrierFamily_noCommonZero h h0b h0
  zeroPoint := Classical.choose (analyticNevCarrierFamily_exists_zero h h0b h0)
  zeroPoint_spec := Classical.choose_spec (analyticNevCarrierFamily_exists_zero h h0b h0)
  regularPoint := Complex.I
  regularPoint_spec := analyticNevCarrierFamily_regular h h0b h0
  upperMap := analyticNevCarrierFamily_lowerMap h h0b h0

/-- **The dense residual maximal-translation phase of the constructed family**, on every
infinite closed boundary face, with no analytic hypothesis left. -/
theorem analyticNevCarrierFamily_maximalTranslationPhase_dense_residual
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (K : Set (OnePoint ℝ)) (hKclosed : IsClosed K) (hK : K.Infinite) :
    Dense ((analyticNevCarrierFamily h h0b
        h0).boundaryCarrierFaceMaximalTranslationPhase K) ∧
      (analyticNevCarrierFamily h h0b
          h0).boundaryCarrierFaceMaximalTranslationPhase K ∈
        residual {nu : ProbabilityMeasure ℝ //
          nu ∈ (analyticNevCarrierFamily h h0b
            h0).base.toBoundaryFamily.boundaryCarrierFace K} :=
  (analyticNevCarrierFamily h h0b
    h0).boundaryCarrierFace_maximalTranslationPhase_dense_residual
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0) K hKclosed hK

/-- The full-rank phase version of the capstone for the constructed family. -/
theorem analyticNevCarrierFamily_maximalTranslationFullRankPhase_dense_residual
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (K : Set (OnePoint ℝ)) (hKclosed : IsClosed K) (hK : K.Infinite) :
    Dense ((analyticNevCarrierFamily h h0b
        h0).boundaryCarrierFaceMaximalTranslationFullRankPhase K) ∧
      (analyticNevCarrierFamily h h0b
          h0).boundaryCarrierFaceMaximalTranslationFullRankPhase K ∈
        residual {nu : ProbabilityMeasure ℝ //
          nu ∈ (analyticNevCarrierFamily h h0b
            h0).base.toBoundaryFamily.boundaryCarrierFace K} :=
  (analyticNevCarrierFamily h h0b
    h0).boundaryCarrierFace_maximalTranslationFullRankPhase_dense_residual
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0) K hKclosed hK

end

end HTGeometry
