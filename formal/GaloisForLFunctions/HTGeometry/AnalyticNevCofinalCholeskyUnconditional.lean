import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaMaximalTranslationInputs
import GaloisForLFunctions.HTGeometry.CofinalCholeskyResidualPhase

/-!
# The global cofinal-selection phase of the constructed carrier family

The constructed analytic Nevanlinna carrier family of an indeterminate normalised moment sequence
carries a complete term of `MaximalTranslationInputs`.  Feeding it to the global assembly gives the
singular-continuous maximal-translation phase of the carrier simplex with no analytic hypothesis
left: on the complete Nevanlinna carrier range the phase is dense, `Gδ`, and residual, and each of
its points is an atomless carrier, singular with respect to Lebesgue measure, and maximally
translation-differentially free.
-/

open Filter MeasureTheory OnePoint Set Topology
open GaloisForLFunctions.HTGeometry
open scoped OnePoint Topology

namespace HTGeometry

noncomputable section

variable {s : ℕ → ℝ}

/-- **The cofinal-selection phase of the constructed family is dense `Gδ` and residual** in the
complete Nevanlinna carrier range. -/
theorem analyticNevCarrierFamily_cofinalCholeskyResidualPhase_dense_gdelta_residual
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Dense (analyticNevCarrierFamily h h0b h0).cofinalCholeskyResidualPhase ∧
      IsGδ (analyticNevCarrierFamily h h0b h0).cofinalCholeskyResidualPhase ∧
      (analyticNevCarrierFamily h h0b h0).cofinalCholeskyResidualPhase ∈
        residual (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily.carrierRange :=
  (analyticNevCarrierFamily h h0b h0).cofinalCholeskyResidualPhase_dense_gdelta_residual
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0)

/-- **Every point of the constructed cofinal phase is an atomless Lebesgue-singular carrier with
maximal translation freedom.** -/
theorem analyticNevCarrierFamily_cofinalPhase_isSingularContinuous_maximalTranslation
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (nu : (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily.carrierRange)
    (hnu : nu ∈ (analyticNevCarrierFamily h h0b h0).cofinalCholeskyResidualPhase) :
    NullSingletonClass (nu.1 : Measure ℝ) ∧
      (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) ∧
      MaximalTranslationDifferentialFree nu.1 :=
  (analyticNevCarrierFamily h h0b
    h0).cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation nu hnu

/-- The maximal-translation locus alone is dense in the complete constructed carrier range. -/
theorem analyticNevCarrierFamily_carrierRange_maximalTranslationPhase_dense
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Dense ({nu : (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily.carrierRange |
      MaximalTranslationDifferentialFree nu.1} :
        Set (analyticNevCarrierFamily h h0b h0).base.toBoundaryFamily.carrierRange) :=
  (analyticNevCarrierFamily h h0b h0).carrierRange_maximalTranslationPhase_dense
    (analyticNevCarrierFamilyMaximalTranslationInputs h h0b h0)

end

end HTGeometry
