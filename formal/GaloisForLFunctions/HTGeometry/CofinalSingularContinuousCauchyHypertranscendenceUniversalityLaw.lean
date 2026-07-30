import GaloisForLFunctions.HTGeometry.CofinalCholeskyResidualPhase

/-!
# Cofinal singular-continuous Cauchy hypertranscendence universality

The global cofinal Cholesky phase already identifies singular-continuous carriers carrying maximal
translation-differential freeness.  Every point of the carrier range also has a projective
barycentric representation.  Viewing that parameter law through its constant unit `L∞` density
connects intrinsic freeness to literal Cauchy hypertranscendence.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory OnePoint Set
open scoped ENNReal OnePoint

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- **Cofinal singular-continuous Cauchy hypertranscendence law.**  Every carrier in the global
cofinal phase is atomless and Lebesgue-singular, is intrinsically free under every finite
translated differential pattern, and has a literally hypertranscendental Cauchy transform. -/
theorem cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation_hypertranscendental
    (hC : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d univ)
    (nu : F.base.toBoundaryFamily.carrierRange)
    (hnu : nu ∈ F.cofinalCholeskyResidualPhase) :
    NullSingletonClass (nu.1 : Measure ℝ) ∧
      (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) ∧
      MaximalTranslationDifferentialFree nu.1 ∧
      Hypertranscendental
        (fun z => ∫ x, ((x : ℂ) - z)⁻¹ ∂(nu.1 : Measure ℝ)) := by
  let BF := F.base.toBoundaryFamily
  have hstructure :=
    F.cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation hC hD nu hnu
  obtain ⟨eta, heta⟩ := nu.property
  let mu : Measure (OnePoint ℝ) := eta
  letI : IsProbabilityMeasure mu := eta.prop
  have hpositive : LinftyStrictlyPositive mu (linftyOne mu) :=
    linftyOne_strictlyPositive mu
  have hintegral : ∫ x, (linftyOne mu) x ∂mu = 1 := by
    rw [← linftyIntegralCLM_apply]
    exact linftyIntegralCLM_linftyOne mu
  have hdensity :
      linftyDensityProbabilityMeasure mu (linftyOne mu) hpositive hintegral = eta := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa [mu, linftyDensityProbabilityMeasure] using
      (linftyDensityMeasure_linftyOne mu)
  have hcarrier :
      weightedBoundaryProbabilityCarrier BF mu (linftyOne mu) hpositive hintegral = nu.1 := by
    rw [weightedBoundaryProbabilityCarrier, hdensity, heta]
  have hfree : MaximalTranslationDifferentialFree
      (weightedBoundaryProbabilityCarrier BF mu (linftyOne mu) hpositive hintegral) := by
    rw [hcarrier]
    exact hstructure.2.2
  have hht := F.hypertranscendental_weightedBoundaryProbabilityCarrierCauchy
    mu (linftyOne mu) hpositive hintegral hfree
  refine ⟨hstructure.1, hstructure.2.1, hstructure.2.2, ?_⟩
  rw [hcarrier] at hht
  exact hht

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
