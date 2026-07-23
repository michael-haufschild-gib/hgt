import GaloisForLFunctions.HTGeometry.CofinalSingularContinuousCauchyHypertranscendenceUniversalityLaw
import GaloisForLFunctions.HTGeometry.CarrierHerglotzPresentationFree
import GaloisForLFunctions.HTGeometry.CauchyHerglotzLocalGlobalHypertranscendenceUniversalityLaw

/-!
# Cofinal singular-continuous Cauchy--Herglotz local/global universality

Every carrier in the cofinal Cholesky residual phase is intrinsically maximally free under finite
translated differential patterns.  Re-expressing that carrier through its constant-density
projective barycenter turns intrinsic freeness into upper-half-plane relation-freeness for its
Cauchy transform.  Polynomial Nevanlinna gauge transport then gives the same local and global
conclusions for every normalized Herglotz presentation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory OnePoint Set
open scoped ENNReal OnePoint

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- **Cofinal singular-continuous Cauchy--Herglotz local/global universality law.**  Every carrier
in the global cofinal phase is atomless, singular, and maximally translation-differentially free.
Its Cauchy transform and every normalized Herglotz presentation are relation-free on the upper
half-plane and literally hypertranscendental on `ℂ`. -/
theorem
    cofinalCholeskyResidualPhase_singularContinuous_cauchyHerglotzLocalGlobalUniversality
    (hC : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c univ)
    (hD : AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d univ)
    (nu : F.base.toBoundaryFamily.carrierRange)
    (hnu : nu ∈ F.cofinalCholeskyResidualPhase) :
    NoAtoms (nu.1 : Measure ℝ) ∧
      (nu.1 : Measure ℝ) ⟂ₘ (volume : Measure ℝ) ∧
      MaximalTranslationDifferentialFree nu.1 ∧
      (¬ DifferentiallyAlgebraicOn
        (cauchyTransform (nu.1 : Measure ℝ)) upperHalfPlane) ∧
      (∀ M : ℂ, ¬ DifferentiallyAlgebraicOn
        (fun z => z * M + (1 + z ^ 2) *
          cauchyTransform (nu.1 : Measure ℝ) z) upperHalfPlane) ∧
      Hypertranscendental (cauchyTransform (nu.1 : Measure ℝ)) ∧
      ∀ M : ℂ, Hypertranscendental
        (fun z => z * M + (1 + z ^ 2) *
          cauchyTransform (nu.1 : Measure ℝ) z) := by
  let BF := F.base.toBoundaryFamily
  have hstructure :=
    F.cofinalCholeskyResidualPhase_isSingularContinuous_maximalTranslation
      hC hD nu hnu
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
  have hactual : ∀ (p : FiniteDifferentialPattern Unit)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      F.weightedBoundaryCarrierExpandedPatternRelationHolds
        (row := CarrierPatternRow p) mu (linftyOne mu)
          p.coefficientDegree p.orders (carrierPatternExponent p) shift coeff →
        ∀ col, coeff col = 0 := by
    intro p shift coeff hrel
    exact hfree p shift coeff hrel
  have hcauchyWeighted :=
    F.not_differentiallyAlgebraicOn_cauchyTransform_weightedBoundaryCarrier
      mu (linftyOne mu) hactual
  have hcauchy :
      ¬ DifferentiallyAlgebraicOn
        (cauchyTransform (nu.1 : Measure ℝ)) upperHalfPlane := by
    rw [← hcarrier]
    exact hcauchyWeighted
  have hlocalH : ∀ M : ℂ, ¬ DifferentiallyAlgebraicOn
      (fun z => z * M + (1 + z ^ 2) *
        cauchyTransform (nu.1 : Measure ℝ) z) upperHalfPlane := by
    intro M
    exact not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane
      (nu.1 : Measure ℝ) M hcauchy
  have hglobal :=
    cauchyHerglotz_upperHalfPlane_globalHypertranscendence
      (nu.1 : Measure ℝ) hcauchy
  exact ⟨hstructure.1, hstructure.2.1, hstructure.2.2,
    hcauchy, hlocalH, hglobal⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
