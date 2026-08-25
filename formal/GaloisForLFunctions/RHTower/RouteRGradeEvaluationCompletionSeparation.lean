import GaloisForLFunctions.RHTower.ConstitutiveGammaCoronaTailRoosEmbedding
import GaloisForLFunctions.HTGeometry.SourceFaceHyperTorEdge

/-!
# Split grade evaluation versus cofinal completion

The pre-divisor Route-R grade specialization is ordinary evaluation on a function space.  It is
split-surjective, so its algebraic cokernel and the associated one-face `Tor₁` vanish.  Nevertheless
the evaluated Fisher boundary has a nonzero fixed-tail Roos class at every nonneutral physical
grade.  Thus the Route-R defect is created by summability/cofinal completion after specialization,
not by algebraic non-flatness of grade evaluation itself.
-/

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Constant-family section of fixed-grade evaluation. -/
def routeRPrimeGammaConstantGradeSection :
    RouteRTraceSequence →ₗ[ℂ] RouteRPrimeGammaVariableGradeSource where
  toFun a := fun _ => a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem routeRPrimeGammaVariableGradeEvaluation_constantGradeSection
    (t : ℝ) (a : RouteRTraceSequence) :
    routeRPrimeGammaVariableGradeEvaluation t
        (routeRPrimeGammaConstantGradeSection a) = a :=
  rfl

/-- Fixed-grade evaluation is split-surjective before any completion is applied. -/
theorem routeRPrimeGammaVariableGradeEvaluation_comp_constantGradeSection
    (t : ℝ) :
    (routeRPrimeGammaVariableGradeEvaluation t).comp
        routeRPrimeGammaConstantGradeSection = LinearMap.id := by
  ext a n
  rfl

theorem routeRPrimeGammaVariableGradeEvaluation_surjective (t : ℝ) :
    Function.Surjective (routeRPrimeGammaVariableGradeEvaluation t) := by
  intro a
  exact ⟨routeRPrimeGammaConstantGradeSection a, rfl⟩

/-- Algebraic attainment defect of canonical grade evaluation. -/
abbrev RouteRPrimeGammaGradeEvaluationCokernel (t : ℝ) :=
  sourceFaceObservationCokernel (routeRPrimeGammaVariableGradeEvaluation t)

/-- Split grade evaluation has zero algebraic cokernel. -/
theorem routeRPrimeGammaGradeEvaluationCokernel_eq_zero
    (t : ℝ) (q : RouteRPrimeGammaGradeEvaluationCokernel t) : q = 0 := by
  induction q using Quotient.inductionOn with
  | _ a =>
      apply Submodule.Quotient.mk_eq_zero _ |>.2
      exact routeRPrimeGammaVariableGradeEvaluation_surjective t a

/-- Hence every degree-one regular-face Tor class of the evaluation cokernel is zero. -/
theorem routeRPrimeGammaGradeEvaluationTorOne_eq_zero
    (t : ℝ) (x : ℂ)
    (q : regularFaceTor x (RouteRPrimeGammaGradeEvaluationCokernel t) 1) :
    q = 0 := by
  apply Subtype.ext
  exact routeRPrimeGammaGradeEvaluationCokernel_eq_zero t q.1

/-- The specialization is split while its post-specialization fixed-tail obstruction is nonzero.
This locates the exactness failure in summability/cofinal completion, not in algebraic evaluation. -/
theorem routeRPrimeGammaSplitEvaluation_nonzeroTailClass
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    (routeRPrimeGammaVariableGradeEvaluation t).comp
          routeRPrimeGammaConstantGradeSection = LinearMap.id ∧
      routeRDiagonalTailRoosClass
          (routeRPrimeGammaVariableGradeEvaluation t
            routeRPrimeGammaFisherSourceBoundary) ≠ 0 := by
  refine ⟨routeRPrimeGammaVariableGradeEvaluation_comp_constantGradeSection t, ?_⟩
  change routeRDiagonalTailRoosClass
      (routeRPrimeGammaVariableGradeBoundary
        routeRPrimeGammaVariableGradeFisherSource t) ≠ 0
  rw [routeRPrimeGammaVariableGradeBoundary_apply]
  intro hzero
  exact ht0 ((routeRPrimeGammaDiagonalTailRoosClass_eq_zero_iff ht).mp hzero)

/-- Source-marked form of the same separation: split evaluation coexists with a nonzero completion
migration class. -/
theorem routeRPrimeGammaSplitEvaluation_nonzeroCompletionEscape
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    (routeRPrimeGammaVariableGradeEvaluation t).comp
          routeRPrimeGammaConstantGradeSection = LinearMap.id ∧
      routeRPrimeGammaFisherCompletionEscapeClass t ≠ 0 := by
  refine ⟨routeRPrimeGammaVariableGradeEvaluation_comp_constantGradeSection t, ?_⟩
  intro hzero
  exact ht0
    ((routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff ht).mp hzero)

/-- No coefficient-faithful linear realization of the nonneutral completion escape can land in
`Tor₁` of canonical grade evaluation: that Tor carrier is identically zero. -/
theorem no_injective_routeRPrimeGammaFisherEscape_to_gradeEvaluationTorOne
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) (x : ℂ) :
    ¬ ∃ F :
        EscapeDefect (routeRPrimeGammaFixedGradeTailLanding t)
              routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary →ₗ[ℂ]
            regularFaceTor x (RouteRPrimeGammaGradeEvaluationCokernel t) 1,
        Function.Injective F := by
  rintro ⟨F, hF⟩
  have hescape : routeRPrimeGammaFisherCompletionEscapeClass t ≠ 0 := by
    intro hzero
    exact ht0
      ((routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff ht).mp hzero)
  have htor : F (routeRPrimeGammaFisherCompletionEscapeClass t) = 0 :=
    routeRPrimeGammaGradeEvaluationTorOne_eq_zero t x _
  have heq : F (routeRPrimeGammaFisherCompletionEscapeClass t) = F 0 := by
    simpa using htor
  exact hescape (hF heq)

end

end RHTower
