import GaloisForLFunctions.HTGeometry.CompletionDefectExactnessFlag
import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos

/-!
# Route R completion migration defect

The complete reflected-minus-forward Fisher family is a literal boundary before a modular grade is
fixed.  Fixed-grade tail completion need not preserve that boundary.  This file constructs the
resulting boundary-migration class without assuming its vanishing.

The construction makes the "zero as completion error" statement exact:

* the pre-divisor Fisher defect is always in the source boundary space;
* fixed-grade specialization followed by the tail mismatch is a linear landing;
* its escape class vanishes exactly when the fixed-tail Roos class vanishes;
* on an actual Xi support point, the class survives in the target provenance-exactness flag exactly
  off the critical line;
* global absence of these surviving completion defects is equivalent to RH.

Thus no zero is produced by the construction.  An off-line zero would witness failure of one
source boundary to remain a boundary under the canonical fixed-grade completion.
-/

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Sequence space in which the fixed-tail Roos difference takes its values. -/
abbrev RouteRTailRoosAmbient :=
  ∀ _n : ℕ, routeRSummableSequenceIdeal

/-- Target boundary space: global Roos coboundaries in the fixed summable tail ideal. -/
def routeRTailRoosBoundary : Submodule ℂ RouteRTailRoosAmbient :=
  LinearMap.range
    (inverseDifference (fun _ : ℕ => routeRSummableSequenceIdeal)
      routeRTailRoosRestrictedBond)

/-- Target exactness flag.  A vector survives precisely when it has no summable Roos primitive. -/
def routeRTailRoosExactnessFlag : ExFlag ℂ RouteRTailRoosAmbient :=
  boundaryExactnessFlag routeRTailRoosBoundary

/-- The diagonal tail mismatch, packaged as a linear map into the Roos sequence space. -/
def routeRDiagonalMismatchLinear :
    RouteRTraceSequence →ₗ[ℂ] RouteRTailRoosAmbient where
  toFun := routeRDiagonalMismatchInIdeal
  map_add' x y := by
    funext n
    apply Subtype.ext
    funext k
    change routeRDiagonalMismatch (x + y) n k =
      routeRDiagonalMismatch x n k + routeRDiagonalMismatch y n k
    cases k with
    | zero => simp; abel
    | succ k => simp
  map_smul' c x := by
    funext n
    apply Subtype.ext
    funext k
    change routeRDiagonalMismatch (c • x) n k =
      c • routeRDiagonalMismatch x n k
    cases k with
    | zero => simp
    | succ k => simp

/-- Fixed-grade evaluation of the complete pre-divisor source. -/
def routeRPrimeGammaVariableGradeEvaluation (t : ℝ) :
    RouteRPrimeGammaVariableGradeSource →ₗ[ℂ] RouteRTraceSequence where
  toFun f := f t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical source-to-completion landing: fix the grade, then form the diagonal tail mismatch. -/
def routeRPrimeGammaFixedGradeTailLanding (t : ℝ) :
    RouteRPrimeGammaVariableGradeSource →ₗ[ℂ]
      RouteRTailRoosAmbient :=
  routeRDiagonalMismatchLinear.comp
    (routeRPrimeGammaVariableGradeEvaluation t)

/-- Literal reflected-minus-forward Fisher boundary before any Xi fibre is selected. -/
def routeRPrimeGammaFisherSourceBoundary :
    RouteRPrimeGammaVariableGradeSource :=
  routeRPrimeGammaVariableGradeBoundary
    routeRPrimeGammaVariableGradeFisherSource

/-- The Fisher boundary is unconditionally a member of the pre-divisor source boundary space. -/
theorem routeRPrimeGammaFisherSourceBoundary_mem :
    routeRPrimeGammaFisherSourceBoundary ∈
      routeRPrimeGammaVariableGradeBoundarySpace := by
  exact ⟨routeRPrimeGammaVariableGradeFisherSource, rfl⟩

/-- Landing the literal source boundary gives the coefficient-faithful fixed-tail mismatch. -/
theorem routeRPrimeGammaFixedGradeTailLanding_fisherBoundary
    (t : ℝ) :
    routeRPrimeGammaFixedGradeTailLanding t
        routeRPrimeGammaFisherSourceBoundary =
      routeRDiagonalMismatchInIdeal
        (routeRPrimeGammaBocksteinSequence t) := by
  change routeRDiagonalMismatchInIdeal
      (routeRPrimeGammaVariableGradeBoundary
        routeRPrimeGammaVariableGradeFisherSource t) = _
  rw [routeRPrimeGammaVariableGradeBoundary_apply]

/-- Completion-error class of the literal Fisher source boundary at a fixed modular grade. -/
def routeRPrimeGammaFisherCompletionEscapeClass (t : ℝ) :
    EscapeDefect (routeRPrimeGammaFixedGradeTailLanding t)
      routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary :=
  boundaryEscapeClass (routeRPrimeGammaFixedGradeTailLanding t)
    routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary
    routeRPrimeGammaFisherSourceBoundary
    routeRPrimeGammaFisherSourceBoundary_mem

/-- The migration class and the fixed-tail Roos class are the same exactness failure. -/
theorem routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff_roos
    (t : ℝ) :
    routeRPrimeGammaFisherCompletionEscapeClass t = 0 ↔
      routeRDiagonalTailRoosClass
        (routeRPrimeGammaBocksteinSequence t) = 0 := by
  rw [routeRPrimeGammaFisherCompletionEscapeClass,
    boundaryEscapeClass_eq_zero_iff,
    routeRPrimeGammaFixedGradeTailLanding_fisherBoundary,
    routeRDiagonalTailRoosClass, Submodule.Quotient.mk_eq_zero]
  rfl

/-- In the physical strip, the completion-error class vanishes exactly at neutral grade. -/
theorem routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    routeRPrimeGammaFisherCompletionEscapeClass t = 0 ↔ t = 0 :=
  (routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff_roos t).trans
    (routeRPrimeGammaDiagonalTailRoosClass_eq_zero_iff ht)

/-- The actual Xi completion-error class, obtained only after the source construction is fixed. -/
def routeRPrimeGammaXiCompletionEscapeClass (rho : XiDivisorSupport) :=
  routeRPrimeGammaFisherCompletionEscapeClass
    (2 * (rho : ℂ).re - 1)

/-- An actual Xi completion error vanishes exactly on the critical line. -/
theorem routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiCompletionEscapeClass rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiCompletionEscapeClass,
    routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff
      (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> linarith

/-- Exact topological-defect statement: the completed source boundary survives in the target flag
precisely when the Xi support point is off the critical line. -/
theorem routeRPrimeGammaXiCompletionDefect_survives_iff_re_ne_half
    (rho : XiDivisorSupport) :
    routeRTailRoosExactnessFlag ∈ ExFlag.survival
        (routeRPrimeGammaFixedGradeTailLanding
          (2 * (rho : ℂ).re - 1)
          routeRPrimeGammaFisherSourceBoundary) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  change boundaryExactnessFlag routeRTailRoosBoundary ∈ ExFlag.survival
      (routeRPrimeGammaFixedGradeTailLanding
        (2 * (rho : ℂ).re - 1)
        routeRPrimeGammaFisherSourceBoundary) ↔ _
  rw [← boundaryEscapeClass_ne_zero_iff_survival
    (routeRPrimeGammaFixedGradeTailLanding
      (2 * (rho : ℂ).re - 1))
    routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary
    routeRPrimeGammaFisherSourceBoundary
    routeRPrimeGammaFisherSourceBoundary_mem]
  change routeRPrimeGammaXiCompletionEscapeClass rho ≠ 0 ↔ _
  rw [ne_eq, routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half]

/-- Global statement that canonical fixed-grade completion creates no surviving physical defect. -/
def RouteRPrimeGammaXiGlobalCompletionEscapeFree : Prop :=
  ∀ rho : XiDivisorSupport,
    routeRPrimeGammaXiCompletionEscapeClass rho = 0

/-- Exact completion-error endpoint: global absence of the constructed escape classes is RH. -/
theorem routeRPrimeGammaXiGlobalCompletionEscapeFree_iff_riemannHypothesis :
    RouteRPrimeGammaXiGlobalCompletionEscapeFree ↔ RiemannHypothesis := by
  constructor
  · intro hescape
    apply
      routeRPrimeGammaXiGlobalDiagonalTailRoosNullHomology_iff_riemannHypothesis.mp
    intro rho
    exact
      (routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff_roos
        (2 * (rho : ℂ).re - 1)).mp (hescape rho)
  · intro hRH rho
    apply
      (routeRPrimeGammaFisherCompletionEscapeClass_eq_zero_iff_roos
        (2 * (rho : ℂ).re - 1)).mpr
    exact
      routeRPrimeGammaXiGlobalDiagonalTailRoosNullHomology_iff_riemannHypothesis.mpr
        hRH rho

/-- Equivalent topological form: RH says no actual Xi source boundary survives the completion flag. -/
theorem riemannHypothesis_iff_no_routeRPrimeGammaXiCompletionDefect_survives :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        routeRTailRoosExactnessFlag ∉ ExFlag.survival
          (routeRPrimeGammaFixedGradeTailLanding
            (2 * (rho : ℂ).re - 1)
            routeRPrimeGammaFisherSourceBoundary) := by
  rw [← routeRPrimeGammaXiGlobalCompletionEscapeFree_iff_riemannHypothesis]
  constructor
  · intro h rho hsurv
    exact
      (routeRPrimeGammaXiCompletionDefect_survives_iff_re_ne_half rho).mp
        hsurv
        ((routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).mp
          (h rho))
  · intro h rho
    by_contra hne
    have hre : (rho : ℂ).re ≠ 1 / 2 := by
      intro hre
      exact hne
        ((routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).2 hre)
    exact h rho
      ((routeRPrimeGammaXiCompletionDefect_survives_iff_re_ne_half rho).2 hre)

end

end RHTower
