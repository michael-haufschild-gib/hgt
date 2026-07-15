import GaloisForLFunctions.HTGeometry.BernsteinSzegoCaratheodoryRational
import GaloisForLFunctions.HTGeometry.CofinalCholeskyResidualPhase

/-!
# Singular Schur-defect collapse and canonical cofinal approximation

The finite defect used here is the consecutive Toeplitz determinant ratio.  By the exact
Gram--Schmidt identity already proved in the OPUC layer, it is the squared norm of the next monic
orthogonal polynomial, hence the coordinate-free form of `1 - |alpha_N|^2` needed by the card.

This module joins the existing pieces at their strongest proved interfaces:

* infinite support makes every finite defect strictly positive;
* the Riesz-brothers density conclusion and singularity force the defect sequence and normalized
  determinant roots to vanish only cofinally, together with least-eigenvalue and inverse-Cholesky
  escape;
* the canonical Bernstein--Szegő probability measures reproduce each growing Toeplitz section,
  converge weakly, have positive real-analytic densities at every finite stage, concentrate in
  arbitrarily small Haar apertures, and have every finite superlinear `L^p` norm diverge.

The residual singular-continuous maximal-translation phase remains the exact theorem
`ClassicalAnalyticNevanlinnaCarrierFamily.cofinalCholeskyResidualPhase_dense_gdelta_residual`;
it is imported rather than wrapped.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set Topology
open scoped ENNReal Topology

noncomputable section

/-- The finite Schur defect in invariant Toeplitz form.  For an infinite-support circle measure,
this is exactly the squared norm of the next monic OPUC. -/
def circleSchurDefect (mu : Measure Circle) (N : ℕ) : ℝ :=
  consecutiveGramDeterminantRatio (circleMeasureGramTower mu) N

/-- Infinite support keeps every finite Schur defect strictly inside the positive chamber. -/
theorem circleSchurDefect_pos
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    0 < circleSchurDefect mu N := by
  have hdetPos (K : ℕ) : 0 < (circleMeasureGramTower mu K).det.re := by
    have h := (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu K).det_pos
    simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at h
    exact h.1
  exact div_pos (hdetPos (N + 1)) (hdetPos N)

/-- The invariant defect is literally the squared monic-OPUC norm. -/
theorem circleSchurDefect_eq_normSq
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    circleSchurDefect mu N =
      ‖InnerProductSpace.gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2 := by
  exact consecutiveGramDeterminantRatio_eq_normSq mu hmu N

/-- Singular analytic completeness makes the strictly positive finite defects collapse to zero
only at the cofinal boundary. -/
theorem circleSchurDefect_tendsto_zero_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    Tendsto (circleSchurDefect mu) atTop (𝓝 0) := by
  have hcomplete := pureSingular_graph_and_completeness_of_rieszBrothers mu hsing hriesz
  have hszego :=
    hasSzegoFirstLimitConclusion_of_analyticMonomialSpan_dense_of_mutuallySingular
      mu hmu hsing hcomplete.2
  exact consecutiveGramDeterminantRatio_tendsto_zero_of_szego_of_mutuallySingular
    (circleMeasureGramTower mu) mu circleLebesgue hsing hszego

/-- Exact finite-defect/cofinal-collapse package for a singular infinite-support circle carrier. -/
def HasSingularSchurDefectCollapse
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) : Prop :=
  (∀ N, 0 < circleSchurDefect mu N) ∧
    Tendsto (circleSchurDefect mu) atTop (𝓝 0) ∧
    HasSzegoNormalizedGramVanishingConclusion mu ∧
    Tendsto (fun N => leastEigenvalue (circleMeasureGramTower mu N)
      (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N)) atTop (𝓝 0) ∧
    Tendsto (normalizedFrameDetRoot (circleMeasureCanonicalFrameTower mu hmu)) atTop atTop ∧
    Tendsto (euclideanFrameOpNorm (circleMeasureCanonicalFrameTower mu hmu)) atTop atTop

/-- Riesz-brothers density is the sole named classical circle input needed for the complete
finite-interior/cofinal-collapse conclusion. -/
theorem hasSingularSchurDefectCollapse_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    HasSingularSchurDefectCollapse mu hmu := by
  have hcomplete := pureSingular_graph_and_completeness_of_rieszBrothers mu hsing hriesz
  have hszego :=
    hasSzegoFirstLimitConclusion_of_analyticMonomialSpan_dense_of_mutuallySingular
      mu hmu hsing hcomplete.2
  have hroot :=
    hasSzegoNormalizedGramVanishingConclusion_of_classicalSzego mu hmu hsing hszego
  have hescape := circleMeasure_frame_escape_of_szego mu hmu hsing hszego
  exact ⟨circleSchurDefect_pos mu hmu,
    circleSchurDefect_tendsto_zero_of_rieszBrothers mu hmu hsing hriesz,
    hroot, hescape.1, hescape.2.1, hescape.2.2⟩

/-- The complete cofinal approximation conclusion.  It records literal probability measures,
exact finite Gram reconstruction, finite positive analytic interiority, weak convergence, genuine
rational and differential-algebraic Carathéodory transforms, locally uniform transform convergence,
singular aperture concentration, and all finite superlinear `L^p` blow-up. -/
def HasBernsteinSzegoCofinalApproximation
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite) : Prop :=
  Tendsto (bernsteinSzegoProbabilityApproximation mu hmu) atTop (𝓝 mu) ∧
    (∀ N w, ‖w‖ < 1 →
      circleCaratheodoryTransform
          (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w =
        (bernsteinSzegoCaratheodoryNumerator mu hmu N).eval w /
          (bernsteinSzegoCaratheodoryDenominator mu hmu N).eval w) ∧
    (∀ N, GaloisForLFunctions.DifferentiallyAlgebraicOn
      (fun w => circleCaratheodoryTransform
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w)
      {w : ℂ | ‖w‖ < 1}) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      let K := (Metric.closedBall (0 : ℂ) r : Set ℂ)
      Tendsto
        (fun N => UniformFun.ofFun (fun w : K =>
          circleCaratheodoryTransform
            (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) w.1))
        atTop
        (𝓝 (UniformFun.ofFun (fun w : K =>
          circleCaratheodoryTransform (mu : Measure Circle) w.1)))) ∧
    (∀ N, circleMeasureGramTower
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) (N + 1) =
      circleMeasureGramTower (mu : Measure Circle) (N + 1)) ∧
    (∀ N, Continuous (bernsteinSzegoApproximationDensity mu hmu N) ∧
      (∀ z, 0 < bernsteinSzegoApproximationDensity mu hmu N z) ∧
      AnalyticOnNhd ℝ
        (bernsteinSzegoAngularDensity (circleMeasureMomentZ (mu : Measure Circle))
          (circleMeasureGramTower_posDef_of_infiniteSupport
            (mu : Measure Circle) hmu (N + 1))) Set.univ) ∧
    (∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set Circle, IsOpen U ∧ circleLebesgue U < ε ∧
        Tendsto (fun N =>
          (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) U)
          atTop (𝓝 1)) ∧
    (∀ p : ℝ≥0∞, 1 < p → p ≠ ∞ →
      Tendsto (bernsteinSzegoApproximationLpNorm mu hmu p) atTop atTop)

/-- Every singular infinite-support circle probability has the canonical cofinal approximation
package.  No compactness extraction is used: the `L^p` escape is the direct Hölder/concentration
theorem. -/
theorem hasBernsteinSzegoCofinalApproximation_of_mutuallySingular
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (hsing : (mu : Measure Circle) ⟂ₘ circleLebesgue) :
    HasBernsteinSzegoCofinalApproximation mu hmu := by
  refine ⟨bernsteinSzegoProbabilityApproximation_tendsto mu hmu, ?_, ?_, ?_,
    bernsteinSzegoProbabilityApproximation_gram_eq mu hmu, ?_, ?_, ?_⟩
  · intro N w hw
    exact bernsteinSzegoProbabilityApproximation_caratheodory_eq_polynomial_div
      mu hmu N hw
  · intro N
    exact bernsteinSzegoProbabilityApproximation_caratheodory_differentiallyAlgebraicOn_disk
      mu hmu N
  · intro r hr0 hr1
    exact bernsteinSzegoProbabilityApproximation_caratheodory_tendstoUniformly_closedBall
      mu hmu hr0 hr1
  · intro N
    exact ⟨bernsteinSzegoApproximationDensity_continuous mu hmu N,
      bernsteinSzegoApproximationDensity_pos mu hmu N,
      bernsteinSzegoAngularDensity_analyticOnNhd _ _⟩
  · intro ε hε
    exact exists_bernsteinSzegoProbabilityApproximation_concentration_aperture
      mu hmu hsing hε
  · intro p hp hpTop
    exact bernsteinSzegoApproximationLpNorm_tendsto_atTop_of_mutuallySingular
      mu hmu hsing hp hpTop

/-- The card's circle-side double-boundary theorem: every finite defect is strict, all metric
defects collapse only cofinally, and the canonical positive analytic measures converge to the
singular carrier while concentrating with divergent superlinear norms. -/
theorem singularSchurDefect_doubleBoundary_of_rieszBrothers
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (hsing : (mu : Measure Circle) ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion (mu : Measure Circle) circleLebesgue) :
    HasSingularSchurDefectCollapse (mu : Measure Circle) hmu ∧
      HasBernsteinSzegoCofinalApproximation mu hmu := by
  exact ⟨hasSingularSchurDefectCollapse_of_rieszBrothers
      (mu : Measure Circle) hmu hsing hriesz,
    hasBernsteinSzegoCofinalApproximation_of_mutuallySingular mu hmu hsing⟩

end

end GaloisForLFunctions.HTGeometry
