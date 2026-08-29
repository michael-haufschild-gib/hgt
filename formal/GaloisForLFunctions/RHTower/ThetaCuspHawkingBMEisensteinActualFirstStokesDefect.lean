import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualCanonicalMaassWeld
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly

/-!
# Actual first Green--Stokes defect for the balanced Eisenstein vertex

Corpus conjecture C-A.9t3a is the first literal Stokes step after the actual/canonical Maass weld.
For repeated actual completed Poincare leg `F` and projecting leg `G`, the first balanced moment
uses `F^2 G`, while its gradient moment uses `G ((partial_x F)^2 + (partial_y F)^2)`.

This module constructs the genuine product Green current

`J = 2 F G grad F - F^2 grad G`

from actual Poincare jets.  Its divergence has no mixed cross term.  The exact eigen equations
then prove

`2 (gradientDensity - (mu/2-lambda) scalarDensity) = y^2 div J`.

Thus the abstract first Stokes defect in the balanced spin-two coefficient is literally an actual
boundary divergence, with no premise or proxy moment.  The RH chain is

`actual first defect = divergence -> literal truncated Green/Stokes -> full cusp-current finite
part -> actual balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection ->
HC94 -> RH`.
-/

open Complex Real Filter Set Topology

namespace RHTower
noncomputable section

def d4BMActualFirstStokesScalarDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
    d4BMCompletedEisensteinPoincareSeries z Q

def d4BMActualFirstStokesGradientDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.y : ℂ) ^ 2 * d4BMCompletedEisensteinPoincareSeries z Q *
    (d4BMCompletedPoincareHorizontalFirstJet z P ^ 2 +
      d4BMCompletedPoincareVerticalFirstJet z P ^ 2)

def d4BMActualFirstStokesDefectDensity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMHyperbolicFirstStokesDefect
    (P.s * (P.s - 1)) (Q.s * (Q.s - 1))
    (d4BMActualFirstStokesScalarDensity z P Q)
    (d4BMActualFirstStokesGradientDensity z P Q)

def d4BMActualFirstStokesHorizontalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareHorizontalFirstJet z P -
    d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
      d4BMCompletedPoincareHorizontalFirstJet z Q

def d4BMActualFirstStokesVerticalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareVerticalFirstJet z P -
    d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
      d4BMCompletedPoincareVerticalFirstJet z Q

def d4BMActualFirstStokesRadialCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareRadialFirstJet z P -
    d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
      d4BMCompletedPoincareRadialFirstJet z Q

theorem d4BM_actualFirstStokesHorizontalCurrent_translate
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesHorizontalCurrent
        (d4BMEisensteinTranslateCoordinate z) P Q =
      d4BMActualFirstStokesHorizontalCurrent z P Q := by
  unfold d4BMActualFirstStokesHorizontalCurrent
  rw [d4BM_completedEisensteinPoincareSeries_translate z P,
    d4BM_completedEisensteinPoincareSeries_translate z Q,
    d4BM_completedPoincareHorizontalFirstJet_translate z P,
    d4BM_completedPoincareHorizontalFirstJet_translate z Q]

theorem d4BM_actualFirstStokesRadialCurrent_invert_unitCircle
    (z : D4BMUnitSemicircleCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesRadialCurrent
        (d4BMEisensteinInvertCoordinate z.point) P Q =
      -d4BMActualFirstStokesRadialCurrent z.point P Q := by
  unfold d4BMActualFirstStokesRadialCurrent
  rw [d4BM_completedEisensteinPoincareSeries_invert z.point P,
    d4BM_completedEisensteinPoincareSeries_invert z.point Q,
    d4BM_completedPoincareRadialFirstJet_invert_unitCircle z P,
    d4BM_completedPoincareRadialFirstJet_invert_unitCircle z Q]
  ring

def d4BMActualFirstStokesNonCuspPairedDefect
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (d4BMActualFirstStokesHorizontalCurrent
      (d4BMEisensteinTranslateCoordinate B.verticalSide) P Q -
    d4BMActualFirstStokesHorizontalCurrent B.verticalSide P Q) +
  (d4BMActualFirstStokesRadialCurrent
      (d4BMEisensteinInvertCoordinate B.circularArc.point) P Q +
    d4BMActualFirstStokesRadialCurrent B.circularArc.point P Q)

def d4BMActualFirstStokesPairedBoundaryCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMActualFirstStokesVerticalCurrent B.cuspTop P Q +
    d4BMActualFirstStokesNonCuspPairedDefect B P Q

/-- Translation and inversion pair every non-cusp boundary contribution of the actual product
current.  The first Stokes boundary therefore has only its cusp-top survivor. -/
theorem d4BM_actualFirstStokes_nonCuspPairedDefect_eq_zero
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesNonCuspPairedDefect B P Q = 0 := by
  unfold d4BMActualFirstStokesNonCuspPairedDefect
  rw [d4BM_actualFirstStokesHorizontalCurrent_translate,
    d4BM_actualFirstStokesRadialCurrent_invert_unitCircle]
  ring

theorem d4BM_actualFirstStokes_pairedBoundaryCurrent_eq_cuspCurrent
    (B : D4BMTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesPairedBoundaryCurrent B P Q =
      d4BMActualFirstStokesVerticalCurrent B.cuspTop P Q := by
  rw [d4BMActualFirstStokesPairedBoundaryCurrent,
    d4BM_actualFirstStokes_nonCuspPairedDefect_eq_zero]
  simp

abbrev D4BMExteriorTruncatedModularBoundaryPair :=
  {B : D4BMTruncatedModularBoundaryPair // 1 ≤ B.cuspTop.y}

def d4BMExteriorTruncatedBoundaryCuspTop
    (B : D4BMExteriorTruncatedModularBoundaryPair) : D4BMExteriorCuspCoordinate :=
  ⟨B.1.cuspTop, B.2⟩

def d4BMActualFirstStokesHorizontalDivergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareHorizontalFirstJet z P ^ 2 +
    2 * d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareHorizontalSecondJet z P -
    d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
      d4BMCompletedPoincareHorizontalSecondJet z Q

def d4BMActualFirstStokesVerticalDivergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareVerticalFirstJet z P ^ 2 +
    2 * d4BMCompletedEisensteinPoincareSeries z P *
      d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMCompletedPoincareVerticalSecondJet z P -
    d4BMCompletedEisensteinPoincareSeries z P ^ 2 *
      d4BMCompletedPoincareVerticalSecondJet z Q

theorem hasDerivAt_d4BMActualFirstStokesHorizontalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMActualFirstStokesHorizontalCurrent
        (d4BMHorizontalCoordinate z x) P Q)
      (d4BMActualFirstStokesHorizontalDivergence z P Q) z.x := by
  have hF := hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal z P
  have hG := hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal z Q
  have hFx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z P
  have hGx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z Q
  have h := (((hF.const_mul (2 : ℂ)).mul hG).mul hFx).sub ((hF.pow 2).mul hGx)
  have hz : d4BMHorizontalCoordinate z z.x = z := by
    cases z
    rfl
  rw [hz] at h
  simp only [Pi.mul_apply, Pi.pow_apply, hz] at h
  refine h.congr_deriv ?_
  unfold d4BMActualFirstStokesHorizontalDivergence
  ring

def d4BMActualFirstStokesVerticalCurrentSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  2 * d4BMCompletedPoincareVerticalSlice z P y *
      d4BMCompletedPoincareVerticalSlice z Q y *
      d4BMCompletedPoincareVerticalFirstJetSlice z P y -
    d4BMCompletedPoincareVerticalSlice z P y ^ 2 *
      d4BMCompletedPoincareVerticalFirstJetSlice z Q y

theorem d4BM_actualFirstStokesVerticalCurrentSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesVerticalCurrentSlice z P Q z.y =
      d4BMActualFirstStokesVerticalCurrent z P Q := by
  rfl

theorem hasDerivAt_d4BMActualFirstStokesVerticalCurrentSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMActualFirstStokesVerticalCurrentSlice z P Q)
      (d4BMActualFirstStokesVerticalDivergence z P Q) z.y := by
  have hF := hasDerivAt_d4BMCompletedPoincareVerticalSlice z P
  have hG := hasDerivAt_d4BMCompletedPoincareVerticalSlice z Q
  have hFy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z P
  have hGy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z Q
  have h := (((hF.const_mul (2 : ℂ)).mul hG).mul hFy).sub ((hF.pow 2).mul hGy)
  simp only [Pi.mul_apply, Pi.pow_apply,
    d4BMCompletedPoincareVerticalSlice_at_height,
    d4BMCompletedPoincareVerticalFirstJetSlice_at_height] at h
  refine h.congr_deriv ?_
  unfold d4BMActualFirstStokesVerticalDivergence
  ring

/-- The first balanced Stokes defect is exactly the hyperbolic divergence of the genuine actual
product Green current.  Cross derivatives cancel identically; only the two corpus eigen equations
enter. -/
theorem d4BM_actualFirstStokesDefectDensity_eq_divergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    2 * d4BMActualFirstStokesDefectDensity z P Q =
      (z.y : ℂ) ^ 2 *
        (d4BMActualFirstStokesHorizontalDivergence z P Q +
          d4BMActualFirstStokesVerticalDivergence z P Q) := by
  have hP :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P
  have hQ :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z Q
  unfold d4BMActualFirstStokesDefectDensity
    d4BMHyperbolicFirstStokesDefect
    d4BMHyperbolicDiagonalGradientShift
    d4BMActualFirstStokesScalarDensity
    d4BMActualFirstStokesGradientDensity
    d4BMActualFirstStokesHorizontalDivergence
    d4BMActualFirstStokesVerticalDivergence
  linear_combination
    -2 * d4BMCompletedEisensteinPoincareSeries z P *
        d4BMCompletedEisensteinPoincareSeries z Q * hP +
      d4BMCompletedEisensteinPoincareSeries z P ^ 2 * hQ

def d4BMCanonicalFirstStokesHorizontalCurrent
    (u v : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) : ℂ :=
  let Ju := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
  let Jv := d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y
  2 * Ju.first.value * Jv.first.value * Ju.first.horizonX -
    Ju.first.value ^ 2 * Jv.first.horizonX

def d4BMCanonicalFirstStokesVerticalCurrent
    (u v : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) : ℂ :=
  let Ju := d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y
  let Jv := d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y
  2 * Ju.first.value * Jv.first.value * Ju.first.sigma -
    Ju.first.value ^ 2 * Jv.first.sigma

/-- The literal actual horizontal product current is the canonical cusp current throughout the
exterior cusp. -/
theorem d4BM_actualFirstStokesHorizontalCurrent_eq_canonical
    (Z : D4BMExteriorCuspCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesHorizontalCurrent Z.1 P Q =
      d4BMCanonicalFirstStokesHorizontalCurrent
        (P.s - 1 / 2) (Q.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z) := by
  have hP :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z P
  have hQ :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z Q
  unfold d4BMActualFirstStokesHorizontalCurrent
    d4BMCanonicalFirstStokesHorizontalCurrent
  simpa [d4BMActualCompletedPoincareFullSecondJet,
    d4BMActualCompletedPoincareFullFirstJet] using
      congrArg₂ (fun a b : D4BMFullSecondJet =>
        2 * a.first.value * b.first.value * a.first.horizonX -
          a.first.value ^ 2 * b.first.horizonX) hP hQ

/-- The literal actual vertical product current is the canonical cusp current throughout the
exterior cusp. -/
theorem d4BM_actualFirstStokesVerticalCurrent_eq_canonical
    (Z : D4BMExteriorCuspCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesVerticalCurrent Z.1 P Q =
      d4BMCanonicalFirstStokesVerticalCurrent
        (P.s - 1 / 2) (Q.s - 1 / 2) Z.1.x (d4BMExteriorCuspHeight Z) := by
  have hP :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z P
  have hQ :=
    d4BM_actualCompletedPoincareFullSecondJet_eq_canonicalCuspFullSecondJet Z Q
  unfold d4BMActualFirstStokesVerticalCurrent
    d4BMCanonicalFirstStokesVerticalCurrent
  simpa [d4BMActualCompletedPoincareFullSecondJet,
    d4BMActualCompletedPoincareFullFirstJet] using
      congrArg₂ (fun a b : D4BMFullSecondJet =>
        2 * a.first.value * b.first.value * a.first.sigma -
          a.first.value ^ 2 * b.first.sigma) hP hQ

/-- After literal side and arc pairing, the entire actual first-Stokes boundary is the canonical
vertical cusp current. -/
theorem d4BM_actualFirstStokes_pairedBoundaryCurrent_eq_canonicalCuspCurrent
    (B : D4BMExteriorTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesPairedBoundaryCurrent B.1 P Q =
      d4BMCanonicalFirstStokesVerticalCurrent
        (P.s - 1 / 2) (Q.s - 1 / 2) B.1.cuspTop.x
        (d4BMExteriorCuspHeight (d4BMExteriorTruncatedBoundaryCuspTop B)) := by
  rw [d4BM_actualFirstStokes_pairedBoundaryCurrent_eq_cuspCurrent]
  exact d4BM_actualFirstStokesVerticalCurrent_eq_canonical
    (d4BMExteriorTruncatedBoundaryCuspTop B) P Q

def d4BMCanonicalFirstStokesConstantBoundaryCoefficient
    (u v : ℂ) (epsilonOne epsilonTwo epsilonThree : Bool) : ℂ :=
  2 * d4BMCompletedEisensteinCuspConstantCoefficient u epsilonOne *
      d4BMCompletedEisensteinCuspConstantCoefficient u epsilonTwo *
      d4BMCompletedEisensteinCuspWeylExponent u epsilonTwo *
      d4BMCompletedEisensteinCuspConstantCoefficient v epsilonThree -
    d4BMCompletedEisensteinCuspConstantCoefficient u epsilonOne *
      d4BMCompletedEisensteinCuspConstantCoefficient u epsilonTwo *
      d4BMCompletedEisensteinCuspConstantCoefficient v epsilonThree *
      d4BMCompletedEisensteinCuspWeylExponent v epsilonThree

def d4BMCanonicalFirstStokesConstantBoundaryFamily (u v : ℂ) :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  d4BMDiagonalEisensteinCuspBoundaryFamily
    (d4BMCanonicalFirstStokesConstantBoundaryCoefficient u v)

def d4BMEvaluateCuspAffineBoundaryFamily
    (u v : ℂ) (Y : ℝ)
    (F : D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ) : ℂ :=
  Finsupp.linearCombination ℂ
    (fun exponent =>
      (Y : ℂ) ^ d4BMSpecializeDiagonalCuspAffineExponent u v exponent) F

theorem d4BM_evaluateDiagonalCuspBoundaryFamily_eq_boolSum
    (u v : ℂ) (Y : ℝ)
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMEvaluateCuspAffineBoundaryFamily u v Y
        (d4BMDiagonalEisensteinCuspBoundaryFamily coefficient) =
      ∑ epsilonOne : Bool, ∑ epsilonTwo : Bool, ∑ epsilonThree : Bool,
        coefficient epsilonOne epsilonTwo epsilonThree *
          (Y : ℂ) ^ (-1 +
            d4BMCompletedEisensteinCuspWeylExponent u epsilonOne +
            d4BMCompletedEisensteinCuspWeylExponent u epsilonTwo +
            d4BMCompletedEisensteinCuspWeylExponent v epsilonThree) := by
  unfold d4BMEvaluateCuspAffineBoundaryFamily
    d4BMDiagonalEisensteinCuspBoundaryFamily
  simp [d4BM_diagonalCuspBoundaryExponent_specialization]

def d4BMCanonicalCuspConstantVerticalFirstJet (u : ℂ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (-1 : ℂ) *
    (d4BMCompletedEisensteinCuspConstantCoefficient u false *
        d4BMCompletedEisensteinCuspWeylExponent u false *
        (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u false +
      d4BMCompletedEisensteinCuspConstantCoefficient u true *
        d4BMCompletedEisensteinCuspWeylExponent u true *
        (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u true)

def d4BMCanonicalFirstStokesConstantVerticalCurrent
    (u v : ℂ) (Y : ℝ) : ℂ :=
  2 * d4BMCompletedEisensteinCuspConstantPart .scalar u Y *
      d4BMCompletedEisensteinCuspConstantPart .scalar v Y *
      d4BMCanonicalCuspConstantVerticalFirstJet u Y -
    d4BMCompletedEisensteinCuspConstantPart .scalar u Y ^ 2 *
      d4BMCanonicalCuspConstantVerticalFirstJet v Y

theorem d4BM_canonicalCuspConstantVerticalFirstJet_eq_fullSecondJet_sigma
    (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMCanonicalCuspConstantVerticalFirstJet u Y =
      (d4BMCompletedEisensteinCuspConstantFullSecondJet u Y).first.sigma := by
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hpower (w : ℂ) :
      (Y : ℂ) ^ (-1 : ℂ) * (Y : ℂ) ^ w = (Y : ℂ) ^ (w - 1) := by
    rw [← Complex.cpow_add (-1 : ℂ) w hYC]
    congr 1
    ring
  unfold d4BMCanonicalCuspConstantVerticalFirstJet
    d4BMCompletedEisensteinCuspConstantFullSecondJet
    d4BMCompletedEisensteinCuspConstantFirstJetTerm
  simp only
  calc
    (Y : ℂ) ^ (-1 : ℂ) *
        (d4BMCompletedEisensteinCuspConstantCoefficient u false *
            d4BMCompletedEisensteinCuspWeylExponent u false *
            (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u false +
          d4BMCompletedEisensteinCuspConstantCoefficient u true *
            d4BMCompletedEisensteinCuspWeylExponent u true *
            (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u true) =
      d4BMCompletedEisensteinCuspConstantCoefficient u false *
          d4BMCompletedEisensteinCuspWeylExponent u false *
          ((Y : ℂ) ^ (-1 : ℂ) *
            (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u false) +
        d4BMCompletedEisensteinCuspConstantCoefficient u true *
          d4BMCompletedEisensteinCuspWeylExponent u true *
          ((Y : ℂ) ^ (-1 : ℂ) *
            (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u true) := by ring
    _ = d4BMCompletedEisensteinCuspConstantCoefficient u false *
          d4BMCompletedEisensteinCuspWeylExponent u false *
            (Y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false - 1) +
        d4BMCompletedEisensteinCuspConstantCoefficient u true *
          d4BMCompletedEisensteinCuspWeylExponent u true *
            (Y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true - 1) := by
      rw [hpower, hpower]
    _ = _ := by ring

/-- Evaluation of the affine-exponent family is exactly the literal constant-sector first-Stokes
vertical current, not merely a support proxy. -/
theorem d4BM_canonicalFirstStokesConstantVerticalCurrent_eq_familyEvaluation
    (u v : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMCanonicalFirstStokesConstantVerticalCurrent u v Y =
      d4BMEvaluateCuspAffineBoundaryFamily u v Y
        (d4BMCanonicalFirstStokesConstantBoundaryFamily u v) := by
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hpower (a b c : ℂ) :
      (Y : ℂ) ^ (-1 + a + b + c) =
        (Y : ℂ) ^ (-1 : ℂ) * (Y : ℂ) ^ a *
          (Y : ℂ) ^ b * (Y : ℂ) ^ c := by
    rw [show -1 + a + b + c = ((-1 : ℂ) + a) + b + c by ring,
      Complex.cpow_add (((-1 : ℂ) + a) + b) c hYC,
      Complex.cpow_add ((-1 : ℂ) + a) b hYC,
      Complex.cpow_add (-1 : ℂ) a hYC]
  unfold d4BMCanonicalFirstStokesConstantBoundaryFamily
  rw [d4BM_evaluateDiagonalCuspBoundaryFamily_eq_boolSum]
  simp only [Fintype.sum_bool]
  simp_rw [hpower]
  unfold d4BMCanonicalFirstStokesConstantVerticalCurrent
    d4BMCanonicalCuspConstantVerticalFirstJet
    d4BMCanonicalFirstStokesConstantBoundaryCoefficient
    d4BMCompletedEisensteinCuspConstantPart
    d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  ring

/-- No constant-frequency monomial of the genuine first product-current boundary has
spectral-family exponent zero. -/
theorem d4BM_canonicalFirstStokesConstantBoundary_finitePart_zero
    (u v : ℂ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalFirstStokesConstantBoundaryFamily u v) = 0 := by
  exact d4BMCuspAnalyticFamilyFinitePart_diagonalEisensteinBoundary_eq_zero
    (d4BMCanonicalFirstStokesConstantBoundaryCoefficient u v)

/-! ## Source-specific decay of the genuine vertical first jet

The corpus tail estimate allows arbitrary complex height powers but previously covered only
square-root Whittaker values.  The genuine vertical derivative is exactly a three-tail packet:
one order-`nu` term of index degree zero and the two adjacent-order terms of index degree one.
This is the analytic input needed to remove every mixed constant/nonconstant term in the literal
first-Stokes cusp current.
-/

/-- One genuine vertical first-jet summand decomposes into three square-root Whittaker summands.
This is an exact derivative identity, not an asymptotic estimate. -/
theorem d4BM_completedEisensteinSignedSqrtWhittakerVerticalFirstJet_summand_decomposition
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) (N : ℕ) :
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
        u negative N nu x Y =
      (1 / (2 * (Y : ℂ))) *
          d4BMCompletedEisensteinSignedSqrtWhittakerSummand
            u nu negative x 0 0 Y N -
        (Real.pi : ℂ) *
          (d4BMCompletedEisensteinSignedSqrtWhittakerSummand
              u (nu + 1) negative x 1 0 Y N +
            d4BMCompletedEisensteinSignedSqrtWhittakerSummand
              u (nu - 1) negative x 1 0 Y N) := by
  have hY0 : 0 < (Y : ℝ) := zero_lt_one.trans_le Y.2
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hY0)
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0.ne'
  have hsqrt_sq : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = (Y : ℝ) := by
    rw [Real.mul_self_sqrt hY0.le]
  have hsqrt_sqC : ((Real.sqrt (Y : ℝ) : ℂ) ^ 2) = (Y : ℂ) := by
    rw [sq, ← Complex.ofReal_mul, hsqrt_sq]
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
    d4BMSignedWhittakerModeVerticalFirstJet d4BMWhittakerP0FirstJet
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
    d4BMPositiveFourierScale
  simp only [pow_zero, pow_one, mul_one]
  push_cast
  field_simp [hsqrt, hYC]
  rw [hsqrt_sqC]
  field_simp [hYC]
  ring

/-- The full genuine vertical first-jet tail is exactly the same adjacent-order packet after
termwise summation.  Absolute summability on every exterior cusp edge justifies all three
rearrangements. -/
theorem d4BM_completedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_decomposition
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
        u nu negative x Y =
      (1 / (2 * (Y : ℂ))) *
          d4BMCompletedEisensteinSignedSqrtWhittakerTail
            u nu negative x 0 0 Y -
        (Real.pi : ℂ) *
          (d4BMCompletedEisensteinSignedSqrtWhittakerTail
              u (nu + 1) negative x 1 0 Y +
            d4BMCompletedEisensteinSignedSqrtWhittakerTail
              u (nu - 1) negative x 1 0 Y) := by
  let f : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u nu negative x 0 0 Y N
  let g : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u (nu + 1) negative x 1 0 Y N
  let h : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u (nu - 1) negative x 1 0 Y N
  have hf : Summable f :=
    summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u nu negative x 0 0 Y
  have hg : Summable g :=
    summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u (nu + 1) negative x 1 0 Y
  have hh : Summable h :=
    summable_d4BMCompletedEisensteinSignedSqrtWhittakerSummand
      u (nu - 1) negative x 1 0 Y
  have hleft : Summable (fun N => (1 / (2 * (Y : ℂ))) * f N) :=
    hf.mul_left _
  have hright : Summable (fun N => (Real.pi : ℂ) * (g N + h N)) :=
    (hg.add hh).mul_left _
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_summand_tsum,
    d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_summand_tsum,
    d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_summand_tsum]
  change (∑' N : ℕ,
      d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
        u negative N nu x Y) =
    (1 / (2 * (Y : ℂ))) * ∑' N : ℕ, f N -
      (Real.pi : ℂ) * ((∑' N : ℕ, g N) + ∑' N : ℕ, h N)
  calc
    _ = ∑' N : ℕ,
        ((1 / (2 * (Y : ℂ))) * f N -
          (Real.pi : ℂ) * (g N + h N)) := by
      apply tsum_congr
      intro N
      exact
        d4BM_completedEisensteinSignedSqrtWhittakerVerticalFirstJet_summand_decomposition
          u nu negative x Y N
    _ = (∑' N : ℕ, (1 / (2 * (Y : ℂ))) * f N) -
        ∑' N : ℕ, (Real.pi : ℂ) * (g N + h N) :=
      hleft.tsum_sub hright
    _ = _ := by
      rw [tsum_mul_left, tsum_mul_left, hg.tsum_add hh]

def d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail
    (u nu w : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w *
    d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
      u nu negative x Y

/-- Every arbitrary-complex-power-weighted genuine vertical first-jet tail tends to zero at the
cusp.  This closes the new derivative-tail burden required by the literal product-current finite
part; it follows from the exact three-tail decomposition and the corpus's strongest Whittaker
decay theorem. -/
theorem
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail_atTop_zero
    (u nu w : ℂ) (negative : Bool) (x : ℝ) :
    Tendsto
      (d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail
        u nu w negative x)
      atTop (𝓝 0) := by
  have hzero :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u nu (w - 1) negative x 0 0
  have hplus :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u (nu + 1) w negative x 1 0
  have hminus :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u (nu - 1) w negative x 1 0
  have hmain : Tendsto
      (fun Y : ℝ =>
        (1 / 2 : ℂ) *
            d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
              u nu (w - 1) negative x 0 0 Y -
          (Real.pi : ℂ) *
            (d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
                u (nu + 1) w negative x 1 0 Y +
              d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
                u (nu - 1) w negative x 1 0 Y))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hzero).sub
      (tendsto_const_nhds.mul (hplus.add hminus))
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0.ne'
  have hcpow :
      (Y : ℂ) ^ w * (1 / (2 * (Y : ℂ))) =
        (1 / 2 : ℂ) * (Y : ℂ) ^ (w - 1) := by
    rw [show w = (w - 1) + 1 by ring,
      Complex.cpow_add (w - 1) 1 hYC, Complex.cpow_one]
    field_simp [hYC]
    ring
  unfold d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail
  rw [d4BM_completedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_decomposition
    u nu negative x ⟨Y, hY⟩]
  unfold d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
  calc
    (1 / 2 : ℂ) *
          ((Y : ℂ) ^ (w - 1) *
            d4BMCompletedEisensteinSignedSqrtWhittakerTail
              u nu negative x 0 0 Y) -
        (Real.pi : ℂ) *
          ((Y : ℂ) ^ w *
              d4BMCompletedEisensteinSignedSqrtWhittakerTail
                u (nu + 1) negative x 1 0 Y +
            (Y : ℂ) ^ w *
              d4BMCompletedEisensteinSignedSqrtWhittakerTail
                u (nu - 1) negative x 1 0 Y) =
      (((Y : ℂ) ^ w * (1 / (2 * (Y : ℂ)))) *
          d4BMCompletedEisensteinSignedSqrtWhittakerTail
            u nu negative x 0 0 Y) -
        (Real.pi : ℂ) *
          ((Y : ℂ) ^ w *
              d4BMCompletedEisensteinSignedSqrtWhittakerTail
                u (nu + 1) negative x 1 0 Y +
            (Y : ℂ) ^ w *
              d4BMCompletedEisensteinSignedSqrtWhittakerTail
                u (nu - 1) negative x 1 0 Y) := by
        rw [hcpow]
        ring
    _ = _ := by ring

/-- Two-sided nonzero-frequency vertical first jet, including the completed cusp factor `2`. -/
def d4BMCompletedEisensteinCuspVerticalFirstJetTail
    (u : ℂ) (x Y : ℝ) : ℂ :=
  2 *
    (d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
        u u false x Y +
      d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
        u u true x Y)

/-- The full two-sided vertical first-jet tail also beats every fixed complex power. -/
theorem tendsto_d4BMCompletedEisensteinComplexPowerCuspVerticalFirstJetTail_atTop_zero
    (u w : ℂ) (x : ℝ) :
    Tendsto
      (fun Y : ℝ =>
        (Y : ℂ) ^ w * d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y)
      atTop (𝓝 0) := by
  have hp :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail_atTop_zero
      u u w false x
  have hn :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail_atTop_zero
      u u w true x
  have h := (hp.add hn).const_mul (2 : ℂ)
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun Y => by
    unfold d4BMCompletedEisensteinCuspVerticalFirstJetTail
      d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerVerticalFirstJetTail
    ring

/-- The canonical cusp jet's literal vertical component splits into its differentiated Weyl
constant sector and its two-sided differentiated Whittaker tail. -/
theorem d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail
    (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.sigma =
      d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y := by
  rw [d4BM_canonicalCuspConstantVerticalFirstJet_eq_fullSecondJet_sigma
    u (zero_lt_one.trans_le Y.2)]
  rfl

/-- Total-height expression for the canonical vertical first-Stokes cusp current.  It agrees with
the actual canonical jet for every exterior height and remains defined on all real heights so its
cusp limit can be stated directly. -/
def d4BMCanonicalFirstStokesVerticalCuspCurrent
    (u v : ℂ) (x Y : ℝ) : ℂ :=
  2 * d4BMCompletedEisensteinCuspLeg .scalar u x Y *
      d4BMCompletedEisensteinCuspLeg .scalar v x Y *
      (d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) -
    d4BMCompletedEisensteinCuspLeg .scalar u x Y ^ 2 *
      (d4BMCanonicalCuspConstantVerticalFirstJet v Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail v x Y)

theorem d4BM_canonicalFirstStokesVerticalCurrent_eq_totalCuspCurrent
    (u v : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    d4BMCanonicalFirstStokesVerticalCurrent u v x Y =
      d4BMCanonicalFirstStokesVerticalCuspCurrent u v x Y := by
  have huValue := d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg u x Y
  have hvValue := d4BM_canonicalCuspFullSecondJet_value_eq_cuspLeg v x Y
  have huSigma := d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail u x Y
  have hvSigma := d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail v x Y
  change
    2 * (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.value *
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y).first.value *
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.sigma -
        (d4BMCompletedEisensteinCanonicalCuspFullSecondJet u x Y).first.value ^ 2 *
          (d4BMCompletedEisensteinCanonicalCuspFullSecondJet v x Y).first.sigma = _
  unfold d4BMCanonicalFirstStokesVerticalCuspCurrent
  rw [huValue, hvValue, huSigma, hvSigma]

/-- Positive-height form of the constant vertical jet as two differentiated Weyl powers. -/
theorem d4BM_canonicalCuspConstantVerticalFirstJet_eq_termSum
    (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMCanonicalCuspConstantVerticalFirstJet u Y =
      d4BMCompletedEisensteinCuspConstantCoefficient u false *
          d4BMCompletedEisensteinCuspWeylExponent u false *
          (Y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u false - 1) +
        d4BMCompletedEisensteinCuspConstantCoefficient u true *
          d4BMCompletedEisensteinCuspWeylExponent u true *
          (Y : ℂ) ^ (d4BMCompletedEisensteinCuspWeylExponent u true - 1) := by
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hpower (w : ℂ) :
      (Y : ℂ) ^ (-1 : ℂ) * (Y : ℂ) ^ w = (Y : ℂ) ^ (w - 1) := by
    rw [← Complex.cpow_add (-1 : ℂ) w hYC]
    congr 1
    ring
  unfold d4BMCanonicalCuspConstantVerticalFirstJet
  rw [mul_add]
  rw [show (Y : ℂ) ^ (-1 : ℂ) *
        (d4BMCompletedEisensteinCuspConstantCoefficient u false *
          d4BMCompletedEisensteinCuspWeylExponent u false *
          (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u false) =
      d4BMCompletedEisensteinCuspConstantCoefficient u false *
        d4BMCompletedEisensteinCuspWeylExponent u false *
        ((Y : ℂ) ^ (-1 : ℂ) *
          (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u false) by ring,
    show (Y : ℂ) ^ (-1 : ℂ) *
        (d4BMCompletedEisensteinCuspConstantCoefficient u true *
          d4BMCompletedEisensteinCuspWeylExponent u true *
          (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u true) =
      d4BMCompletedEisensteinCuspConstantCoefficient u true *
        d4BMCompletedEisensteinCuspWeylExponent u true *
        ((Y : ℂ) ^ (-1 : ℂ) *
          (Y : ℂ) ^ d4BMCompletedEisensteinCuspWeylExponent u true) by ring,
    hpower, hpower]

/-- Super-polynomial cusp decay against every fixed complex height power. -/
def D4BMCuspRapidDecay (f : ℝ → ℂ) : Prop :=
  ∀ w : ℂ, Tendsto (fun Y : ℝ => (Y : ℂ) ^ w * f Y) atTop (𝓝 0)

theorem d4BMCuspRapidDecay_add {f g : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (hg : D4BMCuspRapidDecay g) :
    D4BMCuspRapidDecay (fun Y => f Y + g Y) := by
  intro w
  have h := (hf w).add (hg w)
  simpa [mul_add] using h

theorem d4BMCuspRapidDecay_sub {f g : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (hg : D4BMCuspRapidDecay g) :
    D4BMCuspRapidDecay (fun Y => f Y - g Y) := by
  intro w
  have h := (hf w).sub (hg w)
  simpa [mul_sub] using h

theorem d4BMCuspRapidDecay_const_mul {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (c : ℂ) :
    D4BMCuspRapidDecay (fun Y => c * f Y) := by
  intro w
  have h := (hf w).const_mul c
  simpa only [mul_zero] using h.congr' (Filter.Eventually.of_forall fun Y => by ring)

/-- Rapid cusp decay is multiplicatively closed; it is an ideal inside functions of at most
finite-power growth. -/
theorem d4BMCuspRapidDecay_mul {f g : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (hg : D4BMCuspRapidDecay g) :
    D4BMCuspRapidDecay (fun Y => f Y * g Y) := by
  intro w
  have h := (hf w).mul (hg 0)
  simp only [mul_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun Y => by simp; ring

theorem d4BMCuspRapidDecay_cuspTailPart
    (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (d4BMCompletedEisensteinCuspTailPart kind u x) := by
  intro w
  exact d4BM_tendsto_cpow_cuspTailPart kind u w x

theorem d4BMCuspRapidDecay_verticalFirstJetTail
    (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay (d4BMCompletedEisensteinCuspVerticalFirstJetTail u x) := by
  intro w
  exact tendsto_d4BMCompletedEisensteinComplexPowerCuspVerticalFirstJetTail_atTop_zero
    u w x

/-- Multiplication by either completed Weyl constant term preserves rapid cusp decay. -/
theorem d4BMCuspRapidDecay_mul_constantPart {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f)
    (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) :
    D4BMCuspRapidDecay
      (fun Y => f Y * d4BMCompletedEisensteinCuspConstantPart kind u Y) := by
  intro w
  let wm := d4BMCompletedEisensteinCuspWeylExponent u false
  let wp := d4BMCompletedEisensteinCuspWeylExponent u true
  let cm := d4BMCompletedEisensteinCuspConstantCoefficient u false *
    d4BMCompletedEisensteinCuspConstantMaassFactor kind wm
  let cp := d4BMCompletedEisensteinCuspConstantCoefficient u true *
    d4BMCompletedEisensteinCuspConstantMaassFactor kind wp
  have hm := (hf (w + wm)).const_mul cm
  have hp := (hf (w + wp)).const_mul cp
  have h := hm.add hp
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  dsimp [d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, cm, cp, wm, wp]
  rw [Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent u false) hYC,
    Complex.cpow_add w (d4BMCompletedEisensteinCuspWeylExponent u true) hYC]
  ring

/-- Multiplication by the literal differentiated Weyl constant sector also preserves rapid cusp
decay. -/
theorem d4BMCuspRapidDecay_mul_constantVerticalFirstJet {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (u : ℂ) :
    D4BMCuspRapidDecay
      (fun Y => f Y * d4BMCanonicalCuspConstantVerticalFirstJet u Y) := by
  intro w
  let wm := d4BMCompletedEisensteinCuspWeylExponent u false
  let wp := d4BMCompletedEisensteinCuspWeylExponent u true
  let cm := d4BMCompletedEisensteinCuspConstantCoefficient u false * wm
  let cp := d4BMCompletedEisensteinCuspConstantCoefficient u true * wp
  have hm := (hf (w + (wm - 1))).const_mul cm
  have hp := (hf (w + (wp - 1))).const_mul cp
  have h := hm.add hp
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [d4BM_canonicalCuspConstantVerticalFirstJet_eq_termSum u hY]
  dsimp [cm, cp, wm, wp]
  rw [Complex.cpow_add w
      (d4BMCompletedEisensteinCuspWeylExponent u false - 1) hYC,
    Complex.cpow_add w
      (d4BMCompletedEisensteinCuspWeylExponent u true - 1) hYC]
  ring

theorem d4BMCuspRapidDecay_congr {f g : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f) (hfg : ∀ Y, f Y = g Y) :
    D4BMCuspRapidDecay g := by
  intro w
  apply (hf w).congr'
  exact Filter.Eventually.of_forall fun Y => by
    change (Y : ℂ) ^ w * f Y = (Y : ℂ) ^ w * g Y
    rw [hfg Y]

/-- A rapidly decaying function remains rapidly decaying after multiplication by a full cusp leg:
the constant sector has finite power growth and the tail sector is itself rapidly decaying. -/
theorem d4BMCuspRapidDecay_mul_cuspLeg {f : ℝ → ℂ}
    (hf : D4BMCuspRapidDecay f)
    (kind : D4BMCompletedEisensteinCuspLegKind) (u : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay
      (fun Y => f Y * d4BMCompletedEisensteinCuspLeg kind u x Y) := by
  have hc := d4BMCuspRapidDecay_mul_constantPart hf kind u
  have ht := d4BMCuspRapidDecay_mul hf
    (d4BMCuspRapidDecay_cuspTailPart kind u x)
  apply d4BMCuspRapidDecay_congr (d4BMCuspRapidDecay_add hc ht)
  intro Y
  unfold d4BMCompletedEisensteinCuspLeg
  ring

def d4BMCanonicalFirstStokesVerticalMixedRemainder
    (u v : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCanonicalFirstStokesVerticalCuspCurrent u v x Y -
    d4BMCanonicalFirstStokesConstantVerticalCurrent u v Y

/-- Four-block expansion of the full first-Stokes mixed cusp sector.  Each block contains a
nonconstant scalar or differentiated Whittaker tail. -/
theorem d4BM_canonicalFirstStokesVertical_mixedSectorExpansion
    (u v : ℂ) (x Y : ℝ) :
    d4BMCanonicalFirstStokesVerticalMixedRemainder u v x Y =
      2 *
        ((d4BMCompletedEisensteinCuspLeg .scalar u x Y *
                d4BMCompletedEisensteinCuspLeg .scalar v x Y -
              d4BMCompletedEisensteinCuspConstantPart .scalar u Y *
                d4BMCompletedEisensteinCuspConstantPart .scalar v Y) *
            d4BMCanonicalCuspConstantVerticalFirstJet u Y +
          d4BMCompletedEisensteinCuspLeg .scalar u x Y *
            d4BMCompletedEisensteinCuspLeg .scalar v x Y *
            d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) -
        ((d4BMCompletedEisensteinCuspLeg .scalar u x Y ^ 2 -
              d4BMCompletedEisensteinCuspConstantPart .scalar u Y ^ 2) *
            d4BMCanonicalCuspConstantVerticalFirstJet v Y +
          d4BMCompletedEisensteinCuspLeg .scalar u x Y ^ 2 *
            d4BMCompletedEisensteinCuspVerticalFirstJetTail v x Y) := by
  simp [d4BMCanonicalFirstStokesVerticalMixedRemainder,
    d4BMCanonicalFirstStokesVerticalCuspCurrent,
    d4BMCanonicalFirstStokesConstantVerticalCurrent]
  ring

/-- The complete mixed constant/nonconstant sector of the genuine first-Stokes vertical current
is rapidly decaying.  This simultaneously controls all twelve expanded mixed terms. -/
theorem d4BMCuspRapidDecay_canonicalFirstStokesVerticalMixedRemainder
    (u v : ℂ) (x : ℝ) :
    D4BMCuspRapidDecay
      (d4BMCanonicalFirstStokesVerticalMixedRemainder u v x) := by
  have hTu := d4BMCuspRapidDecay_cuspTailPart .scalar u x
  have hTv := d4BMCuspRapidDecay_cuspTailPart .scalar v x
  have hEu := d4BMCuspRapidDecay_verticalFirstJetTail u x
  have hEv := d4BMCuspRapidDecay_verticalFirstJetTail v x

  have hTuFv := d4BMCuspRapidDecay_mul_cuspLeg hTu .scalar v x
  have hTvCu := d4BMCuspRapidDecay_mul_constantPart hTv .scalar u
  have hAraw := d4BMCuspRapidDecay_add hTuFv hTvCu
  have hA : D4BMCuspRapidDecay (fun Y =>
      d4BMCompletedEisensteinCuspLeg .scalar u x Y *
          d4BMCompletedEisensteinCuspLeg .scalar v x Y -
        d4BMCompletedEisensteinCuspConstantPart .scalar u Y *
          d4BMCompletedEisensteinCuspConstantPart .scalar v Y) := by
    apply d4BMCuspRapidDecay_congr hAraw
    intro Y
    unfold d4BMCompletedEisensteinCuspLeg
    ring
  have hADu := d4BMCuspRapidDecay_mul_constantVerticalFirstJet hA u

  have hEuFu := d4BMCuspRapidDecay_mul_cuspLeg hEu .scalar u x
  have hEuFuFv := d4BMCuspRapidDecay_mul_cuspLeg hEuFu .scalar v x
  have hFuFvEu : D4BMCuspRapidDecay (fun Y =>
      d4BMCompletedEisensteinCuspLeg .scalar u x Y *
        d4BMCompletedEisensteinCuspLeg .scalar v x Y *
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y) := by
    apply d4BMCuspRapidDecay_congr hEuFuFv
    intro Y
    ring

  have hTuFu := d4BMCuspRapidDecay_mul_cuspLeg hTu .scalar u x
  have hTuCu := d4BMCuspRapidDecay_mul_constantPart hTu .scalar u
  have hBraw := d4BMCuspRapidDecay_add hTuFu hTuCu
  have hB : D4BMCuspRapidDecay (fun Y =>
      d4BMCompletedEisensteinCuspLeg .scalar u x Y ^ 2 -
        d4BMCompletedEisensteinCuspConstantPart .scalar u Y ^ 2) := by
    apply d4BMCuspRapidDecay_congr hBraw
    intro Y
    unfold d4BMCompletedEisensteinCuspLeg
    ring
  have hBDv := d4BMCuspRapidDecay_mul_constantVerticalFirstJet hB v

  have hEvFu := d4BMCuspRapidDecay_mul_cuspLeg hEv .scalar u x
  have hEvFuFu := d4BMCuspRapidDecay_mul_cuspLeg hEvFu .scalar u x
  have hFuFuEv : D4BMCuspRapidDecay (fun Y =>
      d4BMCompletedEisensteinCuspLeg .scalar u x Y ^ 2 *
        d4BMCompletedEisensteinCuspVerticalFirstJetTail v x Y) := by
    apply d4BMCuspRapidDecay_congr hEvFuFu
    intro Y
    ring

  have hpositive := d4BMCuspRapidDecay_const_mul
    (d4BMCuspRapidDecay_add hADu hFuFvEu) (2 : ℂ)
  have hnegative := d4BMCuspRapidDecay_add hBDv hFuFuEv
  have hblocks := d4BMCuspRapidDecay_sub hpositive hnegative
  apply d4BMCuspRapidDecay_congr hblocks
  intro Y
  rw [d4BM_canonicalFirstStokesVertical_mixedSectorExpansion]

/-- The genuine first-Stokes mixed cusp current tends to zero. -/
theorem tendsto_d4BMCanonicalFirstStokesVerticalMixedRemainder_atTop_zero
    (u v : ℂ) (x : ℝ) :
    Tendsto (d4BMCanonicalFirstStokesVerticalMixedRemainder u v x)
      atTop (𝓝 0) := by
  have h := d4BMCuspRapidDecay_canonicalFirstStokesVerticalMixedRemainder u v x 0
  simpa using h

/-- Full first-Stokes cusp closure: the literal constant-sector current has zero analytic-family
finite part and the entire nonconstant remainder vanishes at the cusp. -/
theorem d4BM_canonicalFirstStokes_fullCuspCurrentClosure
    (u v : ℂ) (x : ℝ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalFirstStokesConstantBoundaryFamily u v) = 0 ∧
      Tendsto (d4BMCanonicalFirstStokesVerticalMixedRemainder u v x)
        atTop (𝓝 0) :=
  ⟨d4BM_canonicalFirstStokesConstantBoundary_finitePart_zero u v,
    tendsto_d4BMCanonicalFirstStokesVerticalMixedRemainder_atTop_zero u v x⟩

/-- Exact actual boundary decomposition: after literal side/arc pairing, the remaining current is
the differentiated Weyl constant sector plus the rapidly decaying mixed remainder. -/
theorem d4BM_actualFirstStokes_pairedBoundaryCurrent_decomposition
    (B : D4BMExteriorTruncatedModularBoundaryPair)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesPairedBoundaryCurrent B.1 P Q =
      d4BMCanonicalFirstStokesConstantVerticalCurrent
          (P.s - 1 / 2) (Q.s - 1 / 2) B.1.cuspTop.y +
        d4BMCanonicalFirstStokesVerticalMixedRemainder
          (P.s - 1 / 2) (Q.s - 1 / 2)
          B.1.cuspTop.x B.1.cuspTop.y := by
  rw [d4BM_actualFirstStokes_pairedBoundaryCurrent_eq_canonicalCuspCurrent,
    d4BM_canonicalFirstStokesVerticalCurrent_eq_totalCuspCurrent]
  unfold d4BMCanonicalFirstStokesVerticalMixedRemainder
  simp [d4BMExteriorCuspHeight, d4BMExteriorTruncatedBoundaryCuspTop]

/-- Actual-parameter first-Stokes cusp closure.  Together with the preceding exact decomposition,
this removes every boundary finite part after the non-cusp sides have paired. -/
theorem d4BM_actualFirstStokes_fullCuspBoundaryClosure
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    d4BMCuspAnalyticFamilyFinitePart
        (d4BMCanonicalFirstStokesConstantBoundaryFamily
          (P.s - 1 / 2) (Q.s - 1 / 2)) = 0 ∧
      Tendsto
        (d4BMCanonicalFirstStokesVerticalMixedRemainder
          (P.s - 1 / 2) (Q.s - 1 / 2) x)
        atTop (𝓝 0) :=
  d4BM_canonicalFirstStokes_fullCuspCurrentClosure
    (P.s - 1 / 2) (Q.s - 1 / 2) x

end
end RHTower
