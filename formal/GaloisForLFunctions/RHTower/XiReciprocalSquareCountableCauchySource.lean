import GaloisForLFunctions.RHTower.XiReciprocalSquareOneCauchySource
import GaloisForLFunctions.RHTower.XiContinuedCauchyGaussianRatDensity

/-!
# Countable reciprocal-square Cauchy source criterion for RH

The rank-one reciprocal-square criterion can be reduced to the countable family of regular
Gaussian-rational poles in the centered strip.  The countable Cauchy density theorem approximates
each continued-source vector in norm, and quadratic reality is a closed condition.

Thus the remaining source obligation is a countable scalar value family.  No finite packets,
mixed coefficients, zero enumeration, density axiom, RH assumption, or limiting measure enters
the forward implication.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Countable scalar source condition: reciprocal-square quadratic reality is tested only at
regular Gaussian-rational poles in the centered open strip. -/
def XiReciprocalSquareGaussianRatCauchyQuadraticReal : Prop :=
  ∀ q : XiGaussianRatContinuedCauchyPoint,
    inner ℂ
        (xiReciprocalSquareOperator
          (xiWeilGaussianRatContinuedCauchyLp q))
        (xiWeilGaussianRatContinuedCauchyLp q) =
      inner ℂ
        (xiWeilGaussianRatContinuedCauchyLp q)
        (xiReciprocalSquareOperator
          (xiWeilGaussianRatContinuedCauchyLp q))

/-- The scalar orientation defect at one regular Gaussian-rational source pole. -/
def xiReciprocalSquareGaussianRatOrientationDefect
    (q : XiGaussianRatContinuedCauchyPoint) : ℝ :=
  (inner ℂ
    (xiReciprocalSquareOperator (xiWeilGaussianRatContinuedCauchyLp q))
    (xiWeilGaussianRatContinuedCauchyLp q)).im

/-- Pointwise vanishing of the scalar orientation defect is exactly reciprocal-square quadratic
reality at that Gaussian-rational source pole. -/
theorem xiReciprocalSquareGaussianRatOrientationDefect_eq_zero_iff
    (q : XiGaussianRatContinuedCauchyPoint) :
    xiReciprocalSquareGaussianRatOrientationDefect q = 0 ↔
      inner ℂ
          (xiReciprocalSquareOperator
            (xiWeilGaussianRatContinuedCauchyLp q))
          (xiWeilGaussianRatContinuedCauchyLp q) =
        inner ℂ
          (xiWeilGaussianRatContinuedCauchyLp q)
          (xiReciprocalSquareOperator
            (xiWeilGaussianRatContinuedCauchyLp q)) := by
  rw [← inner_conj_symm
    (xiWeilGaussianRatContinuedCauchyLp q)
    (xiReciprocalSquareOperator (xiWeilGaussianRatContinuedCauchyLp q))]
  unfold xiReciprocalSquareGaussianRatOrientationDefect
  constructor
  · intro him
    exact (Complex.conj_eq_iff_im.mpr him).symm
  · intro heq
    exact Complex.conj_eq_iff_im.mp heq.symm

/-- Vanishing of the complete countable scalar orientation-defect family. -/
def XiReciprocalSquareGaussianRatOrientationDefectsVanish : Prop :=
  ∀ q : XiGaussianRatContinuedCauchyPoint,
    xiReciprocalSquareGaussianRatOrientationDefect q = 0

/-- The countable defect family vanishes exactly when the countable quadratic values are real. -/
theorem xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_quadraticReal :
    XiReciprocalSquareGaussianRatOrientationDefectsVanish ↔
      XiReciprocalSquareGaussianRatCauchyQuadraticReal := by
  constructor
  · intro h q
    exact (xiReciprocalSquareGaussianRatOrientationDefect_eq_zero_iff q).mp (h q)
  · intro h q
    exact (xiReciprocalSquareGaussianRatOrientationDefect_eq_zero_iff q).mpr (h q)

/-- Gaussian-rational scalar reality extends to every individual continued-Cauchy source vector. -/
theorem xiReciprocalSquareOneCauchyQuadraticReal_of_gaussianRat
    (hsource : XiReciprocalSquareGaussianRatCauchyQuadraticReal) :
    XiReciprocalSquareOneCauchyQuadraticReal := by
  intro z
  have hclosed : IsClosed {v |
      inner ℂ (xiReciprocalSquareOperator v) v =
        inner ℂ v (xiReciprocalSquareOperator v)} := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  obtain ⟨q, _hpoint, hlim⟩ :=
    exists_gaussianRatContinuedCauchyLp_tendsto z
  apply hclosed.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n ↦ hsource (q n)

/-- **Countable source chain to RH.**  Reciprocal-square quadratic reality on the countable
Gaussian-rational Cauchy family forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiReciprocalSquareGaussianRatCauchyQuadraticReal
    (hsource : XiReciprocalSquareGaussianRatCauchyQuadraticReal) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiReciprocalSquareOneCauchyQuadraticReal
    (xiReciprocalSquareOneCauchyQuadraticReal_of_gaussianRat hsource)

/-- RH makes the reciprocal-square operator self-adjoint, hence supplies every countable scalar
Gaussian-rational test. -/
theorem xiReciprocalSquareGaussianRatCauchyQuadraticReal_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiReciprocalSquareGaussianRatCauchyQuadraticReal := by
  intro q
  exact (xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis hRH).isSymmetric
    (xiWeilGaussianRatContinuedCauchyLp q)
    (xiWeilGaussianRatContinuedCauchyLp q)

/-- Exact countable scalar continued-source criterion for RH. -/
theorem xiReciprocalSquareGaussianRatCauchyQuadraticReal_iff_riemannHypothesis :
    XiReciprocalSquareGaussianRatCauchyQuadraticReal ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalSquareGaussianRatCauchyQuadraticReal,
    xiReciprocalSquareGaussianRatCauchyQuadraticReal_of_riemannHypothesis⟩

/-- **Countable scalar defect criterion.**  RH is equivalent to the vanishing of one explicitly
defined real orientation defect at every regular Gaussian-rational pole in the centered strip. -/
theorem xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_riemannHypothesis :
    XiReciprocalSquareGaussianRatOrientationDefectsVanish ↔ RiemannHypothesis :=
  xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_quadraticReal.trans
    xiReciprocalSquareGaussianRatCauchyQuadraticReal_iff_riemannHypothesis

/-- The countable condition discharges the former uncountable rank-one source interface. -/
theorem xiReciprocalSquareContinuedCauchyQuadraticReal_of_gaussianRat
    (hsource : XiReciprocalSquareGaussianRatCauchyQuadraticReal) :
    XiReciprocalSquareContinuedCauchyQuadraticReal :=
  xiReciprocalSquareContinuedCauchyQuadraticReal_of_oneCauchy
    (xiReciprocalSquareOneCauchyQuadraticReal_of_gaussianRat hsource)

end

end RHTower
