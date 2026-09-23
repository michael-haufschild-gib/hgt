import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure

/-!
# Reciprocal-square Xi operator on the continued Cauchy source core

Squaring the compact reciprocal Xi divisor operator removes the sign of each centered spectral
coordinate.  For a general complex operator, self-adjointness of the square is strictly weaker
than self-adjointness of the operator.  On the actual Xi divisor the remaining square ambiguity is
excluded by the open critical-strip geometry: a real reciprocal-square coordinate is equivalent
to a critical-line zero.

The full operator condition can be weakened further.  It suffices that the quadratic values of the
square be real on the algebraic Cauchy span lying in the analytically continued prime--Gamma source
domain.  The unconditional Cauchy closure theorem puts every exact multiplicity fiber in the
closure of that span, and closedness transfers quadratic reality to those fibers.

These are terminal bridge theorems, not a source proof of the required quadratic-value relation.
The reciprocal operator remains indexed by the actual Xi divisor.
-/

open Complex
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- The square of the compact reciprocal Xi divisor operator. -/
def xiReciprocalSquareOperator :
    lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiReciprocalOperator ∘L xiReciprocalOperator

/-- The reciprocal Xi operator acts by coordinatewise reciprocal spectral multiplication on every
`ell^(2 : ℕ)` vector, not only on basis vectors. -/
theorem xiReciprocalOperator_apply
    (f : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiReciprocalOperator f q = (xiSpectralPoint q)⁻¹ * f q := by
  classical
  rw [xiReciprocalOperator, HilbertSchmidt.toOperator_apply]
  rw [tsum_eq_single q]
  · simp [xiReciprocalDiagonalKernel, diagMul]
  · intro r hr
    simp [xiReciprocalDiagonalKernel, diagMul, Ne.symm hr]

/-- The squared reciprocal operator has the centered reciprocal-square coordinate as its exact
pointwise multiplier. -/
theorem xiReciprocalSquareOperator_apply
    (f : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiReciprocalSquareOperator f q =
      xiZeroCopyReciprocalSquare q * f q := by
  rw [xiReciprocalSquareOperator, ContinuousLinearMap.comp_apply,
    xiReciprocalOperator_apply, xiReciprocalOperator_apply,
    xiZeroCopyReciprocalSquare]
  ring

/-- Exact squared reciprocal eigenvalue on a canonical basis vector. -/
theorem xiReciprocalSquareOperator_single (q : XiZeroCopy) :
    xiReciprocalSquareOperator (lp.single 2 q (1 : ℂ)) =
      xiZeroCopyReciprocalSquare q • lp.single 2 q (1 : ℂ) := by
  rw [xiReciprocalSquareOperator, ContinuousLinearMap.comp_apply,
    xiReciprocalOperator_single, map_smul, xiReciprocalOperator_single,
    smul_smul, xiZeroCopyReciprocalSquare]
  ring_nf

/-- Every complete analytic-multiplicity fiber is an eigenvector of the reciprocal-square
operator. -/
theorem xiReciprocalSquareOperator_fiberIndicator (q : XiZeroCopy) :
    xiReciprocalSquareOperator
        (xiWeilFiberIndicatorLp (xiSpectralPoint q)) =
      xiZeroCopyReciprocalSquare q •
        xiWeilFiberIndicatorLp (xiSpectralPoint q) := by
  apply Subtype.ext
  funext r
  rw [xiReciprocalSquareOperator_apply]
  by_cases hrq : xiSpectralPoint r = xiSpectralPoint q
  · simp [xiWeilFiberIndicatorLp_apply,
      xiZeroCopyReciprocalSquare, hrq]
  · simp [xiWeilFiberIndicatorLp_apply, hrq]

/-- Self-adjointness of the squared reciprocal operator makes each squared reciprocal spectral
coordinate real. -/
theorem xiZeroCopyReciprocalSquare_star_eq_of_squareOperator_isSelfAdjoint
    (hself : IsSelfAdjoint xiReciprocalSquareOperator) (q : XiZeroCopy) :
    (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) =
      xiZeroCopyReciprocalSquare q := by
  have hdiag := hself.isSymmetric
    (lp.single 2 q (1 : ℂ)) (lp.single 2 q (1 : ℂ))
  change inner ℂ
      (xiReciprocalSquareOperator (lp.single 2 q (1 : ℂ)))
      (lp.single 2 q (1 : ℂ)) =
    inner ℂ (lp.single 2 q (1 : ℂ))
      (xiReciprocalSquareOperator (lp.single 2 q (1 : ℂ))) at hdiag
  rw [xiReciprocalSquareOperator_single] at hdiag
  simpa [lp.inner_single_left, lp.inner_single_right] using hdiag

/-- Self-adjointness of the square of the reciprocal Xi operator forces RH. -/
theorem riemannHypothesis_of_xiReciprocalSquareOperator_isSelfAdjoint
    (hself : IsSelfAdjoint xiReciprocalSquareOperator) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hstar :=
    xiZeroCopyReciprocalSquare_star_eq_of_squareOperator_isSelfAdjoint hself q
  have him := congrArg Complex.im hstar
  have him0 : (xiZeroCopyReciprocalSquare q).im = 0 := by
    have him' : -(xiZeroCopyReciprocalSquare q).im =
        (xiZeroCopyReciprocalSquare q).im := by
      simpa using him
    linarith
  rw [xiZeroCopyReciprocalSquare_eq] at him0
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him0
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [xiSpectralPoint, hre]

/-- RH makes the reciprocal operator self-adjoint and therefore also makes its square
self-adjoint. -/
theorem xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    IsSelfAdjoint xiReciprocalSquareOperator := by
  have hR := xiReciprocalOperator_isSelfAdjoint_of_rh hRH
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [xiReciprocalSquareOperator, ContinuousLinearMap.adjoint_comp,
    hR.adjoint_eq]

/-- Exact reciprocal-square operator criterion for RH.  This condition is weaker than
self-adjointness of the unsquared operator in the ambient category of complex operators. -/
theorem xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis :
    IsSelfAdjoint xiReciprocalSquareOperator ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalSquareOperator_isSelfAdjoint,
    xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis⟩

/-- The source-core condition: reciprocal-square quadratic values are real only on the algebraic
Cauchy span inside the analytically continued prime--Gamma domain. -/
def XiReciprocalSquareContinuedCauchyQuadraticReal : Prop :=
  ∀ v ∈ xiWeilContinuedCauchyAlgebraicSubspace,
    inner ℂ (xiReciprocalSquareOperator v) v =
      inner ℂ v (xiReciprocalSquareOperator v)

/-- Source-core quadratic reality transfers through the unconditional Cauchy closure to the exact
multiplicity fiber of every Xi divisor point, making its reciprocal-square coordinate real. -/
theorem xiZeroCopyReciprocalSquare_star_eq_of_continuedCauchyQuadraticReal
    (hsource : XiReciprocalSquareContinuedCauchyQuadraticReal)
    (q : XiZeroCopy) :
    (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) =
      xiZeroCopyReciprocalSquare q := by
  let f := xiWeilFiberIndicatorLp (xiSpectralPoint q)
  have hclosed : IsClosed {v |
      inner ℂ (xiReciprocalSquareOperator v) v =
        inner ℂ v (xiReciprocalSquareOperator v)} := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hf : f ∈ closure
      (↑xiWeilContinuedCauchyAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    exact xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace q
  have hdiag : inner ℂ (xiReciprocalSquareOperator f) f =
      inner ℂ f (xiReciprocalSquareOperator f) :=
    (closure_minimal hsource hclosed) hf
  rw [xiReciprocalSquareOperator_fiberIndicator] at hdiag
  have hfne : f ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun v => v q) hzero
    change xiWeilFiberIndicatorLp (xiSpectralPoint q) q = (0 : ℂ) at hcoord
    simp only [xiWeilFiberIndicatorLp_apply] at hcoord
    exact one_ne_zero hcoord
  have hinnerne : inner ℂ f f ≠ 0 := inner_self_ne_zero.mpr hfne
  simp only [inner_smul_left, inner_smul_right] at hdiag
  exact mul_right_cancel₀ hinnerne hdiag

/-- Source-core quadratic reality transfers to every exact divisor-multiplicity fiber and forces
RH. -/
theorem riemannHypothesis_of_xiReciprocalSquareContinuedCauchyQuadraticReal
    (hsource : XiReciprocalSquareContinuedCauchyQuadraticReal) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hstar :=
    xiZeroCopyReciprocalSquare_star_eq_of_continuedCauchyQuadraticReal hsource q
  have him := congrArg Complex.im hstar
  have him0 : (xiZeroCopyReciprocalSquare q).im = 0 := by
    have him' : -(xiZeroCopyReciprocalSquare q).im =
        (xiZeroCopyReciprocalSquare q).im := by
      simpa using him
    linarith
  rw [xiZeroCopyReciprocalSquare_eq] at him0
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him0
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [xiSpectralPoint, hre]

/-- Under RH the square is self-adjoint, so its quadratic value is real on the entire carrier and
in particular on the continued source core. -/
theorem xiReciprocalSquareContinuedCauchyQuadraticReal_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiReciprocalSquareContinuedCauchyQuadraticReal := by
  intro v _hv
  exact (xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis hRH).isSymmetric v v

/-- **Continued source-core criterion.**  It is enough to orient the squared reciprocal operator
on the concrete algebraic continued-Cauchy span; no all-carrier self-adjointness or density axiom
is required. -/
theorem xiReciprocalSquareContinuedCauchyQuadraticReal_iff_riemannHypothesis :
    XiReciprocalSquareContinuedCauchyQuadraticReal ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalSquareContinuedCauchyQuadraticReal,
    xiReciprocalSquareContinuedCauchyQuadraticReal_of_riemannHypothesis⟩

end

end RHTower
