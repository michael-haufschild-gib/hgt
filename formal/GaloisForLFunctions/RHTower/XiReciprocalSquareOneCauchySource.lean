import GaloisForLFunctions.RHTower.XiReciprocalSquareSourceCore

/-!
# Rank-one continued-Cauchy source criterion for the reciprocal-square Xi operator

The reciprocal-square source-core criterion formerly asked for quadratic reality on every finite
algebraic packet of continued Cauchy vectors.  The exact horizontal pole-exhaustion theorem makes
the packet cross-relations unnecessary: every complete Xi multiplicity fibre is a norm limit of
scalar multiples of individual continued-Cauchy vectors.

Consequently it is enough to know quadratic reality separately on each single source vector.  No
polarization, off-diagonal packet relation, zero enumeration, density axiom, or RH assumption is
used in the transfer.  This is a terminal bridge: it isolates a strictly smaller source value
relation but does not prove that relation from the prime--Gamma formula.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Rank-one source condition: the reciprocal-square quadratic value is real on every individual
continued-Cauchy vector.  Unlike the previous source-core hypothesis, no finite sums of distinct
Cauchy vectors occur. -/
def XiReciprocalSquareOneCauchyQuadraticReal : Prop :=
  ∀ z : XiContinuedCauchyPoint,
    inner ℂ
        (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
        (xiWeilContinuedCauchyLp z) =
      inner ℂ
        (xiWeilContinuedCauchyLp z)
        (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))

/-- Quadratic reality on one vector is invariant under arbitrary complex rescaling. -/
theorem xiReciprocalSquare_quadraticReal_smul
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : inner ℂ (xiReciprocalSquareOperator v) v =
      inner ℂ v (xiReciprocalSquareOperator v))
    (c : ℂ) :
    inner ℂ (xiReciprocalSquareOperator (c • v)) (c • v) =
      inner ℂ (c • v) (xiReciprocalSquareOperator (c • v)) := by
  simp only [map_smul, inner_smul_left, inner_smul_right]
  rw [hv]

/-- Rank-one source reality transfers along the explicit horizontal Cauchy-pole exhaustion to the
complete analytic-multiplicity fibre of every Xi divisor point. -/
theorem xiZeroCopyReciprocalSquare_star_eq_of_oneCauchyQuadraticReal
    (hsource : XiReciprocalSquareOneCauchyQuadraticReal)
    (q : XiZeroCopy) :
    (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) =
      xiZeroCopyReciprocalSquare q := by
  let f := xiWeilFiberIndicatorLp (xiSpectralPoint q)
  have hclosed : IsClosed {v |
      inner ℂ (xiReciprocalSquareOperator v) v =
        inner ℂ v (xiReciprocalSquareOperator v)} := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  obtain ⟨c, _hc, _hcap, z, hzform, hzlim⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
      (xiSpectralPoint q) zero_lt_one
  have hdiag : inner ℂ (xiReciprocalSquareOperator f) f =
      inner ℂ f (xiReciprocalSquareOperator f) := by
    apply hclosed.mem_of_tendsto hzlim
    exact Filter.Eventually.of_forall fun n => by
      let zn : XiContinuedCauchyPoint :=
        ⟨z n, ccmContinuedCauchyDomain_of_regular_same_spectral_im q
          (z n).property (by rw [hzform n]; simp [Complex.div_im])⟩
      exact xiReciprocalSquare_quadraticReal_smul (hsource zn)
        (xiSpectralPoint q - (z n : ℂ))
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

/-- Reality of the reciprocal-square quadratic value on every individual continued-Cauchy source
vector forces every Xi divisor point onto the critical line. -/
theorem riemannHypothesis_of_xiReciprocalSquareOneCauchyQuadraticReal
    (hsource : XiReciprocalSquareOneCauchyQuadraticReal) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hstar :=
    xiZeroCopyReciprocalSquare_star_eq_of_oneCauchyQuadraticReal hsource q
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

/-- Under RH the reciprocal-square operator is self-adjoint, so rank-one source reality holds. -/
theorem xiReciprocalSquareOneCauchyQuadraticReal_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiReciprocalSquareOneCauchyQuadraticReal := by
  intro z
  exact (xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis hRH).isSymmetric
    (xiWeilContinuedCauchyLp z) (xiWeilContinuedCauchyLp z)

/-- **Rank-one continued-Cauchy criterion.**  RH is equivalent to quadratic reality separately on
the individual regular continued-Cauchy source vectors; all finite packet cross-relations have
been removed from the hypothesis. -/
theorem xiReciprocalSquareOneCauchyQuadraticReal_iff_riemannHypothesis :
    XiReciprocalSquareOneCauchyQuadraticReal ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalSquareOneCauchyQuadraticReal,
    xiReciprocalSquareOneCauchyQuadraticReal_of_riemannHypothesis⟩

/-- The rank-one condition is genuinely sufficient for the older algebraic packet source-core
interface, by way of RH and the unconditional self-adjointness implication. -/
theorem xiReciprocalSquareContinuedCauchyQuadraticReal_of_oneCauchy
    (hsource : XiReciprocalSquareOneCauchyQuadraticReal) :
    XiReciprocalSquareContinuedCauchyQuadraticReal :=
  xiReciprocalSquareContinuedCauchyQuadraticReal_of_riemannHypothesis
    (riemannHypothesis_of_xiReciprocalSquareOneCauchyQuadraticReal hsource)

end

end RHTower
