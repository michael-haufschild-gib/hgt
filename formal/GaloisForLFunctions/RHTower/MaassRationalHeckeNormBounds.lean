import GaloisForLFunctions.RHTower.MaassRationalHeckeCorrespondenceL2
import GaloisForLFunctions.RHTower.MaassRationalHeckeAdjoint

/-!
# Square-root degree bounds for rational Hecke correspondences

The finite-fibre trace is the Hilbert adjoint of finite-cover pullback. Its
operator norm is therefore at most the square root of the fibre degree.
Composing with the principal-side pullback gives a bound by the geometric mean
of the two cover degrees, including on every actual Maass source vector.

This is a whole-space correspondence bound. It does not supply the additional
cancellation on cusp forms needed for the Ramanujan-Petersson bound.
-/

open MeasureTheory Matrix
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower

/-- Adjointness gives the square-root-degree operator bound for the finite trace. -/
theorem rationalHeckeConjugateFiberTraceLpContinuousLinear_norm_le_sqrt_card
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    ‖rationalHeckeConjugateFiberTraceLpContinuousLinear N g‖ ≤
      Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) := by
  rw [← ContinuousLinearMap.adjoint.norm_map
    (rationalHeckeConjugateFiberTraceLpContinuousLinear N g),
    rationalHeckeConjugateFiberTraceLpContinuousLinear_adjoint]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  exact (norm_rationalHeckeConjugateCoverPullbackLp N g u).le

theorem rationalHeckeConjugateFiberTraceLp_norm_le_sqrt_card_mul
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (u : Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    ‖rationalHeckeConjugateFiberTraceLp N g u‖ ≤
      Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) * ‖u‖ := by
  exact (rationalHeckeConjugateFiberTraceLpContinuousLinear N g).le_opNorm u |>.trans
    (mul_le_mul_of_nonneg_right
      (rationalHeckeConjugateFiberTraceLpContinuousLinear_norm_le_sqrt_card N g)
      (norm_nonneg _))

/-- The full common-cover correspondence costs the geometric mean of its two degrees. -/
theorem rationalHeckePrincipalToConjugateLpContinuousLinear_norm_le
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (u : Lp ℂ 2 (MaassQuotientL2.quotientMeasure N)) :
    ‖rationalHeckePrincipalToConjugateLpContinuousLinear N g u‖ ≤
      Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) *
      Real.sqrt (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
        (rationalHeckeIntegralIntersection N g).subgroupOf
          (CongruenceSubgroup.Gamma (N + 1))) : ℝ) * ‖u‖ := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  change ‖rationalHeckeConjugateFiberTraceLp N g
    (integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
      (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g) u)‖ ≤ _
  refine (rationalHeckeConjugateFiberTraceLp_norm_le_sqrt_card_mul N g _).trans_eq ?_
  rw [norm_integralFiniteCoverPullbackLp, mul_assoc]

/-- The degree bound applies to the identified trace of an actual Maass cusp form. -/
theorem rationalHeckeConjugateFiberTraceSourceLp_norm_le
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ‖rationalHeckeConjugateFiberTraceSourceLp N g f‖ ≤
      Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ℝ) *
      Real.sqrt (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
        (rationalHeckeIntegralIntersection N g).subgroupOf
          (CongruenceSubgroup.Gamma (N + 1))) : ℝ) * ‖MaassQuotientL2.sourceLp N f‖ := by
  rw [← rationalHeckePrincipalToConjugateLpContinuousLinear_source N g f]
  exact rationalHeckePrincipalToConjugateLpContinuousLinear_norm_le N g _

end GaloisForLFunctions.RHTower
