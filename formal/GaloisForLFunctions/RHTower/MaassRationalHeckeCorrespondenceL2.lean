import GaloisForLFunctions.RHTower.MaassFiniteCoverPullbackL2
import GaloisForLFunctions.RHTower.SelbergMaassFiniteFiberIntegration

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The common-cover Maass vector is exactly finite-cover pullback of the
principal quotient vector. -/
theorem rationalHeckeIntegralCoverSourceLp_eq_finiteCoverPullback
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
        rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
    integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
      (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g)
      (MaassQuotientL2.sourceLp N f) =
      rationalHeckeIntegralCoverSourceLp N g f := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  have hsource := (MaassQuotientL2.sourceLp_ae N f).comp_tendsto
    (integralFiniteCoverProjection_quasiMeasurePreserving
      (rationalHeckeIntegralIntersection N g) (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g)).tendsto_ae
  apply Lp.ext
  filter_upwards [coe_integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
      (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g) (MaassQuotientL2.sourceLp N f),
    (rationalHeckeIntegralCoverSourceFunction_memLp N g f).coeFn_toLp, hsource] with q hpull hcover hsource
  rw [hpull]
  change MaassQuotientL2.sourceLp N f (rationalHeckeIntegralCoverProjection N g q) =
    rationalHeckeIntegralCoverSourceLp N g f q
  unfold rationalHeckeIntegralCoverSourceLp
  rw [hcover]
  change MaassQuotientL2.sourceLp N f
      (subgroupQuotientProjection (realImage (rationalHeckeIntegralIntersection N g))
        (realImage (CongruenceSubgroup.Gamma (N + 1)))
        (Subgroup.map_mono (rationalHeckeIntegralIntersection_le_principal N g)) q) =
    rationalHeckeIntegralCoverSourceFunction N g f q
  have hsource' : MaassQuotientL2.sourceLp N f
      (subgroupQuotientProjection (realImage (rationalHeckeIntegralIntersection N g))
        (realImage (CongruenceSubgroup.Gamma (N + 1)))
        (Subgroup.map_mono (rationalHeckeIntegralIntersection_le_principal N g)) q) =
      MaassQuotientL2.sourceFunction N f
        (subgroupQuotientProjection (realImage (rationalHeckeIntegralIntersection N g))
          (realImage (CongruenceSubgroup.Gamma (N + 1)))
          (Subgroup.map_mono (rationalHeckeIntegralIntersection_le_principal N g)) q) := by
    simpa only [Function.comp_apply] using hsource
  rw [hsource']
  exact (congrFun (rationalHeckeIntegralCoverSourceFunction_eq_comp_projection N g f) q).symm

/-- The rational common-cover correspondence is a bounded complex-linear map
from the principal quotient Hilbert space to the rational-conjugate quotient Hilbert space. -/
noncomputable def rationalHeckePrincipalToConjugateLpContinuousLinear (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (MaassQuotientL2.quotientMeasure N) →L[ℂ]
      Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  exact (rationalHeckeConjugateFiberTraceLpContinuousLinear N g).comp
    (integralFiniteCoverPullbackLpContinuousLinear (rationalHeckeIntegralIntersection N g)
      (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g))

/-- On the actual Maass source, the bounded correspondence is the already
identified bounded common-cover fiber trace. -/
theorem rationalHeckePrincipalToConjugateLpContinuousLinear_source
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
        rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
    rationalHeckePrincipalToConjugateLpContinuousLinear N g
      (MaassQuotientL2.sourceLp N f) =
      rationalHeckeConjugateFiberTraceSourceLp N g f := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  unfold rationalHeckePrincipalToConjugateLpContinuousLinear
  change rationalHeckeConjugateFiberTraceLp N g
    (integralFiniteCoverPullbackLp (rationalHeckeIntegralIntersection N g)
      (CongruenceSubgroup.Gamma (N + 1))
      (rationalHeckeIntegralIntersection_le_principal N g)
      (MaassQuotientL2.sourceLp N f)) = _
  rw [rationalHeckeIntegralCoverSourceLp_eq_finiteCoverPullback N g f]
  rfl

end

end GaloisForLFunctions.RHTower
