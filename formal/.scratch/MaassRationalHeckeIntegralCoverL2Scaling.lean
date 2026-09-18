import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCoverMeasureScaling

namespace GaloisForLFunctions.RHTower

open MeasureTheory

noncomputable section

/-- The principal Maass source has exact `L²` pullback scaling on every rational
common cover. -/
theorem rationalHeckeIntegralCoverSourceFunction_eLpNorm_eq_scaled
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    eLpNorm (rationalHeckeIntegralCoverSourceFunction N g f) 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) =
      eLpNorm (MaassQuotientL2.sourceFunction N f) 2
        (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
          (rationalHeckeIntegralIntersection N g).subgroupOf
            (CongruenceSubgroup.Gamma (N + 1))) • MaassQuotientL2.quotientMeasure N) := by
  let K := rationalHeckeIntegralIntersection N g
  let Γ := CongruenceSubgroup.Gamma (N + 1)
  letI : K.IsFiniteRelIndex Γ :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  have hKΓ : K ≤ Γ := rationalHeckeIntegralIntersection_le_principal N g
  rw [rationalHeckeIntegralCoverSourceFunction_eq_comp_projection]
  simpa only [K, Γ, rationalHeckeIntegralCoverProjection] using
    eLpNorm_comp_subgroupQuotientProjection K Γ hKΓ
      (MaassQuotientL2.sourceFunction N f) 2
      ((MaassQuotientL2.sourceFunction_memLp N f).aestronglyMeasurable.smul_measure _)

/-- The rational-cover source `L²` admission follows from finite-cover pullback. -/
theorem rationalHeckeIntegralCoverSourceFunction_memLp_by_projection
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MemLp (rationalHeckeIntegralCoverSourceFunction N g f) 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
  let K := rationalHeckeIntegralIntersection N g
  let Γ := CongruenceSubgroup.Gamma (N + 1)
  letI : K.IsFiniteRelIndex Γ :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  have hKΓ : K ≤ Γ := rationalHeckeIntegralIntersection_le_principal N g
  rw [rationalHeckeIntegralCoverSourceFunction_eq_comp_projection]
  simpa only [K, Γ, rationalHeckeIntegralCoverProjection] using
    memLp_comp_subgroupQuotientProjection K Γ hKΓ
      (MaassQuotientL2.sourceFunction N f) 2
      (MaassQuotientL2.sourceFunction_memLp N f)

end

end GaloisForLFunctions.RHTower
