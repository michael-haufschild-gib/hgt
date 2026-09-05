import GaloisForLFunctions.HTGeometry.HorizontalLayerProjective
import GaloisForLFunctions.HTGeometry.ProjectiveBoundaryMultiplier
import GaloisForLFunctions.HTGeometry.HardyHorizontalLayerLeakage

open Filter Topology

set_option maxHeartbeats 800000

namespace GaloisForLFunctions.HTGeometry

theorem projectiveBoundaryMul_horizontalLayerInfinitesimalProjective
    {a : ℝ} (ha : 0 < a) :
    projectiveBoundaryMul (horizontalLayerInfinitesimalProjective a) =
      infinitesimalBlaschkeMul a ha + infinitesimalBlaschkeInvMul a := by
  apply ContinuousLinearMap.ext
  intro f
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_projectiveBoundaryMul
      (horizontalLayerInfinitesimalProjective a) f,
    coeFn_infinitesimalBlaschkeMul ha f,
    coeFn_infinitesimalBlaschkeInvMul ha f,
    MeasureTheory.Lp.coeFn_add (infinitesimalBlaschkeMul a ha f)
      (infinitesimalBlaschkeInvMul a f)] with x hP hB hI hadd
  rw [hP]
  change horizontalLayerInfinitesimalProjective a (x : OnePoint ℝ) *
      (f : ℝ → ℂ) x =
    ((((infinitesimalBlaschkeMul a ha + infinitesimalBlaschkeInvMul a) f :
      RealLineL2) : ℝ → ℂ) x)
  rw [add_apply, hadd, Pi.add_apply, hB, hI,
    horizontalLayerInfinitesimalProjective_coe ha.ne']
  unfold horizontalLayerFullInfinitesimalSymbol infinitesimalBlaschkeSymbol
    infinitesimalBlaschkeInvSymbol
  ring

theorem hardyLeakage_horizontalLayerInfinitesimalProjective {a : ℝ} (ha : 0 < a) :
    hardyLeakage (projectiveBoundaryMul (horizontalLayerInfinitesimalProjective a)) =
      (-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
          (lowerCauchyFeature a ha) := by
  rw [projectiveBoundaryMul_horizontalLayerInfinitesimalProjective ha]
  rw [hardyLeakage_add (infinitesimalBlaschkeMul a ha)
    (infinitesimalBlaschkeInvMul a), hardyLeakage_infinitesimalBlaschkeMul ha,
    hardyLeakage_infinitesimalBlaschkeInvMul ha, add_zero]

theorem tendsto_projectiveBoundaryMul_finiteHorizontalLayerNormalizedProjective
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    Tendsto
      (fun ω => projectiveBoundaryMul (finiteHorizontalLayerNormalizedProjective s a ω))
      (𝓝[≠] 0)
      (𝓝 (projectiveBoundaryMul (finiteHorizontalLayerInfinitesimalProjective s a))) := by
  have h := tendsto_finiteHorizontalLayerNormalizedProjective s a ha
  exact projectiveBoundaryMulCLM.continuous.continuousAt.tendsto.comp h

theorem tendsto_hardyLeakage_finiteHorizontalLayerNormalizedProjective
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    Tendsto
      (fun ω => hardyLeakage
        (projectiveBoundaryMul (finiteHorizontalLayerNormalizedProjective s a ω)))
      (𝓝[≠] 0)
      (𝓝 (hardyLeakage
        (projectiveBoundaryMul (finiteHorizontalLayerInfinitesimalProjective s a)))) := by
  exact tendsto_hardyLeakage
    (tendsto_projectiveBoundaryMul_finiteHorizontalLayerNormalizedProjective s a ha)

theorem hardyLeakage_zero :
    hardyLeakage (0 : RealLineL2 →L[ℂ] RealLineL2) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  simp [hardyLeakage]

theorem projectiveBoundaryMul_zero :
    projectiveBoundaryMul (0 : ProjectiveBoundary) = 0 := by
  change projectiveBoundaryMulCLM 0 = 0
  exact map_zero projectiveBoundaryMulCLM

theorem hardyLeakage_sum {ι : Type*} (s : Finset ι)
    (M : ι → (RealLineL2 →L[ℂ] RealLineL2)) :
    hardyLeakage (s.sum M) = s.sum fun i => hardyLeakage (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hardyLeakage_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, hardyLeakage_add (M i) (s.sum M), ih,
        Finset.sum_insert hi]

theorem hardyLeakage_finiteHorizontalLayerInfinitesimalProjective
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    hardyLeakage (projectiveBoundaryMul (finiteHorizontalLayerInfinitesimalProjective s a)) =
      s.sum fun i => (-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature (a i) (ha i))
          (lowerCauchyFeature (a i) (ha i)) := by
  classical
  have hm :
      projectiveBoundaryMul
          (s.sum fun i => horizontalLayerInfinitesimalProjective (a i)) =
        s.sum fun i =>
          projectiveBoundaryMul (horizontalLayerInfinitesimalProjective (a i)) := by
    change projectiveBoundaryMulCLM
        (s.sum fun i => horizontalLayerInfinitesimalProjective (a i)) =
      s.sum fun i => projectiveBoundaryMulCLM
        (horizontalLayerInfinitesimalProjective (a i))
    exact map_sum projectiveBoundaryMulCLM _ _
  rw [finiteHorizontalLayerInfinitesimalProjective, hm,
    hardyLeakage_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hardyLeakage_horizontalLayerInfinitesimalProjective (ha i)

end GaloisForLFunctions.HTGeometry
