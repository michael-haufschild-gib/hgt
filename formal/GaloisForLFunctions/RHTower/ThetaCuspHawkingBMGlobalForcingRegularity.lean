import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalSmoothForcing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalCutoffLaplacian

/-!
Every compact localization of the actual global forcing has a Schwartz representative and every Sobolev order.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open scoped ContDiff ENNReal SchwartzMap
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse GaloisForLFunctions.HTGeometry
noncomputable section

/-- The actual globally smooth forcing localized by an arbitrary compact positive-height test. -/
def PlanarChartTest.globalForcingTest (g : PlanarChartTest) (q : XiZeroCopy) (branch : Bool) :
    PlanarChartTest where
  field z := g.field z*globalForcing q branch (ofComplex z)
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · have hy := g.support hz
      have hf := globalForcing_smooth q branch (ofComplex z)
      rw [ofComplex_apply_of_im_pos hy] at hf
      exact g.smooth.contDiffAt.mul hf
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  compact := g.compact.mul_right
  support := (closure_mono (Function.support_mul_subset_left _ _)).trans g.support

private theorem global_ae_to_planar {P : ℂ → Prop}
    (hP : ∀ᵐ z : UpperHalfPlane ∂volume, P (z:ℂ)) :
    ∀ᵐ z ∂((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}), P z := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane), P z :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr hP
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  filter_upwards [hh,ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
  apply hz
  simp [chartDensity,ne_of_gt hy]

/-- Every compact planar localization identifies the smooth glued source with the actual lifted L² forcing. -/
theorem PlanarChartTest.globalForcing_localValue_ae (g : PlanarChartTest)
    (q : XiZeroCopy) (branch : Bool) :
    g.localValue (forcingVector q branch) =ᵐ[(volume : Measure ℂ)]
      (g.globalForcingTest q branch).field := by
  have hp := global_ae_to_planar (P := fun z : ℂ =>
    globalLift (forcingVector q branch) (ofComplex z) = globalForcing q branch (ofComplex z)) (by
      filter_upwards [globalForcing_ae_lift q branch] with z hz
      simpa only [ofComplex_apply] using hz.symm)
  have hh := (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mp hp
  filter_upwards [hh] with z hz
  by_cases hy : 0 < z.im
  · simp only [PlanarChartTest.localValue,PlanarChartTest.globalForcingTest,hz hy]
  · have hg : g.field z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (g.support h))
    simp [PlanarChartTest.localValue,PlanarChartTest.globalForcingTest,hg]

/-- The actual global forcing distribution has a Schwartz representative on every compact chart. -/
theorem PlanarChartTest.globalForcing_localDistribution_eq (g : PlanarChartTest)
    (q : XiZeroCopy) (branch : Bool) :
    g.localDistribution (forcingVector q branch) =
      ((g.globalForcingTest q branch).compact.toSchwartzMap
        (g.globalForcingTest q branch).smooth : 𝓢'(ℂ,ℂ)) := by
  ext ψ
  rw [g.localDistribution_apply]
  change _ = ∫ z : ℂ, ψ z • (g.globalForcingTest q branch).field z
  apply integral_congr_ae
  filter_upwards [g.globalForcing_localValue_ae q branch] with z hz
  rw [hz]
  rfl

/-- The original full forcing has every local Sobolev order across all modular seams and elliptic points. -/
theorem full_forcing_global_local_sobolev (q : XiZeroCopy) (branch : Bool)
    (g : PlanarChartTest) (s : ℝ) : MemSobolev s 2 (g.localDistribution (forcingVector q branch)) := by
  rw [g.globalForcing_localDistribution_eq]
  exact SchwartzMap.memSobolev _

end
end RHTower.D4BMModularCore
