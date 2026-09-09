import GaloisForLFunctions.RHTower.SelbergMaassCurrentDensity
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport

/-!
# Actual source density and nodal separation of Maass current curvature

The proved compact-test density integrability transfers through the actual
hyperbolic chart. Compact cutoffs give local finiteness of the literal density
measure, and regular-measure uniqueness identifies it with the existing current
measure. Thus the current is absolutely continuous and gives zero mass to the
common-zero set. Together with residual support this makes the two original
measures mutually singular. No zero-area assertion for the nodal set, residual
singularity relative to volume, or spectral quarter bound is assumed.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported NNReal ENNReal
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentDensityMeasure
open SelbergMaassCongruenceTrace SelbergMaassWeakCurvature SelbergMaassCurrentCurvature
  SelbergMaassCurrentTests SelbergMaassCurrentDensity SelbergMaassCurrentMeasures
  SelbergMaassResidualSupport SelbergMaassCurvatureTransport SelbergUpperHalfPlaneCompactTests
noncomputable section

/-- Genuine integrability transfers across the actual hyperbolic chart with its squared-height factor. -/
theorem integrable_height_sq_chart (F : ℂ → ℝ) :
    Integrable (fun z : ℍ => z.im ^ 2 * F z) ↔
      IntegrableOn F {z : ℂ | 0 < z.im} := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  change Integrable ((fun z : ℂ => z.im ^ 2 * F z) ∘ UpperHalfPlane.coe) _ ↔ _
  rw [← UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff, map_volume_chart,
    integrable_withDensity_iff_integrable_smul hm]
  apply integrableOn_congr_fun _ isOpen_upperHalfPlaneSet.measurableSet
  intro z hz
  change 0 < z.im at hz
  simp only [chartDensity, NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs, abs_of_pos hz, smul_eq_mul]
  field_simp

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The literal source current density relative to hyperbolic volume. -/
def hyperbolicCurrentDensity (z : ℍ) : ℝ := z.im ^ 2 * sourceCurrentDensity N f z

/-- The actual hyperbolic current density is nonnegative. -/
theorem hyperbolicCurrentDensity_nonneg (z : ℍ) : 0 ≤ hyperbolicCurrentDensity N f z :=
  mul_nonneg (sq_nonneg z.im) (sourceCurrentDensity_nonneg N f z)

/-- The source current density is measurable even at its original zero set. -/
theorem hyperbolicCurrentDensity_measurable : Measurable (hyperbolicCurrentDensity N f) := by
  have hC : Continuous (fun z : ℍ => currentEnergy N f z) :=
    (currentEnergy_continuousOn N f).comp_continuous continuous_coe (fun z => z.im_pos)
  have hA : Continuous (fun z : ℍ => SelbergMaassWeakCurvature.amplitude N f z) := by
    simpa only [SelbergMaassWeakCurvature.amplitude, ofComplex_apply] using
      (density_continuous N f).sqrt
  exact (UpperHalfPlane.continuous_im.pow 2).measurable.mul (hC.measurable.div (hA.pow 3).measurable)

/-- The actual density defines a measure with respect to hyperbolic volume. -/
def currentDensityMeasure : Measure ℍ :=
  volume.withDensity (fun z => ENNReal.ofReal (hyperbolicCurrentDensity N f z))

/-- Every compact test is integrable for the literal density measure; this is proved before measure uniqueness. -/
theorem densityMeasure_test_integrable (g : C_c(ℍ, ℝ)) :
    Integrable g (currentDensityMeasure N f) := by
  rw [currentDensityMeasure, integrable_withDensity_iff_integrable_smul'
    (hyperbolicCurrentDensity_measurable N f).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hyperbolicCurrentDensity_nonneg N f _), smul_eq_mul]
  have hi := (integrable_height_sq_chart (fun z => zeroExtend g z * sourceCurrentDensity N f z)).mpr
    (test_density_integrable N f (zeroExtend_continuous g) (zeroExtend_compact g)
      (zeroExtend_support g)).integrableOn
  apply hi.congr
  exact Eventually.of_forall (fun z => by dsimp only; rw [zeroExtend_apply]; unfold hyperbolicCurrentDensity; ring)

/-- Integration against the density measure equals the literal original planar test integral. -/
theorem integral_densityMeasure_test (g : C_c(ℍ, ℝ)) :
    (∫ z, g z ∂currentDensityMeasure N f) = ∫ z, zeroExtend g z * sourceCurrentDensity N f z := by
  rw [currentDensityMeasure, integral_withDensity_eq_integral_toReal_smul
    (hyperbolicCurrentDensity_measurable N f).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hyperbolicCurrentDensity_nonneg N f _), smul_eq_mul]
  calc
    _ = ∫ z : ℍ, z.im ^ 2 * (zeroExtend g z * sourceCurrentDensity N f z) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by dsimp only; rw [zeroExtend_apply]; unfold hyperbolicCurrentDensity; ring)
    _ = ∫ z in {z : ℂ | 0 < z.im}, zeroExtend g z * sourceCurrentDensity N f z :=
      integral_height_sq_chart (fun z : ℂ => zeroExtend g z * sourceCurrentDensity N f z)
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (zeroExtend_support g h)), zero_mul]

/-- Actual compact cutoffs give finite mass on every compact set for the density measure. -/
instance currentDensityMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (currentDensityMeasure N f) := ⟨by
  intro K hK
  obtain ⟨h, hone, hcomp, _, h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let g : C_c(ℍ, ℝ) := ⟨h, hcomp⟩
  apply lt_of_le_of_lt ((densityMeasure_test_integrable N f g).measure_le_integral
    (Eventually.of_forall (fun z => (h01 z).1)) (fun z hz => by
      change (1 : ℝ) ≤ h z
      rw [hone hz]
      exact le_rfl)) ENNReal.ofReal_lt_top⟩

/-- The actual density measure is regular, with local finiteness derived from source tests. -/
instance currentDensityMeasure_regular : (currentDensityMeasure N f).Regular := by infer_instance

/-- The constructed current measure is exactly the source density measure. -/
theorem currentMeasure_eq_densityMeasure : currentMeasure N f = currentDensityMeasure N f := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_current_eq_density, integral_densityMeasure_test]

/-- Explicit density of the original current measure with respect to hyperbolic volume. -/
theorem currentMeasure_eq_withDensity : currentMeasure N f =
    volume.withDensity (fun z : ℍ => ENNReal.ofReal (z.im ^ 2 * sourceCurrentDensity N f z)) :=
  currentMeasure_eq_densityMeasure N f

/-- The actual current measure is absolutely continuous with respect to hyperbolic volume. -/
theorem currentMeasure_absolutelyContinuous : currentMeasure N f ≪ (volume : Measure ℍ) := by
  rw [currentMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The actual current measure gives no mass to original common zeros, independently of their area. -/
theorem currentMeasure_node_zero : currentMeasure N f {z : ℍ | density N f z = 0} = 0 := by
  rw [currentMeasure_eq_densityMeasure, currentDensityMeasure,
    withDensity_apply_eq_zero (hyperbolicCurrentDensity_measurable N f).ennreal_ofReal]
  have he : {z : ℍ | ENNReal.ofReal (hyperbolicCurrentDensity N f z) ≠ 0} ∩
      {z : ℍ | density N f z = 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzero : hyperbolicCurrentDensity N f z = 0 := by
      rw [hyperbolicCurrentDensity, sourceCurrentDensity_at_node N f z hz.2, mul_zero]
    exact hz.1 (by rw [hzero, ENNReal.ofReal_zero])
  rw [he, measure_empty]

/-- The original current and residual measures are mutually singular, with the actual nodal set as separator. -/
theorem currentMeasure_mutuallySingular_residual :
    (currentMeasure N f).MutuallySingular (residualMeasure N f) := by
  exact ⟨{z : ℍ | density N f z = 0},
    (isClosed_eq (density_continuous N f) continuous_const).measurableSet,
    currentMeasure_node_zero N f, residualMeasure_compl_node_zero N f⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentDensityMeasure
