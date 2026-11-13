import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness
import GaloisForLFunctions.RHTower.DetectorDuality

/-!
# Exact Cayley transport between disk Hardy space and half-line data

The half-line Laplace features and the disk Szegő kernels have equal Gram
matrices after their Cayley normalization. Totality gives a unitary, with an
exact Laplace evaluation formula.
-/

noncomputable section
open Complex MeasureTheory Metric Set Filter Topology
open scoped InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry

/-- The feature definition and the literal Laplace integral agree. -/
theorem halfLineLaplaceTransform_eq_laplaceRay
    (f : Lp ℂ 2 halfLineLaplaceMeasure) {w : ℂ} (hw : 0 < w.re) :
    halfLineLaplaceTransform f w hw = laplaceRay f w := by
  rw [halfLineLaplaceTransform_eq_integral]
  change (∫ x in Ioi (0 : ℝ), Complex.exp (-w * (x : ℂ)) * f x) = _
  unfold laplaceRay
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [expRay, neg_mul]
    exact mul_comm _ _

private theorem cayleyRight_diskToRight {z : ℂ} (hz : ‖z‖ < 1) :
    cayleyRight (diskToRight z) = z := by
  have hz' : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
  have hden := one_sub_ne_zero_of_mem_unitBall hz'
  unfold cayleyRight diskToRight
  field_simp
  ring

/-- Disk Szegő kernels indexed by the right half-plane. -/
def rightCayleyDiskFeature (w : {w : ℂ // 0 < w.re}) : HardyDisk :=
  hardyKernel (norm_cayleyRight_lt_one w.2)

/-- The normalizing scalar of a half-line Cauchy feature. -/
def rightCayleyFeatureScale (w : {w : ℂ // 0 < w.re}) : ℂ :=
  ((starRingEnd ℂ) w.1 + 1) / (Real.sqrt 2 : ℂ)

theorem rightCayleyFeatureScale_ne_zero (w : {w : ℂ // 0 < w.re}) :
    rightCayleyFeatureScale w ≠ 0 := by
  apply div_ne_zero
  · apply add_one_ne_zero_of_re_nonneg
    simpa only [Complex.conj_re] using w.2.le
  · exact ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- Half-line Laplace features in disk normalization. -/
def rightCayleyHalfLineFeature (w : {w : ℂ // 0 < w.re}) : Lp ℂ 2 halfLineLaplaceMeasure :=
  rightCayleyFeatureScale w • halfLineLaplaceFeature w.1 w.2

/-- The two normalized feature families have exactly the same Gram kernel. -/
theorem inner_rightCayleyDiskFeature_eq_halfLine (w v : {w : ℂ // 0 < w.re}) :
    inner ℂ (rightCayleyDiskFeature w) (rightCayleyDiskFeature v) =
      inner ℂ (rightCayleyHalfLineFeature w) (rightCayleyHalfLineFeature v) := by
  have hw1 := add_one_ne_zero_of_re_nonneg w.2.le
  have hv1 := add_one_ne_zero_of_re_nonneg
    (show 0 ≤ ((starRingEnd ℂ) v.1).re by simpa only [Complex.conj_re] using v.2.le)
  have hwv : w.1 + (starRingEnd ℂ) v.1 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [add_re, Complex.conj_re, zero_re] at hre
    linarith only [w.2, v.2, hre]
  have hs : (Real.sqrt 2 : ℂ) ^ (2 : ℕ) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsn : (Real.sqrt 2 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [rightCayleyDiskFeature, rightCayleyDiskFeature, inner_hardyKernel_hardyKernel]
  rw [mul_comm ((starRingEnd ℂ) (cayleyRight v.1)) (cayleyRight w.1),
    one_sub_cayleyRight_mul_conj w.2.le v.2.le]
  simp only [rightCayleyHalfLineFeature, inner_smul_left, inner_smul_right,
    inner_halfLineLaplaceFeature, rightCayleyFeatureScale, map_div₀, map_add,
    map_one, Complex.conj_ofReal, Complex.conj_conj, RCLike.star_def]
  field_simp
  rw [hs]

private theorem rightCayleyDiskFeature_total :
    (Submodule.span ℂ (range rightCayleyDiskFeature)).topologicalClosure = ⊤ := by
  rw [topologicalClosure_span_eq_top_iff]
  intro f hf
  apply hardyDisk_ext
  intro z hz
  let w : {w : ℂ // 0 < w.re} :=
    ⟨diskToRight z, diskToRight_re_pos (mem_ball_zero_iff.mpr hz)⟩
  have he := hf (rightCayleyDiskFeature w) ⟨w, rfl⟩
  have he' := congrArg (starRingEnd ℂ) he
  rw [inner_conj_symm, map_zero, rightCayleyDiskFeature, inner_hardyKernel] at he'
  change hardyFun f (cayleyRight (diskToRight z)) = 0 at he'
  rw [cayleyRight_diskToRight hz] at he'
  simpa [hardyFun] using he'

private theorem rightCayleyHalfLineFeature_total :
    (Submodule.span ℂ (range rightCayleyHalfLineFeature)).topologicalClosure = ⊤ := by
  rw [topologicalClosure_span_eq_top_iff]
  intro f hf
  have hzero : ∀ w : ℂ, 0 < w.re → laplaceRay f w = 0 := by
    intro w hw
    have he := hf (rightCayleyHalfLineFeature ⟨w, hw⟩) ⟨⟨w, hw⟩, rfl⟩
    rw [rightCayleyHalfLineFeature, inner_smul_right] at he
    have he' : inner ℂ f (halfLineLaplaceFeature w hw) = 0 :=
      (mul_eq_zero.mp he).resolve_left (rightCayleyFeatureScale_ne_zero ⟨w, hw⟩)
    have hh := congrArg (starRingEnd ℂ) he'
    rw [inner_conj_symm, map_zero] at hh
    rw [← halfLineLaplaceTransform, halfLineLaplaceTransform_eq_laplaceRay] at hh
    exact hh
  have hae := ae_eq_zero_of_laplaceRay_eq_zero (Lp.memLp f) hzero
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℂ 2 halfLineLaplaceMeasure] with x hx hz
  exact hx.trans hz.symm

/-- The canonical unitary whose normalized Laplace features are the disk kernels. -/
def hardyDiskHalfLineCayleyUnitary : HardyDisk ≃ₗᵢ[ℂ] Lp ℂ 2 halfLineLaplaceMeasure :=
  denseFeatureGramUnitary rightCayleyDiskFeature rightCayleyHalfLineFeature
    inner_rightCayleyDiskFeature_eq_halfLine
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      rightCayleyDiskFeature rightCayleyDiskFeature_total)
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      rightCayleyHalfLineFeature rightCayleyHalfLineFeature_total)

theorem hardyDiskHalfLineCayleyUnitary_apply_feature (w : {w : ℂ // 0 < w.re}) :
    hardyDiskHalfLineCayleyUnitary (rightCayleyDiskFeature w) = rightCayleyHalfLineFeature w :=
  denseFeatureGramUnitary_apply rightCayleyDiskFeature rightCayleyHalfLineFeature
    inner_rightCayleyDiskFeature_eq_halfLine
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      rightCayleyDiskFeature rightCayleyDiskFeature_total)
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      rightCayleyHalfLineFeature rightCayleyHalfLineFeature_total) w

/-- Exact Laplace evaluation of the disk Hardy representative of a half-line datum. -/
theorem hardyFun_halfLineCayley_inverse (f : Lp ℂ 2 halfLineLaplaceMeasure)
    {w : ℂ} (hw : 0 < w.re) :
    hardyFun (hardyDiskHalfLineCayleyUnitary.symm f) (cayleyRight w) =
      (w + 1) / (Real.sqrt 2 : ℂ) * laplaceRay f w := by
  rw [← inner_hardyKernel (norm_cayleyRight_lt_one hw)]
  change inner ℂ (rightCayleyDiskFeature ⟨w, hw⟩) _ = _
  rw [← hardyDiskHalfLineCayleyUnitary.inner_map_map,
    hardyDiskHalfLineCayleyUnitary_apply_feature,
    hardyDiskHalfLineCayleyUnitary.apply_symm_apply]
  rw [rightCayleyHalfLineFeature, inner_smul_left]
  change (starRingEnd ℂ) (rightCayleyFeatureScale ⟨w, hw⟩) *
    halfLineLaplaceTransform f w hw = _
  rw [halfLineLaplaceTransform_eq_laplaceRay]
  simp only [rightCayleyFeatureScale, map_div₀, map_add, map_one,
    Complex.conj_ofReal, Complex.conj_conj]

/-- Evaluation in disk coordinates, with the exact Cayley weight. -/
theorem hardyFun_halfLineCayley_inverse_disk (f : Lp ℂ 2 halfLineLaplaceMeasure)
    {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (hardyDiskHalfLineCayleyUnitary.symm f) z =
      (diskToRight z + 1) / (Real.sqrt 2 : ℂ) * laplaceRay f (diskToRight z) := by
  have he := hardyFun_halfLineCayley_inverse f
    (diskToRight_re_pos (mem_ball_zero_iff.mpr hz))
  rwa [cayleyRight_diskToRight hz] at he

#print axioms hardyFun_halfLineCayley_inverse

end GaloisForLFunctions.HTGeometry
