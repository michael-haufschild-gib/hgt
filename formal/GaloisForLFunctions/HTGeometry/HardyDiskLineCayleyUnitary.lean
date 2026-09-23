import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCauchyTotality
import GaloisForLFunctions.HTGeometry.HalfPlaneFiniteBlaschkeModel
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteUpperKernelInertia

/-!
# Exact Cayley unitary between disk and line Hardy spaces

The disk Szegő kernels and the upper-half-plane Cauchy kernels have the same Gram matrix after the
classical Cayley half-density normalization.  Both families are total, so the equal-Gram completion
theorem gives a canonical unitary between `H²(D)` and the literal upper Hardy boundary subspace of
`L²(ℝ)`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance hardyDiskLineCayleyUnitaryLocalInst1 : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

/-- Disk Szegő feature at the Cayley image of an upper-half-plane point. -/
def cayleyDiskHardyFeature (w : UpperHalfPlanePoint) : HardyDisk :=
  hardyKernel (GaloisForLFunctions.cayley_upperHalfPlane_to_disk w.1 w.2)

/-- Cayley half-density normalizing the line Cauchy feature to the disk Szegő kernel. -/
def cayleyLineFeatureScale (w : UpperHalfPlanePoint) : ℂ :=
  ((starRingEnd ℂ) w.1 - I) / ((2 * Real.sqrt Real.pi : ℝ) : ℂ)

theorem cayleyLineFeatureScale_ne_zero (w : UpperHalfPlanePoint) :
    cayleyLineFeatureScale w ≠ 0 := by
  apply div_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith [w.2]
  · exact ofReal_ne_zero.mpr (mul_ne_zero (by norm_num)
      (Real.sqrt_ne_zero'.mpr Real.pi_pos))

/-- Half-density-normalized upper-half-plane Cauchy feature. -/
def cayleyLineHardyFeature (w : UpperHalfPlanePoint) : UpperHardyL2 :=
  cayleyLineFeatureScale w • lowerCauchyFeatureAt w.1 w.2

/-- Cross-Gram formula for arbitrary upper-half-plane Cauchy features. -/
theorem inner_lowerCauchyFeatureAt_cross
    (z w : UpperHalfPlanePoint) :
    inner ℂ (lowerCauchyFeatureAt z.1 z.2)
        (lowerCauchyFeatureAt w.1 w.2) =
      2 * (Real.pi : ℂ) * I *
        (z.1 - (starRingEnd ℂ) w.1)⁻¹ := by
  rw [inner_lowerCauchyFeatureAt]
  have hdiff : ∀ u : ℂ, 0 ≤ u.im →
      DifferentiableAt ℂ (fun v : ℂ => (v - (starRingEnd ℂ) w.1)⁻¹) u := by
    intro u hu
    apply (differentiableAt_id.sub_const _).inv
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    norm_num at him
    linarith [w.2]
  have hR : 0 < 2 * ‖w.1‖ + 1 := by positivity
  have hfar : ∀ u : ℂ, 0 ≤ u.im → 2 * ‖w.1‖ + 1 ≤ ‖u‖ →
      ‖(u - (starRingEnd ℂ) w.1)⁻¹‖ ≤ 2 / ‖u‖ := by
    intro u hu huR
    have huPos : 0 < ‖u‖ := by linarith [norm_nonneg w.1]
    have hhalf : ‖w.1‖ ≤ ‖u‖ / 2 := by linarith
    have hden : ‖u‖ / 2 ≤ ‖u - (starRingEnd ℂ) w.1‖ := by
      have h := norm_sub_norm_le u ((starRingEnd ℂ) w.1)
      rw [RCLike.norm_conj] at h
      linarith
    have hhalfPos : 0 < ‖u‖ / 2 := by positivity
    rw [norm_inv]
    calc
      ‖u - (starRingEnd ℂ) w.1‖⁻¹ ≤ (‖u‖ / 2)⁻¹ :=
        inv_anti₀ hhalfPos hden
      _ = 2 / ‖u‖ := by field_simp
  have hcauchy := integral_div_sub_eq_of_upperHalfPlane_farDecay
    (u := fun v : ℂ => (v - (starRingEnd ℂ) w.1)⁻¹)
    (M := 2) (R := 2 * ‖w.1‖ + 1) hdiff hR hfar z.2
  calc
    (∫ x : ℝ,
        ((lowerCauchyFeatureAt w.1 w.2 : UpperHardyL2) : RealLineL2) x /
          (((x : ℝ) : ℂ) - z.1)) =
      (∫ x : ℝ, (((x : ℝ) : ℂ) - (starRingEnd ℂ) w.1)⁻¹ /
        (((x : ℝ) : ℂ) - z.1)) := by
          apply integral_congr_ae
          filter_upwards [coe_lowerCauchyFeatureAt w.2] with x hx
          rw [hx]
    _ = 2 * (Real.pi : ℂ) * I *
        (z.1 - (starRingEnd ℂ) w.1)⁻¹ := hcauchy

/-- The Cayley-normalized line and disk feature families have identical Gram kernels. -/
theorem inner_cayleyDiskHardyFeature_eq_line
    (z w : UpperHalfPlanePoint) :
    inner ℂ (cayleyDiskHardyFeature z) (cayleyDiskHardyFeature w) =
      inner ℂ (cayleyLineHardyFeature z) (cayleyLineHardyFeature w) := by
  unfold cayleyDiskHardyFeature cayleyLineHardyFeature
  have hzI : z.1 + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [z.2]
  have hwI : (starRingEnd ℂ) w.1 - I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [w.2]
  have hzw : z.1 - (starRingEnd ℂ) w.1 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [z.2, w.2]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hscaleSq : ((((2 * Real.sqrt Real.pi : ℝ) : ℂ)) ^ (2 : ℕ)) =
      4 * (Real.pi : ℂ) := by
    norm_cast
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  rw [inner_hardyKernel_hardyKernel,
    _root_.inner_smul_left
      (lowerCauchyFeatureAt z.1 z.2)
      (cayleyLineFeatureScale w • lowerCauchyFeatureAt w.1 w.2)
      (cayleyLineFeatureScale z),
    _root_.inner_smul_right
      (lowerCauchyFeatureAt z.1 z.2)
      (lowerCauchyFeatureAt w.1 w.2)
      (cayleyLineFeatureScale w),
    inner_lowerCauchyFeatureAt_cross]
  change (1 - (starRingEnd ℂ) (upperToDiskCayley w.1) *
      upperToDiskCayley z.1)⁻¹ = _
  rw [mul_comm ((starRingEnd ℂ) (upperToDiskCayley w.1))
      (upperToDiskCayley z.1),
    one_sub_upperToDiskCayley_mul_conj hzI hwI]
  simp only [cayleyLineFeatureScale, map_div₀, map_sub,
    Complex.conj_ofReal, Complex.conj_conj, Complex.conj_I, inv_div]
  field_simp [hzI, hwI, hzw, hsqrt]
  rw [hscaleSq]
  simp only [Complex.I_sq]
  ring

/-- Cayley-indexed disk Szegő kernels are total in `H²(D)`. -/
theorem topologicalClosure_span_cayleyDiskHardyFeature_eq_top :
    (Submodule.span ℂ (Set.range cayleyDiskHardyFeature)).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro f hf
  apply hardyDisk_ext
  intro u hu
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, norm_one] at hu
    exact (lt_irrefl 1) hu
  let z : ℂ := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u
  have hz : 0 < z.im :=
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hu
  let zw : UpperHalfPlanePoint := ⟨z, hz⟩
  have horth := hf (cayleyDiskHardyFeature zw) ⟨zw, rfl⟩
  have hreverse : inner ℂ (cayleyDiskHardyFeature zw) f = 0 := by
    have hstar := congrArg (starRingEnd ℂ) horth
    simpa only [map_zero, inner_conj_symm] using hstar
  rw [cayleyDiskHardyFeature, inner_hardyKernel] at hreverse
  have hcayley := RHTower.upperToDiskCayley_suzukiUpperCayleyInv hu1
  change upperToDiskCayley z = u at hcayley
  change hardyFun f (upperToDiskCayley z) = 0 at hreverse
  rw [hcayley] at hreverse
  simpa [hardyFun] using hreverse

/-- Cayley-normalized line Cauchy kernels remain total in the literal upper Hardy boundary space. -/
theorem topologicalClosure_span_cayleyLineHardyFeature_eq_top :
    (Submodule.span ℂ (Set.range cayleyLineHardyFeature)).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro f hf
  have htotal := topologicalClosure_span_lowerCauchyFeatureAt_eq_top
  rw [RHTower.topologicalClosure_span_eq_top_iff] at htotal
  apply htotal f
  intro k hk
  rcases hk with ⟨w, rfl⟩
  have hscaled := hf (cayleyLineHardyFeature w) ⟨w, rfl⟩
  have hscaled' : cayleyLineFeatureScale w *
      inner ℂ f (lowerCauchyFeatureAt w.1 w.2) = 0 := by
    rw [cayleyLineHardyFeature,
      _root_.inner_smul_right f (lowerCauchyFeatureAt w.1 w.2)
        (cayleyLineFeatureScale w)] at hscaled
    exact hscaled
  exact (mul_eq_zero.mp hscaled').resolve_left (cayleyLineFeatureScale_ne_zero w)

/-- Exact unitary Cayley transport from disk Hardy space to literal upper-half-plane `L²`
boundary space. -/
noncomputable def hardyDiskLineCayleyUnitary :
    HardyDisk ≃ₗᵢ[ℂ] UpperHardyL2 :=
  denseFeatureGramUnitary cayleyDiskHardyFeature cayleyLineHardyFeature
    inner_cayleyDiskHardyFeature_eq_line
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      cayleyDiskHardyFeature topologicalClosure_span_cayleyDiskHardyFeature_eq_top)
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      cayleyLineHardyFeature topologicalClosure_span_cayleyLineHardyFeature_eq_top)

/-- The Hardy Cayley unitary has the exact classical action on every Szegő kernel. -/
theorem hardyDiskLineCayleyUnitary_apply_feature (w : UpperHalfPlanePoint) :
    hardyDiskLineCayleyUnitary (cayleyDiskHardyFeature w) =
      cayleyLineHardyFeature w :=
  denseFeatureGramUnitary_apply cayleyDiskHardyFeature cayleyLineHardyFeature
    inner_cayleyDiskHardyFeature_eq_line
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      cayleyDiskHardyFeature topologicalClosure_span_cayleyDiskHardyFeature_eq_top)
    (dense_range_featureSynthesis_of_topologicalClosure_span_eq_top
      cayleyLineHardyFeature topologicalClosure_span_cayleyLineHardyFeature_eq_top) w

end GaloisForLFunctions.HTGeometry
