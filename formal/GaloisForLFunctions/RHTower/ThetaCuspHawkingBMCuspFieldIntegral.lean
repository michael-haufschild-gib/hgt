import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspSourceMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNativeIntegral

/-! Exact hyperbolic integration of a full cusp-supported field, at any threshold above one. -/
open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMCuspProjection
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private def rectangle (L : ℝ) : Set ℂ := {z | z.re ∈ Icc (-1/2) (1/2) ∧ L < z.im}

private theorem rectangle_subset (L : ℝ) (hL : 1 ≤ L) : rectangle L ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by linarith : 0 < L) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

/-- Exact original hyperbolic integral for any full field supported in a cusp strip. -/
theorem integral_cusp_field_from (L : ℝ) (hL : 1 ≤ L) (F : ℂ → ℂ)
    (hi : Integrable (fun z : UpperHalfPlane => F z) measure)
    (hz : ∀ z : ℂ, z.im ≤ L → F z=0) :
    (∫ z : UpperHalfPlane, F z ∂measure) =
      ∫ y in Ioi L, mean (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^2 := by
  have hcell : MeasurableSet cellChart :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet
  have hden (z : ℂ) (hp : 0 < z.im) : chartDensity z • F z = F z/(z.im:ℂ)^2 := by
    simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      coe_nnnorm,Real.norm_eq_abs,abs_of_pos hp,Complex.real_smul,
      Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
    ring
  have hmap : Integrable F (Measure.map UpperHalfPlane.coe measure) :=
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr hi
  rw [map_measure_eq] at hmap
  have hd : IntegrableOn (fun z => chartDensity z • F z) cellChart :=
    (integrable_withDensity_iff_integrable_smul (show Measurable chartDensity by
    unfold chartDensity; fun_prop)).mp hmap
  have hrect : IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) (rectangle L) := by
    apply (hd.mono_set (rectangle_subset L hL)).congr_fun
    · intro z hz
      exact hden z (lt_trans (by linarith : 0 < L) hz.2)
    · exact (isClosed_Icc.preimage Complex.continuous_re).measurableSet.inter
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  let G : ℝ × ℝ → ℂ := fun xy => F (Complex.measurableEquivRealProd.symm xy)/(xy.2:ℂ)^2
  have hG : IntegrableOn G (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi L)
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    change IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) (rectangle L)
    exact hrect
  rw [integral_measure_chart]
  have he : (∫ z in cellChart, chartDensity z • F z) =
      ∫ z in cellChart, F z/(z.im:ℂ)^2 := by
    apply setIntegral_congr_fun hcell
    rintro z ⟨w,hw,rfl⟩
    exact hden w w.im_pos
  rw [he,setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hcell (rectangle_subset L hL)]
  · have hp := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding G
      (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi L)
    change (∫ z in Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi L),
      G (Complex.measurableEquivRealProd z)) = _
    rw [hp,Measure.volume_eq_prod]
    have hf : Integrable G
        ((volume.restrict (Icc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi L))) := by
      simpa only [Measure.prod_restrict,IntegrableOn] using hG
    rw [← Measure.prod_restrict,integral_prod_symm G hf]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp [G]
    simp only [div_eq_mul_inv]
    rw [integral_mul_const,integral_Icc_eq_integral_Ioc]
    rfl
  · intro z hz'
    obtain ⟨w,hw,rfl⟩ := hz'.1
    have hlow : w.im ≤ L := by
      by_contra hn
      apply hz'.2
      refine ⟨?_,lt_of_not_ge hn⟩
      change w.re ∈ Icc (-1/2) (1/2)
      simpa only [mem_Icc,neg_div] using abs_le.mp hw.2
    rw [hz w hlow,zero_div]

end
end RHTower.D4BMCuspProjection
