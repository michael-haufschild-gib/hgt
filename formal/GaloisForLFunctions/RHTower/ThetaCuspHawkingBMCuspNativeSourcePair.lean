import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNativeIntegral

/-!
# Exact source projection in the original modular Hilbert pairing with every actual cusp test.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
namespace RHTower.D4BMCuspProjection
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private def rectangle : Set ℂ := {z | z.re ∈ Icc (-1/2) (1/2) ∧ 2 < z.im}

private theorem rectangle_subset : rectangle ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by norm_num) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

private theorem integral_cusp_field (F : ℂ → ℂ)
    (hi : Integrable (fun z : UpperHalfPlane => F z) measure)
    (hz : ∀ z : ℂ, z.im ≤ 2 → F z=0) :
    (∫ z : UpperHalfPlane, F z ∂measure) =
      ∫ y in Ioi 2, mean (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^2 := by
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
  have hrect : IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) rectangle := by
    apply (hd.mono_set rectangle_subset).congr_fun
    · intro z hz
      exact hden z (lt_trans (by norm_num) hz.2)
    · exact (isClosed_Icc.preimage Complex.continuous_re).measurableSet.inter
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  let G : ℝ × ℝ → ℂ := fun xy => F (Complex.measurableEquivRealProd.symm xy)/(xy.2:ℂ)^2
  have hG : IntegrableOn G (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (2:ℝ))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    change IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^2) rectangle
    exact hrect
  rw [integral_measure_chart]
  have he : (∫ z in cellChart, chartDensity z • F z) =
      ∫ z in cellChart, F z/(z.im:ℂ)^2 := by
    apply setIntegral_congr_fun hcell
    rintro z ⟨w,hw,rfl⟩
    exact hden w w.im_pos
  rw [he,setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hcell rectangle_subset]
  · have hp := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding G
      (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (2:ℝ))
    change (∫ z in Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (2:ℝ)),
      G (Complex.measurableEquivRealProd z)) = _
    rw [hp,Measure.volume_eq_prod]
    have hf : Integrable G
        ((volume.restrict (Icc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi (2:ℝ)))) := by
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
    have hlow : w.im ≤ 2 := by
      by_contra hn
      apply hz'.2
      refine ⟨?_,lt_of_not_ge hn⟩
      change w.re ∈ Icc (-1/2) (1/2)
      simpa only [mem_Icc,neg_div] using abs_le.mp hw.2
    rw [hz w hlow,zero_div]

/-- The exact native pairing of the full admitted forcing with every actual
cusp test is its derived horizontal mean with the original hyperbolic density. -/
theorem forcingVector_cusp_inner (q : XiZeroCopy) (branch : Bool) (h : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (forcingVector q branch) =
      ∫ y in Ioi 2, conj (h.field y)*mean (fun x => forcing q branch ![x,y])/(y:ℂ)^2 := by
  have he : (fun z : UpperHalfPlane =>
      inner ℂ ((h.operatorVector : Space) z) (forcingVector q branch z)) =ᵐ[measure]
      (fun z => conj (h.field z.im)*forcing q branch ![z.re,z.im]) := by
    filter_upwards [h.operatorVector_coe,forcingVector_coe q branch] with z hh hf
    rw [hh,hf]
    simp [RCLike.inner_apply,coordinates,mul_comm]
  have hi := (L2.integrable_inner (𝕜 := ℂ) (h.operatorVector : Space)
    (forcingVector q branch)).congr he
  rw [L2.inner_def,integral_congr_ae he]
  change (∫ z : UpperHalfPlane, conj (h.field (z:ℂ).im)*forcing q branch ![(z:ℂ).re,(z:ℂ).im] ∂measure)=_
  rw [integral_cusp_field (fun z => conj (h.field z.im)*forcing q branch ![z.re,z.im]) hi
    (fun z hz => by rw [h.zero_low hz]; simp)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  congr 1
  change mean (fun x => conj (h.field y)*forcing q branch ![x,y]) = _
  exact integral_const_mul _ _

/-- Native source pairing with the complete explicit cusp projection, including
all cutoff derivatives and every opposite Fourier pair. -/
theorem forcingVector_cusp_inner_explicit (q : XiZeroCopy) (branch : Bool) (h : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (forcingVector q branch) =
      ∫ y in Ioi 2, conj (h.field y)*
        ((parameter q branch/2)*(principal (center q) ![0,y] ^2+
          8*∑' N, amplitude (center q) y N^2)-
          ((y:ℂ)^2*deriv (deriv (cutoffHeight q branch)) y-
            parameter q branch*cutoffHeight q branch y))/(y:ℂ)^2 := by
  rw [forcingVector_cusp_inner]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [mean_forcing q branch (y := y) (by change 2 < y at hy; linarith)]

end
end RHTower.D4BMCuspProjection
