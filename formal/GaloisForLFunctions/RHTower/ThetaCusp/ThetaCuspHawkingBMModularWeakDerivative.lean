import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSmoothModularCore
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
The actual modular measure has its exact planar density. Height-weighted interior tests give the literal local integration-by-parts identity for the hyperbolic derivatives.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff NNReal ENNReal
namespace RHTower.D4BMModularCore
noncomputable section

/-- The original invariant volume density in the complex coordinate. -/
def chartDensity (z : ℂ) : ℝ≥0 := (1/‖z.im‖₊)^(2 : ℕ)

/-- The closed modular cell in the original complex coordinate. -/
def cellChart : Set ℂ := UpperHalfPlane.coe '' ModularGroup.fd

private theorem chartDensity_measurable : Measurable chartDensity := by
  unfold chartDensity
  fun_prop

/-- Exact pushforward of the actual modular Hilbert measure to its weighted planar measure. -/
theorem map_measure_eq : Measure.map UpperHalfPlane.coe measure =
    ((volume : Measure ℂ).restrict cellChart).withDensity (fun z => (chartDensity z : ℝ≥0∞)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs]
  change (volume.restrict ModularGroup.fd) (UpperHalfPlane.coe ⁻¹' s) = _
  rw [Measure.restrict_apply (UpperHalfPlane.measurable_coe hs),UpperHalfPlane.volume_eq_lintegral,
    withDensity_apply _ hs,Measure.restrict_restrict hs]
  have he : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' s ∩ ModularGroup.fd) = s ∩ cellChart := by
    ext z
    constructor
    · rintro ⟨w,⟨hw,hfd⟩,rfl⟩
      exact ⟨hw,w,hfd,rfl⟩
    · rintro ⟨hs,⟨w,hw,rfl⟩⟩
      exact ⟨w,⟨hs,hw⟩,rfl⟩
  rw [he]
  rfl

/-- The full cell integral is the literal planar integral with density y⁻². -/
theorem integral_measure_chart (F : ℂ → ℂ) :
    (∫ z : UpperHalfPlane, F z ∂measure) =
      ∫ z in cellChart, chartDensity z • F z := by
  rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map, map_measure_eq,
    integral_withDensity_eq_integral_smul chartDensity_measurable]

/-- Squared height cancels exactly the native hyperbolic measure density on the cell. -/
theorem integral_height_sq_chart (F : ℂ → ℂ) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*F z ∂measure) = ∫ z in cellChart, F z := by
  have hi := integral_measure_chart (fun z => (z.im : ℂ)^(2 : ℕ)*F z)
  change (∫ z : UpperHalfPlane, ((z:ℂ).im : ℂ)^(2 : ℕ)*F z ∂measure) = _
  rw [hi]
  apply setIntegral_congr_fun
    (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr ModularGroup.isClosed_fd.measurableSet)
  rintro z ⟨w,hw,rfl⟩
  have hy : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr w.im_ne_zero
  simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    coe_nnnorm,Real.norm_eq_abs,abs_of_pos w.im_pos,Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,coe_im]
  field_simp

end
end RHTower.D4BMModularCore

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

private theorem interiorChart_subset_halfplane : interiorChart ⊆ {z : ℂ | 0 < z.im} := by
  rintro _ ⟨z,hz,rfl⟩
  exact z.im_pos

private theorem interiorChart_subset_cellChart : interiorChart ⊆ cellChart :=
  Set.image_mono ModularGroup.fdo_subset_fd

private theorem chart_continuousOn (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) :
    ContinuousOn (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (hf ⟨z,hz⟩).continuousAt.continuousWithinAt

private theorem chart_deriv_continuousOn (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) (v : ℂ) :
    ContinuousOn (fun z => fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) z v)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (((hf ⟨z,hz⟩).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
    continuousAt_const).continuousWithinAt

private theorem integrable_chart_mul_test (a g : ℂ → ℂ)
    (ha : ContinuousOn a {z : ℂ | 0 < z.im}) (hg : Continuous g)
    (hk : HasCompactSupport g) (hs : tsupport g ⊆ {z : ℂ | 0 < z.im}) :
    Integrable (fun z => a z*g z) (volume : Measure ℂ) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right a g).trans (subset_tsupport g))).mp
  exact ((ha.mono hs).mul hg.continuousOn).integrableOn_compact hk

/-- The actual weighted derivative and its compact test satisfy the literal modular-cell
integration-by-parts identity. No boundary term is discarded: the test support lies strictly
inside the cell, and squared height cancels the original invariant volume density. -/
theorem weightedDeriv_test_identity (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hk : HasCompactSupport g)
    (hs : tsupport g ⊆ interiorChart) (v : ℂ) :
    (∫ z : UpperHalfPlane, weightedDeriv v f z*((z.im : ℂ)*g z) ∂measure) =
      -(∫ z : UpperHalfPlane, f z*((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g (z:ℂ) v) ∂measure) := by
  let F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  let D : ℂ → ℂ := fun z => fderiv ℝ g z v
  have hD : Continuous D :=
    ((hg.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const)
  have hDK : HasCompactSupport D := hk.fderiv_apply ℝ v
  have hDS : tsupport D ⊆ tsupport g := tsupport_fderiv_apply_subset ℝ v
  have hgH := hs.trans interiorChart_subset_halfplane
  have hf'g := integrable_chart_mul_test _ g (chart_deriv_continuousOn f hf v)
    hg.continuous hk hgH
  have hfg' := integrable_chart_mul_test F D (chart_continuousOn f hf) hD hDK (hDS.trans hgH)
  have hfg := integrable_chart_mul_test F g (chart_continuousOn f hf) hg.continuous hk hgH
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun z hz => (hf ⟨z,hgH hz⟩).differentiableAt (by simp))
    (fun z _ => hg.differentiable (by simp) z)
  have hL : (∫ z : UpperHalfPlane, weightedDeriv v f z*((z.im : ℂ)*g z) ∂measure) =
      ∫ z : ℂ, fderiv ℝ F z v*g z := by
    calc
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*(fderiv ℝ F (z:ℂ) v*g z) ∂measure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by unfold weightedDeriv F; ring)
      _ = ∫ z in cellChart, fderiv ℝ F z v*g z :=
        integral_height_sq_chart (fun z => fderiv ℝ F z v*g z)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hn : z ∉ tsupport g := fun hg => hz (interiorChart_subset_cellChart (hs hg))
        rw [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  have hR : (∫ z : UpperHalfPlane, f z*((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g (z:ℂ) v) ∂measure) =
      ∫ z : ℂ, F z*fderiv ℝ g z v := by
    calc
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*(F z*fderiv ℝ g (z:ℂ) v) ∂measure := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [F,Function.comp_apply,UpperHalfPlane.ofComplex_apply]
        ring
      _ = ∫ z in cellChart, F z*fderiv ℝ g z v :=
        integral_height_sq_chart (fun z => F z*fderiv ℝ g z v)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hn : z ∉ tsupport D := fun hd => hz (interiorChart_subset_cellChart (hs (hDS hd)))
        change F z*D z = 0
        rw [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  rw [hL,hR]
  simpa only [neg_neg] using (congrArg Neg.neg hibp).symm

end
end RHTower.D4BMModularCore
