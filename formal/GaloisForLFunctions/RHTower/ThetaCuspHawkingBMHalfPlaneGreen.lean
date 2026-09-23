import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularDirichletUnfolding

/-!
Exact native density transport and integration by parts for all compact positive-height chart tests.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff NNReal ENNReal ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- Smooth compact planar tests in positive height, with no modular seam restriction. -/
structure PlanarChartTest where
  field : ℂ → ℂ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ {z : ℂ | 0 < z.im}

def PlanarChartTest.toChartTest (g : PlanarChartTest) : CompactChartTest :=
  CompactChartTest.ofPlanar g.field g.smooth g.compact g.support

def PlanarChartTest.derivative (g : PlanarChartTest) (v : ℂ) : PlanarChartTest where
  field z := fderiv ℝ g.field z v
  smooth := (g.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  compact := g.compact.fderiv_apply ℝ v
  support := (tsupport_fderiv_apply_subset ℝ v).trans g.support

def PlanarChartTest.conjugate (g : PlanarChartTest) : PlanarChartTest where
  field z := conj (g.field z)
  smooth := Complex.conjCLE.contDiff.comp g.smooth
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

/-- Restricting a planar test to the half-plane preserves its actual chart derivative. -/
theorem PlanarChartTest.weightedDeriv_eq (g : PlanarChartTest) (v : ℂ) (z : UpperHalfPlane) :
    weightedDeriv v g.toChartTest.field z = (z.im : ℂ)*fderiv ℝ g.field (z:ℂ) v := by
  have he : g.toChartTest.field ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g.field := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
      ofComplex_apply_of_im_pos hw]
  unfold weightedDeriv
  rw [he.fderiv_eq]

/-- The original directional derivative commutes with complex conjugation. -/
theorem PlanarChartTest.conjugate_deriv (g : PlanarChartTest) (v z : ℂ) :
    fderiv ℝ g.conjugate.field z v = conj (fderiv ℝ g.field z v) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z
    (g.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
  exact congrArg (fun a : ℂ →L[ℝ] ℂ => a v) hd

/-- Exact chart pushforward of the full hyperbolic volume, including every seam. -/
theorem map_volume_chart_eq : Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane) =
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).withDensity
      (fun z => (chartDensity z : ℝ≥0∞)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs,UpperHalfPlane.volume_eq_lintegral,
    withDensity_apply _ hs,Measure.restrict_restrict hs]
  rw [Set.image_preimage_eq_inter_range,UpperHalfPlane.range_coe]
  rfl

/-- Squared height cancels the actual density on the entire upper half-plane. -/
theorem integral_volume_height_sq_chart (F : ℂ → ℂ) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*F z) = ∫ z in {z : ℂ | 0 < z.im}, F z := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  have hi (G : ℂ → ℂ) : (∫ z : UpperHalfPlane, G z) =
      ∫ z in {z : ℂ | 0 < z.im}, chartDensity z • G z := by
    rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map, map_volume_chart_eq,
      integral_withDensity_eq_integral_smul hm]
  change (∫ z : UpperHalfPlane, (((z:ℂ).im : ℂ)^(2 : ℕ)*F z)) = _
  rw [hi (fun z => (z.im : ℂ)^(2 : ℕ)*F z)]
  apply setIntegral_congr_fun isOpen_upperHalfPlaneSet.measurableSet
  intro z hz
  change 0 < z.im at hz
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    coe_nnnorm,Real.norm_eq_abs,abs_of_pos hz,Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
  field_simp

private theorem chart_continuousOn_full (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f) :
    ContinuousOn (f ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (hf ⟨z,hz⟩).continuousAt.continuousWithinAt

private theorem chart_deriv_continuousOn_full (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f)
    (v : ℂ) : ContinuousOn (fun z => fderiv ℝ (f ∘ ofComplex) z v)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (((hf ⟨z,hz⟩).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
    continuousAt_const).continuousWithinAt

private theorem integrable_planar_test_mul (a : ℂ → ℂ) (g : PlanarChartTest)
    (ha : ContinuousOn a {z : ℂ | 0 < z.im}) :
    Integrable (fun z => a z*g.field z) (volume : Measure ℂ) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right a g.field).trans (subset_tsupport g.field))).mp
  exact ((ha.mono g.support).mul g.smooth.continuous.continuousOn).integrableOn_compact g.compact

/-- Integration by parts for the original weighted derivative over the whole
half-plane. Positive-height compact support discharges every boundary term. -/
theorem weightedDeriv_full_test_identity (f : UpperHalfPlane → ℂ) (hf : ChartSmooth f)
    (g : PlanarChartTest) (v : ℂ) :
    (∫ z : UpperHalfPlane, weightedDeriv v f z*((z.im : ℂ)*g.field z)) =
      -(∫ z : UpperHalfPlane, f z*((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field (z:ℂ) v)) := by
  let F : ℂ → ℂ := f ∘ ofComplex
  have hf'g := integrable_planar_test_mul _ g (chart_deriv_continuousOn_full f hf v)
  have hfg' := integrable_planar_test_mul F (g.derivative v) (chart_continuousOn_full f hf)
  have hfg := integrable_planar_test_mul F g (chart_continuousOn_full f hf)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun z hz => (hf ⟨z,g.support hz⟩).differentiableAt (by simp))
    (fun z _ => g.smooth.differentiable (by simp) z)
  have hL : (∫ z : UpperHalfPlane, weightedDeriv v f z*((z.im : ℂ)*g.field z)) =
      ∫ z : ℂ, fderiv ℝ F z v*g.field z := by
    calc
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*(fderiv ℝ F (z:ℂ) v*g.field z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by unfold weightedDeriv F; ring)
      _ = ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ F z v*g.field z :=
        integral_volume_height_sq_chart (fun z => fderiv ℝ F z v*g.field z)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hn : z ∉ tsupport g.field := fun hg => hz (g.support hg)
        rw [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  have hR : (∫ z : UpperHalfPlane, f z*((z.im : ℂ)^(2 : ℕ)*fderiv ℝ g.field (z:ℂ) v)) =
      ∫ z : ℂ, F z*fderiv ℝ g.field z v := by
    calc
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*(F z*fderiv ℝ g.field (z:ℂ) v) := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [F,Function.comp_apply,ofComplex_apply]
        ring
      _ = ∫ z in {z : ℂ | 0 < z.im}, F z*fderiv ℝ g.field z v :=
        integral_volume_height_sq_chart (fun z => F z*fderiv ℝ g.field z v)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hn : z ∉ tsupport (g.derivative v).field := fun hd => hz ((g.derivative v).support hd)
        change F z*(g.derivative v).field z = 0
        rw [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  rw [hL,hR]
  simpa only [neg_neg] using (congrArg Neg.neg hibp).symm

end
end RHTower.D4BMModularCore
