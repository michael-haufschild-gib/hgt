import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelHasItsFourierMultiplier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalL1Translation
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Boundary values of the logarithmic backward convolution

Bounded measurable forcing pairs continuously with translated copies of the
integrable causal kernel. The kernel is square-integrable away from zero,
so dominated convergence handles remote L² forcing. Splitting these two parts
gives an absolutely convergent readout, continuous at zero, whenever the L²
forcing is essentially bounded near the endpoint.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The literal backward convolution which supplies the half-line boundary readout. -/
def logarithmicBackwardConvolution (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, (logarithmicCausalKernel (y - x) : ℂ) * f y

theorem logarithmicBackwardConvolution_congr {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    logarithmicBackwardConvolution f = logarithmicBackwardConvolution g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

theorem measurable_logarithmicBackwardConvolution {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (logarithmicBackwardConvolution f) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  exact ((Complex.continuous_ofReal.measurable.comp
    (measurable_logarithmicCausalKernel.comp (measurable_snd.sub measurable_fst))).mul
      (hf.comp measurable_snd)).stronglyMeasurable

theorem integrable_logarithmicBackwardConvolution_of_bounded {f : ℝ → ℂ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    Integrable (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ) * f y) := by
  have ht : Integrable (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ)) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable
        integrable_complex_logarithmicCausalKernel
  exact ht.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall hb)

/-- Integrable translation against bounded forcing is continuous, even when the forcing is rough. -/
theorem continuous_logarithmicBackwardConvolution_of_bounded {f : ℝ → ℂ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖f y‖ ≤ C) :
    Continuous (logarithmicBackwardConvolution f) := by
  let hv := memLp_one_iff_integrable.mpr integrable_complex_logarithmicCausalKernel
  let g : Lp ℂ 1 (volume : Measure ℝ) := hv.toLp (fun y => (logarithmicCausalKernel y : ℂ))
  let M := lpBoundedMulCLM (p := 1) (μ := (volume : Measure ℝ)) hf hC hb
  have hi : Continuous (fun w : Lp ℂ 1 (volume : Measure ℝ) => ∫ y : ℝ, w y) := by
    simpa only [ContinuousLinearMap.id_apply] using
      (ContinuousLinearMap.id ℂ ℂ).continuous_integral_comp_L1 (μ := (volume : Measure ℝ))
  have hc := hi.comp (M.continuous.comp ((RHTower.continuous_realL1Translate g).comp continuous_neg))
  apply hc.congr
  intro x
  change (∫ y : ℝ, (M (RHTower.realL1Translate (-x) g)) y) = _
  apply integral_congr_ae
  have hg : (g : ℝ → ℂ) =ᵐ[volume] fun y => (logarithmicCausalKernel y : ℂ) := hv.coeFn_toLp
  have ht := hg.comp_tendsto
    (RHTower.measurePreserving_realAddTranslationFamily (-x)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [lpBoundedMulCLM_coeFn (p := 1) (μ := (volume : Measure ℝ)) hf hC hb
    (RHTower.realL1Translate (-x) g), RHTower.realL1Translate_ae (-x) g, ht] with y hM hy hyt
  change g (-x + y) = (logarithmicCausalKernel (-x + y) : ℂ) at hyt
  rw [hM, hy, hyt]
  rw [show -x + y = y - x by ring, mul_comm]

/-- The causal density is square-integrable on every ray separated from its singular endpoint. -/
theorem memLp_logarithmicCausalKernel_away {δ : ℝ} (hδ : 0 < δ) :
    MemLp ((Ici δ).indicator (fun y : ℝ => (logarithmicCausalKernel y : ℂ))) 2 volume := by
  have hm : Measurable ((Ici δ).indicator (fun y : ℝ => (logarithmicCausalKernel y : ℂ))) :=
    (Complex.continuous_ofReal.measurable.comp measurable_logarithmicCausalKernel).indicator measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (logarithmicCausalKernel_mass_one.1.const_mul (logarithmicCausalKernel δ)).mono'
    (hm.aestronglyMeasurable.norm.pow 2)
  filter_upwards with y
  simp only [Pi.pow_apply]
  by_cases hy : δ ≤ y
  · rw [indicator_of_mem (s := Ici δ) hy, Complex.norm_real,
      Real.norm_of_nonneg (logarithmicCausalKernel_nonneg y), Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [pow_two] using mul_le_mul_of_nonneg_right
      (antitoneOn_logarithmicCausalKernel hδ (hδ.trans_le hy) hy)
      (logarithmicCausalKernel_nonneg y)
  · rw [indicator_of_notMem (s := Ici δ) hy, norm_zero, zero_pow (by norm_num), norm_zero]
    exact mul_nonneg (logarithmicCausalKernel_nonneg _) (logarithmicCausalKernel_nonneg _)

private theorem memLp_logarithmicCausalKernel_shift_away {δ x : ℝ} (hx : x < δ) :
    MemLp (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ)) 2
      (volume.restrict (Ioi δ)) := by
  have ht := (memLp_logarithmicCausalKernel_away (sub_pos.mpr hx)).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) (-x))
  apply (memLp_congr_ae (μ := volume.restrict (Ioi δ)) ?_).mp (ht.restrict (Ioi δ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change δ < y at hy
  change ((Ici (δ - x)).indicator (fun s : ℝ => (logarithmicCausalKernel s : ℂ))) (y + -x) = _
  rw [indicator_of_mem (show y + -x ∈ Ici (δ - x) by change δ - x ≤ y + -x; linarith only [hy])]
  rfl

/-- Essential local boundedness makes the literal readout integral absolutely convergent. -/
theorem integrable_logarithmicBackwardConvolution_of_ae_locally_bounded {f : ℝ → ℂ}
    (hm : Measurable f) (h2 : MemLp f 2 volume) {δ C x : ℝ} (hx : x < δ)
    (hb : ∀ᵐ y ∂volume, y ≤ δ → ‖f y‖ ≤ C) :
    Integrable (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ) * f y) := by
  have ht : Integrable (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ)) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable
        integrable_complex_logarithmicCausalKernel
  have hlocal : IntegrableOn (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ) * f y) (Iic δ) :=
    ht.integrableOn.mul_bdd hm.aestronglyMeasurable.restrict
      ((ae_restrict_iff' measurableSet_Iic).mpr hb)
  have hremote : IntegrableOn (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ) * f y) (Ioi δ) :=
    (memLp_logarithmicCausalKernel_shift_away hx).integrable_mul (h2.restrict (Ioi δ))
  have hu := hlocal.union hremote
  have he : Iic δ ∪ Ioi δ = (univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt y δ
  rw [he] at hu
  exact integrableOn_univ.mp hu

/-- Remote L² forcing has a continuous boundary readout: the translated kernel stays away from zero. -/
theorem continuousAt_logarithmicBackwardConvolution_remote {f : ℝ → ℂ}
    (hm : Measurable f) (h2 : MemLp f 2 volume) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousAt (fun x : ℝ => ∫ y in Ioi δ, (logarithmicCausalKernel (y - x) : ℂ) * f y) 0 := by
  have hhalf : δ / 2 < δ := by linarith only [hδ]
  have hmajor : IntegrableOn (fun y : ℝ => logarithmicCausalKernel (y - δ / 2) * ‖f y‖) (Ioi δ) := by
    have hi := ((memLp_logarithmicCausalKernel_shift_away hhalf).integrable_mul (h2.restrict (Ioi δ))).norm
    apply hi.congr
    filter_upwards with y
    rw [Pi.mul_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => logarithmicCausalKernel (y - δ / 2) * ‖f y‖)
  · exact Eventually.of_forall fun x =>
      ((Complex.continuous_ofReal.measurable.comp
        (measurable_logarithmicCausalKernel.comp (measurable_id.sub measurable_const))).mul hm).aestronglyMeasurable
  · filter_upwards [eventually_lt_nhds (show (0 : ℝ) < δ / 2 by linarith only [hδ])] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change δ < y at hy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact antitoneOn_logarithmicCausalKernel (by change 0 < y - δ / 2; linarith only [hy, hδ])
      (by change 0 < y - x; linarith only [hy, hx, hδ]) (by linarith only [hx])
  · exact hmajor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hypos : 0 < y := hδ.trans hy
    have hc : ContinuousAt logarithmicCausalKernel y :=
      (continuousOn_logarithmicCausalKernel y hypos).continuousAt (isOpen_Ioi.mem_nhds hypos)
    have hpath : Tendsto (fun x : ℝ => y - x) (𝓝 (0 : ℝ)) (nhds y) := by
      simpa only [Pi.sub_apply, id_eq, sub_zero] using!
        ((continuous_const : Continuous (fun _ : ℝ => y)).sub continuous_id).tendsto (0 : ℝ)
    simpa only [Function.comp_def, sub_zero] using!
      ((Complex.continuous_ofReal.tendsto _).comp (hc.tendsto.comp hpath)).mul_const (f y)

/-- Local boundedness at the endpoint suffices; the remaining forcing need only belong to L². -/
theorem continuousAt_logarithmicBackwardConvolution_of_locally_bounded {f : ℝ → ℂ}
    (hm : Measurable f) (h2 : MemLp f 2 volume) {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hb : ∀ y ≤ δ, ‖f y‖ ≤ C) :
    ContinuousAt (logarithmicBackwardConvolution f) 0 := by
  let f₀ : ℝ → ℂ := (Iic δ).indicator f
  have hm₀ : Measurable f₀ := hm.indicator measurableSet_Iic
  have hb₀ : ∀ y, ‖f₀ y‖ ≤ C := by
    intro y
    by_cases hy : y ≤ δ
    · simpa only [f₀, indicator_of_mem (s := Iic δ) hy] using hb y hy
    · simpa only [f₀, indicator_of_notMem (s := Iic δ) hy, norm_zero] using hC
  have hsplit (x : ℝ) (hx : x < δ) : logarithmicBackwardConvolution f x =
      logarithmicBackwardConvolution f₀ x +
        ∫ y in Ioi δ, (logarithmicCausalKernel (y - x) : ℂ) * f y := by
    have hlocal := integrable_logarithmicBackwardConvolution_of_bounded hm₀ hb₀ x
    have hremote : IntegrableOn (fun y : ℝ => (logarithmicCausalKernel (y - x) : ℂ) * f y) (Ioi δ) :=
      (memLp_logarithmicCausalKernel_shift_away hx).integrable_mul (h2.restrict (Ioi δ))
    unfold logarithmicBackwardConvolution
    calc
      _ = ∫ y : ℝ, (logarithmicCausalKernel (y - x) : ℂ) * f₀ y +
          (Ioi δ).indicator (fun y => (logarithmicCausalKernel (y - x) : ℂ) * f y) y := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y ≤ δ
        · simp only [f₀, indicator_of_mem (s := Iic δ) hy,
            indicator_of_notMem (s := Ioi δ) (not_lt.mpr hy), add_zero]
        · simp only [f₀, indicator_of_notMem (s := Iic δ) hy,
            indicator_of_mem (s := Ioi δ) (lt_of_not_ge hy), mul_zero, zero_add]
      _ = _ := by
        rw [integral_add hlocal (hremote.integrable_indicator measurableSet_Ioi),
          integral_indicator measurableSet_Ioi]
  have hc : ContinuousAt (logarithmicBackwardConvolution f₀) 0 :=
    (continuous_logarithmicBackwardConvolution_of_bounded hm₀ hC hb₀).continuousAt
  have hr := continuousAt_logarithmicBackwardConvolution_remote hm h2 hδ
  have hl := hc.tendsto.add hr.tendsto
  rw [← hsplit 0 hδ] at hl
  apply hl.congr'
  filter_upwards [eventually_lt_nhds hδ] with x hx
  exact (hsplit x hx).symm

/-- The boundary readout depends only on the L² class, so essential local bounds suffice. -/
theorem continuousAt_logarithmicBackwardConvolution_of_ae_locally_bounded {f : ℝ → ℂ}
    (hm : Measurable f) (h2 : MemLp f 2 volume) {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hb : ∀ᵐ y ∂volume, y ≤ δ → ‖f y‖ ≤ C) :
    ContinuousAt (logarithmicBackwardConvolution f) 0 := by
  let S : Set ℝ := {y | ‖f y‖ ≤ C} ∪ Ioi δ
  have hS : MeasurableSet S := (measurableSet_le hm.norm measurable_const).union measurableSet_Ioi
  have heq : S.indicator f =ᵐ[volume] f := by
    filter_upwards [hb] with y hy
    apply indicator_of_mem
    by_cases hyδ : y ≤ δ
    · exact Or.inl (hy hyδ)
    · exact Or.inr (lt_of_not_ge hyδ)
  have hbound : ∀ y ≤ δ, ‖S.indicator f y‖ ≤ C := by
    intro y hy
    by_cases hyS : y ∈ S
    · rw [indicator_of_mem hyS]
      rcases hyS with hb | hfar
      · exact hb
      · exact False.elim ((not_lt.mpr hy) hfar)
    · rw [indicator_of_notMem hyS, norm_zero]
      exact hC
  have hc := continuousAt_logarithmicBackwardConvolution_of_locally_bounded
    (hm.indicator hS) (h2.indicator hS) hδ hC hbound
  rwa [logarithmicBackwardConvolution_congr heq] at hc

#print axioms continuous_logarithmicBackwardConvolution_of_bounded
#print axioms memLp_logarithmicCausalKernel_away
#print axioms continuousAt_logarithmicBackwardConvolution_remote
#print axioms continuousAt_logarithmicBackwardConvolution_of_locally_bounded
#print axioms continuousAt_logarithmicBackwardConvolution_of_ae_locally_bounded

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
