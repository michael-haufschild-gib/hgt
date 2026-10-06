import GaloisForLFunctions.RHTower.ChiCubicSelectedKernelEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong weighted convergence of the actual selected reciprocal kernels

The literal shrinking-cutoff Gaussian/logarithmic slice tends pointwise to
its sharp-band limit. A fixed physical cube dominates the full three-variable
kernel, including its window, conjugate, reciprocal factor and curvature.
Fubini and dominated convergence identify the actual limiting kernel.

For each order below 3/2, the admitted uniform energy at an intermediate
higher order bounds the limiting energy by Fatou. Compact-frequency
convergence and the gap between the two orders then give global strong
weighted L2 convergence. No assumed stationary profile, regularity budget,
or cancellation estimate enters the public results. Physical logarithmic
coordinate transfer and Mellin line tails remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem selected_parameters_eventually :
    ∀ᶠ N : ℝ in atTop, N^(-(3/4 : ℝ))∈Ioo (0 : ℝ) (1/2) ∧
      1/Real.log N∈Icc (0 : ℝ) 1 := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hdN
  have hN1 : 1<N := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) hN
  have hN0 : 0<N := zero_lt_one.trans hN1
  have hL : 1 ≤ Real.log N := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hN
  exact ⟨⟨Real.rpow_pos_of_pos hN0 _,hdN⟩,
    div_nonneg zero_le_one (by linarith),
    (div_le_iff₀ (Real.log_pos hN1)).mpr (by simpa using hL)⟩

/-- The literal sharp-band limiting Gaussian slice. -/
def bagCubicSharpSlice (x : ℝ) : ℂ := (Ioo (1 : ℝ) 2).indicator smoothAFECutoff x

private theorem normalized_slice_norm_le_one
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) (x : ℝ) :
    ‖bagCubicNormalizedSlice δ.1 h.1 x‖ ≤ 1 := by
  by_cases hx : x∈Icc (1 : ℝ) 2
  · have hd : 1 ≤ 1+h.1*Real.log x := by nlinarith [mul_nonneg h.2.1 (Real.log_nonneg hx.1)]
    have hc := (bagCubicControlledCutoff_properties δ).2.2.1 x
    change ‖(bagCubicControlledCutoff δ.1 x : ℂ)*
      (smoothAFECutoff x/((1+h.1*Real.log x : ℝ) : ℂ))‖ ≤ 1
    simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hd),abs_of_nonneg hc.1]
    have hv : ‖smoothAFECutoff x‖/(1+h.1*Real.log x) ≤ 1 :=
      (div_le_one (by linarith)).mpr ((norm_smoothAFECutoff_le_one (zero_lt_one.trans_le hx.1)).trans hd)
    exact (mul_le_mul hc.2 hv (by positivity) zero_le_one).trans_eq (by ring)
  · rw [(bagCubicNormalizedSlice_properties δ h).2 x hx,norm_zero]
    norm_num

/-- Pointwise limit of the actual shrinking-cutoff and logarithmic slice. -/
theorem bagCubicNormalizedSlice_selected_tendsto (x : ℝ) :
    Tendsto (fun N : ℝ => bagCubicNormalizedSlice (N^(-(3/4 : ℝ))) (1/Real.log N) x)
      atTop (𝓝 (bagCubicSharpSlice x)) := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  have hh : Tendsto (fun N : ℝ => 1/Real.log N) atTop (𝓝 0) :=
    by simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  by_cases hx : x∈Ioo (1 : ℝ) 2
  · have he : ∀ᶠ N : ℝ in atTop,
        bagCubicNormalizedSlice (N^(-(3/4 : ℝ))) (1/Real.log N) x =
          smoothAFECutoff x/((1+(1/Real.log N)*Real.log x : ℝ) : ℂ) := by
      filter_upwards [selected_parameters_eventually,
        hd.eventually (Iio_mem_nhds (sub_pos.mpr hx.1)),
        hd.eventually (Iio_mem_nhds (sub_pos.mpr hx.2))] with N hN hleft hright
      let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} := ⟨N^(-(3/4 : ℝ)),hN.1⟩
      have hp : x∈Icc (1+δ.1) (2-δ.1) := ⟨by dsimp only [δ]; linarith,by dsimp only [δ]; linarith⟩
      have hc := (bagCubicControlledCutoff_properties δ).2.2.2.2 x hp
      change (bagCubicControlledCutoff δ.1 x : ℂ)*_=_
      rw [hc,Complex.ofReal_one,one_mul]
      rfl
    have hden : Tendsto (fun N : ℝ => ((1+(1/Real.log N)*Real.log x : ℝ) : ℂ)) atTop (𝓝 1) := by
      simpa only [zero_mul,add_zero,Complex.ofReal_one] using
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hh.mul_const (Real.log x))).ofReal
    have ht := (tendsto_const_nhds (x := smoothAFECutoff x)).div hden (by norm_num : (1 : ℂ)≠0)
    simpa only [div_one,bagCubicSharpSlice,indicator_of_mem hx] using ht.congr' (Filter.EventuallyEq.symm he)
  · have he : ∀ᶠ N : ℝ in atTop,
        bagCubicNormalizedSlice (N^(-(3/4 : ℝ))) (1/Real.log N) x=0 := by
      filter_upwards [selected_parameters_eventually] with N hN
      have hz := (bagCubicControlledCutoff_properties ⟨_,hN.1⟩).2.2.2.1 x hx
      change (bagCubicControlledCutoff _ x : ℂ)*_=0
      rw [hz,Complex.ofReal_zero,zero_mul]
    simpa only [bagCubicSharpSlice,indicator_of_notMem hx] using
      (tendsto_const_nhds (x := (0 : ℂ))).congr' (Filter.EventuallyEq.symm he)

private theorem sharp_slice_measurable : Measurable bagCubicSharpSlice := by
  classical
  have hc : ContinuousOn smoothAFECutoff (Ioo (1 : ℝ) 2) :=
    contDiffOn_smoothAFECutoff_infty_pos.continuousOn.mono (fun _ hx => zero_lt_one.trans hx.1)
  have he : bagCubicSharpSlice = (Ioo (1 : ℝ) 2).piecewise smoothAFECutoff (fun _ => (0 : ℂ)) := by
    funext x
    by_cases hx : x∈Ioo (1 : ℝ) 2 <;> simp [bagCubicSharpSlice,Set.piecewise,hx]
  rw [he]
  exact hc.measurable_piecewise continuousOn_const measurableSet_Ioo

private theorem sharp_slice_norm_le_one (x : ℝ) : ‖bagCubicSharpSlice x‖ ≤ 1 := by
  by_cases hx : x∈Ioo (1 : ℝ) 2
  · simpa only [bagCubicSharpSlice,indicator_of_mem hx] using
      norm_smoothAFECutoff_le_one (zero_lt_one.trans hx.1)
  · simp only [bagCubicSharpSlice,indicator_of_notMem hx,norm_zero,zero_le_one]

private theorem sharp_slice_off (x : ℝ) (hx : x∉Icc (1 : ℝ) 2) : bagCubicSharpSlice x=0 :=
  indicator_of_notMem (fun h => hx ⟨h.1.le,h.2.le⟩) _

private def physicalCube : Set (ℝ×(ℝ×ℝ)) := Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2)
private def cubeMajorant : ℝ×(ℝ×ℝ)→ℝ := physicalCube.indicator (fun _ => 1)
private theorem physical_cube_measurable : MeasurableSet physicalCube :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
private theorem cube_majorant_integrable : Integrable cubeMajorant := by
  have hi : IntegrableOn (fun _ : ℝ×(ℝ×ℝ) => (1 : ℝ)) physicalCube :=
    integrableOn_const (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top.ne
  exact hi.integrable_indicator physical_cube_measurable

private def reciprocalStage (F : ℝ→ℂ) (a b c : ℝ) (z : ℝ×(ℝ×ℝ)) : ℂ :=
  F z.2.2*F z.2.1*star (F z.1)/(z.1 : ℂ)^2*
    (bagPhysicalHeightWindow (z.2.2*z.2.1/z.1) : ℂ)*
      bourgainOscillation (-(z.2.2*b+z.2.1*a+c)/z.1)

private theorem stage_measurable {F : ℝ→ℂ} (hF : Measurable F) (a b c : ℝ) :
    Measurable (reciprocalStage F a b c) := by
  have hW : Measurable (bagPhysicalHeightWindow : ℝ→ℝ) :=
    (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous.measurable
  unfold reciprocalStage bourgainOscillation
  fun_prop

private theorem stage_norm_bound {F : ℝ→ℂ} (hb : ∀x, ‖F x‖ ≤ 1)
    (hz : ∀x, x∉Icc (1 : ℝ) 2 → F x=0) (a b c : ℝ) (z : ℝ×(ℝ×ℝ)) :
    ‖reciprocalStage F a b c z‖ ≤ cubeMajorant z := by
  by_cases hmem : z∈physicalCube
  · have hr : 1 ≤ z.1 := hmem.1.1
    have hd : 1 ≤ |z.1|^2 := by rw [abs_of_nonneg (by linarith)]; nlinarith
    have hp : ‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖ ≤ 1 := by
      calc ‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖  ≤  1*1*1 := by gcongr <;> apply hb
        _ = 1 := by norm_num
    have hq : (‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖)/|z.1|^2 ≤ 1 :=
      (div_le_one (by linarith)).mpr (hp.trans hd)
    simp only [reciprocalStage,norm_mul,norm_div,norm_star,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,norm_bourgainOscillation,mul_one,cubeMajorant,indicator_of_mem hmem,
      abs_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact (mul_le_mul hq bagPhysicalHeightWindow.le_one bagPhysicalHeightWindow.nonneg zero_le_one).trans_eq (by ring)
  · rw [cubeMajorant,indicator_of_notMem hmem]
    have he : reciprocalStage F a b c z=0 := by
      by_cases hr : z.1∈Icc (1 : ℝ) 2
      · by_cases hq : z.2.1∈Icc (1 : ℝ) 2
        · have hp : z.2.2∉Icc (1 : ℝ) 2 := fun hp => hmem ⟨hr,hq,hp⟩
          simp only [reciprocalStage,hz _ hp,zero_mul,zero_div]
        · simp only [reciprocalStage,hz _ hq,mul_zero,zero_mul,zero_div]
      · simp only [reciprocalStage,hz _ hr,star_zero,mul_zero,zero_div,zero_mul]
    rw [he,norm_zero]

private theorem stage_integrable {F : ℝ→ℂ} (hF : Measurable F) (hb : ∀x, ‖F x‖ ≤ 1)
    (hz : ∀x, x∉Icc (1 : ℝ) 2 → F x=0) (a b c : ℝ) :
    Integrable (reciprocalStage F a b c) :=
  cube_majorant_integrable.mono' (stage_measurable hF a b c).aestronglyMeasurable
    (Eventually.of_forall (stage_norm_bound hb hz a b c))

private theorem stage_integral_eq {F : ℝ→ℂ} (hF : Measurable F) (hb : ∀x, ‖F x‖ ≤ 1)
    (hz : ∀x, x∉Icc (1 : ℝ) 2 → F x=0) (a b c : ℝ) :
    (∫z : ℝ×(ℝ×ℝ), reciprocalStage F a b c z)=
      ∫r : ℝ,∫q : ℝ,∫p : ℝ,
        F p*F q*star (F r)/(r : ℂ)^2*(bagPhysicalHeightWindow (p*q/r) : ℂ)*
          bourgainOscillation (-(p*b+q*a+c)/r) := by
  have hi := stage_integrable hF hb hz a b c
  change (∫z : ℝ×(ℝ×ℝ), reciprocalStage F a b c z ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with r hr
  exact integral_prod _ hr

/-- Explicit limiting sharp-band reciprocal kernel, with zero curvature. -/
def bagCubicSharpReciprocalKernel (a b : ℝ) : ℂ :=
  ∫r : ℝ,∫q : ℝ,∫p : ℝ,
    bagCubicSharpSlice p*bagCubicSharpSlice q*star (bagCubicSharpSlice r)/(r : ℂ)^2*
      (bagPhysicalHeightWindow (p*q/r) : ℂ)*bourgainOscillation (-(p*b+q*a)/r)

private theorem stage_selected_tendsto (tau a b : ℝ) (z : ℝ×(ℝ×ℝ)) :
    Tendsto (fun N : ℝ => reciprocalStage
      (bagCubicNormalizedSlice (N^(-(3/4 : ℝ))) (1/Real.log N)) a b ((tau/N)*a*b) z)
      atTop (𝓝 (reciprocalStage bagCubicSharpSlice a b 0 z)) := by
  have htau : Tendsto (fun N : ℝ => (tau/N)*a*b) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,div_eq_mul_inv] using
      ((tendsto_const_nhds (x := tau)).mul (tendsto_inv_atTop_zero :
        Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0))).mul_const a |>.mul_const b
  have hphase : Tendsto (fun N : ℝ => -(z.2.2*b+z.2.1*a+(tau/N)*a*b)/z.1)
      atTop (𝓝 (-(z.2.2*b+z.2.1*a+0)/z.1)) :=
    (tendsto_const_nhds.add htau).neg.div_const _
  have hosc : Tendsto (fun N : ℝ => bourgainOscillation (-(z.2.2*b+z.2.1*a+(tau/N)*a*b)/z.1))
      atTop (𝓝 (bourgainOscillation (-(z.2.2*b+z.2.1*a+0)/z.1))) := by
    unfold bourgainOscillation
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hphase.ofReal)
  exact ((((bagCubicNormalizedSlice_selected_tendsto z.2.2).mul
    (bagCubicNormalizedSlice_selected_tendsto z.2.1)).mul
    (bagCubicNormalizedSlice_selected_tendsto z.1).star).div_const _ |>.mul_const _).mul hosc

/-- The actual selected moving kernel converges to its explicit sharp-band limit. -/
theorem bagCubicReciprocalKernel_selected_tendsto (tau a b : ℝ) :
    Tendsto (fun N : ℝ => bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N)
      a b ((tau/N)*a*b)) atTop (𝓝 (bagCubicSharpReciprocalKernel a b)) := by
  let f := fun (N : ℝ) => reciprocalStage
    (bagCubicNormalizedSlice (N^(-(3/4 : ℝ))) (1/Real.log N)) a b ((tau/N)*a*b)
  have hm : ∀ᶠ N : ℝ in atTop, AEStronglyMeasurable (f N) volume := by
    filter_upwards [selected_parameters_eventually] with N hN
    exact (stage_measurable (bagCubicNormalizedSlice_properties ⟨_,hN.1⟩ ⟨_,hN.2⟩).1.continuous.measurable _ _ _).aestronglyMeasurable
  have hb : ∀ᶠ N : ℝ in atTop, ∀ᵐ z, ‖f N z‖ ≤ cubeMajorant z := by
    filter_upwards [selected_parameters_eventually] with N hN
    exact Eventually.of_forall (stage_norm_bound
      (normalized_slice_norm_le_one ⟨_,hN.1⟩ ⟨_,hN.2⟩)
      (bagCubicNormalizedSlice_properties ⟨_,hN.1⟩ ⟨_,hN.2⟩).2 _ _ _)
  have ht := tendsto_integral_filter_of_dominated_convergence cubeMajorant hm hb
    cube_majorant_integrable (Eventually.of_forall (stage_selected_tendsto tau a b))
  have he : ∀ᶠ N : ℝ in atTop, (∫z, f N z)=
      bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) a b ((tau/N)*a*b) := by
    filter_upwards [selected_parameters_eventually] with N hN
    exact stage_integral_eq (bagCubicNormalizedSlice_properties ⟨_,hN.1⟩ ⟨_,hN.2⟩).1.continuous.measurable
      (normalized_slice_norm_le_one ⟨_,hN.1⟩ ⟨_,hN.2⟩)
      (bagCubicNormalizedSlice_properties ⟨_,hN.1⟩ ⟨_,hN.2⟩).2 _ _ _
  have hsharp : (∫z : ℝ×(ℝ×ℝ), reciprocalStage bagCubicSharpSlice a b 0 z)=
      bagCubicSharpReciprocalKernel a b := by
    simpa only [bagCubicSharpReciprocalKernel,add_zero] using
      stage_integral_eq sharp_slice_measurable sharp_slice_norm_le_one sharp_slice_off a b 0
  rw [hsharp] at ht
  exact ht.congr' he

private def selectedKernel (tau N : ℝ) (ab : ℝ×ℝ) : ℂ :=
  bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) ab.1 ab.2 ((tau/N)*ab.1*ab.2)
private def sharpKernel (ab : ℝ×ℝ) : ℂ := bagCubicSharpReciprocalKernel ab.1 ab.2
private def flatKernel (F : ℝ→ℂ) (lam : ℝ) (ab : ℝ×ℝ) : ℂ :=
  ∫z : ℝ×(ℝ×ℝ), reciprocalStage F ab.1 ab.2 (lam*ab.1*ab.2) z

private theorem flat_kernel_measurable {F : ℝ→ℂ} (hF : Measurable F) (lam : ℝ) :
    Measurable (flatKernel F lam) := by
  have hW : Measurable (bagPhysicalHeightWindow : ℝ→ℝ) :=
    (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous.measurable
  have hm : Measurable (fun w : (ℝ×ℝ)×(ℝ×(ℝ×ℝ)) =>
      reciprocalStage F w.1.1 w.1.2 (lam*w.1.1*w.1.2) w.2) := by
    unfold reciprocalStage bourgainOscillation
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem flat_kernel_bound {F : ℝ→ℂ} (hF : Measurable F) (hb : ∀x, ‖F x‖ ≤ 1)
    (hz : ∀x, x∉Icc (1 : ℝ) 2 → F x=0) (lam : ℝ) (ab : ℝ×ℝ) :
    ‖flatKernel F lam ab‖ ≤ ∫z, cubeMajorant z := by
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono (stage_integrable hF hb hz _ _ _).norm cube_majorant_integrable
      (stage_norm_bound hb hz _ _ _))

private theorem selected_kernel_measurable_bounded (tau : ℝ) :
    ∃ B : ℝ, 0<B ∧ Measurable sharpKernel ∧ (∀ab, ‖sharpKernel ab‖ ≤ B) ∧
      ∀ᶠ N : ℝ in atTop, Measurable (selectedKernel tau N) ∧ ∀ab, ‖selectedKernel tau N ab‖ ≤ B := by
  let mass := ∫z : ℝ×(ℝ×ℝ), cubeMajorant z
  have hm : 0  ≤  mass := integral_nonneg (fun z => by
    simp only [cubeMajorant]; exact indicator_nonneg (fun _ _ => zero_le_one) z)
  have hsharp : sharpKernel=flatKernel bagCubicSharpSlice 0 := by
    funext ab
    simpa only [flatKernel,sharpKernel,bagCubicSharpReciprocalKernel,zero_mul,add_zero] using
      (stage_integral_eq sharp_slice_measurable sharp_slice_norm_le_one sharp_slice_off ab.1 ab.2 0).symm
  refine ⟨mass+1,by linarith,?_,?_,?_⟩
  · rw [hsharp]
    exact flat_kernel_measurable sharp_slice_measurable 0
  · intro ab
    rw [hsharp]
    exact (flat_kernel_bound sharp_slice_measurable sharp_slice_norm_le_one sharp_slice_off 0 ab).trans (by dsimp only [mass]; linarith)
  · filter_upwards [selected_parameters_eventually] with N hN
    let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} := ⟨_,hN.1⟩
    let h : {r : ℝ // r∈Icc (0 : ℝ) 1} := ⟨_,hN.2⟩
    have hF := (bagCubicNormalizedSlice_properties δ h).1.continuous.measurable
    have hb := normalized_slice_norm_le_one δ h
    have hz := (bagCubicNormalizedSlice_properties δ h).2
    have he : selectedKernel tau N=flatKernel (bagCubicNormalizedSlice δ.1 h.1) (tau/N) := by
      funext ab
      exact (stage_integral_eq hF hb hz _ _ _).symm
    rw [he]
    exact ⟨flat_kernel_measurable hF _,fun ab => (flat_kernel_bound hF hb hz _ ab).trans (by dsimp only [mass]; linarith)⟩

private def frequencyWeight (ab : ℝ×ℝ) : ℝ := 1+|ab.1|+|ab.2|
private theorem frequency_weight_one_le (ab : ℝ×ℝ) : 1 ≤ frequencyWeight ab := by
  dsimp only [frequencyWeight]; linarith [abs_nonneg ab.1,abs_nonneg ab.2]
private theorem frequency_weight_measurable : Measurable frequencyWeight := by
  unfold frequencyWeight
  fun_prop

private theorem selected_local_energy_tendsto (tau s R : ℝ) (hs : 0 ≤ s) (hR : 0 ≤ R) :
    Tendsto (fun N : ℝ => ∫ab : ℝ×ℝ in Icc (-R) R ×ˢ Icc (-R) R,
      (frequencyWeight ab)^(2*s)*‖selectedKernel tau N ab-sharpKernel ab‖^2)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hm,hb,hN⟩ := selected_kernel_measurable_bounded tau
  let S : Set (ℝ×ℝ) := Icc (-R) R ×ˢ Icc (-R) R
  let D := (1+2*R)^(2*s)*(2*B)^2
  have hmN : ∀ᶠ N : ℝ in atTop, AEStronglyMeasurable
      (fun ab => (frequencyWeight ab)^(2*s)*‖selectedKernel tau N ab-sharpKernel ab‖^2)
      (volume.restrict S) := by
    filter_upwards [hN] with N hN
    exact ((frequency_weight_measurable.pow_const _).mul ((hN.1.sub hm).norm.pow_const 2)).aestronglyMeasurable
  have hdN : ∀ᶠ N : ℝ in atTop, ∀ᵐ ab ∂volume.restrict S,
      ‖(frequencyWeight ab)^(2*s)*‖selectedKernel tau N ab-sharpKernel ab‖^2‖ ≤ D := by
    filter_upwards [hN] with N hN
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with ab hab
    have ha : |ab.1| ≤ R := abs_le.mpr hab.1
    have hbR : |ab.2| ≤ R := abs_le.mpr hab.2
    have hw : frequencyWeight ab ≤ 1+2*R := by dsimp only [frequencyWeight]; linarith
    have hn : ‖selectedKernel tau N ab-sharpKernel ab‖ ≤ 2*B :=
      (norm_sub_le _ _).trans (by linarith [hN.2 ab,hb ab])
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (frequency_weight_one_le ab)) _) (sq_nonneg _))]
    exact mul_le_mul (Real.rpow_le_rpow (zero_le_one.trans (frequency_weight_one_le ab)) hw (by positivity))
      (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _) (by positivity)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ×ℝ => D) hmN hdN
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)
    (Eventually.of_forall (fun ab : ℝ×ℝ => show Tendsto
      (fun N : ℝ => (frequencyWeight ab)^(2*s)*‖selectedKernel tau N ab-sharpKernel ab‖^2)
      atTop (𝓝 (0 : ℝ)) from by
      simpa only [selectedKernel,sharpKernel,sub_self,norm_zero,zero_pow (by omega : 2≠0),mul_zero] using
        (tendsto_const_nhds (x := (frequencyWeight ab)^(2*s))).mul
          (((bagCubicReciprocalKernel_selected_tendsto tau ab.1 ab.2).sub (tendsto_const_nhds (x := bagCubicSharpReciprocalKernel ab.1 ab.2))).norm.pow 2)))
  simpa only [integral_zero] using ht

private theorem integral_limit_bound {f : ℝ→(ℝ×ℝ)→ℝ} {g : (ℝ×ℝ)→ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : Measurable g) (hgn : ∀z, 0 ≤ g z)
    (hfn : ∀N z, 0 ≤ f N z) (hlim : ∀z, Tendsto (fun N => f N z) atTop (𝓝 (g z)))
    (hbound : ∀ᶠ N : ℝ in atTop, Integrable (f N) ∧ (∫z, f N z) ≤ C) :
    Integrable g ∧ (∫z, g z) ≤ C := by
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hbound
  let F := fun (N : ℝ) => f (max N0 N)
  have hFi (N : ℝ) : Integrable (F N) := (hN0 _ (le_max_left _ _)).1
  have hFb (N : ℝ) : (∫z, F N z) ≤ C := (hN0 _ (le_max_left _ _)).2
  have hmax : Tendsto (fun N : ℝ => max N0 N) atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_right N0 N) tendsto_id
  have hlimit (z : ℝ×ℝ) : Tendsto (fun N : ℝ => ENNReal.ofReal (F N z)) atTop (𝓝 (ENNReal.ofReal (g z))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hlim z).comp hmax)
  have hfat : (∫⁻z, ENNReal.ofReal (g z)) ≤ ENNReal.ofReal C := by
    calc (∫⁻z, ENNReal.ofReal (g z))
        = ∫⁻z, liminf (fun N : ℝ => ENNReal.ofReal (F N z)) atTop :=
          lintegral_congr (fun z => (hlimit z).liminf_eq.symm)
      _  ≤  liminf (fun N : ℝ => ∫⁻z, ENNReal.ofReal (F N z)) atTop :=
        lintegral_liminf_le' (fun N => (hFi N).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _  ≤  ENNReal.ofReal C := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        apply Eventually.of_forall
        intro N
        rw [←ofReal_integral_eq_lintegral_ofReal (hFi N) (Eventually.of_forall (hfn _))]
        exact ENNReal.ofReal_le_ofReal (hFb N)
  have hi : Integrable g := ⟨hg.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hgn)).mpr
      (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hgn)]

private def weightedEnergy (s : ℝ) (F : (ℝ×ℝ)→ℂ) (ab : ℝ×ℝ) : ℝ :=
  (frequencyWeight ab)^(2*s)*‖F ab‖^2
private theorem weighted_energy_nonneg (s : ℝ) (F : (ℝ×ℝ)→ℂ) (ab : ℝ×ℝ) :
    0 ≤ weightedEnergy s F ab :=
  mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (frequency_weight_one_le ab)) _) (sq_nonneg _)
private theorem weighted_energy_measurable (s : ℝ) {F : (ℝ×ℝ)→ℂ} (hF : Measurable F) :
    Measurable (weightedEnergy s F) :=
  (frequency_weight_measurable.pow_const _).mul (hF.norm.pow_const 2)
private theorem weighted_energy_mono {s t : ℝ} (hst : s ≤ t) (F : (ℝ×ℝ)→ℂ) (ab : ℝ×ℝ) :
    weightedEnergy s F ab ≤ weightedEnergy t F ab :=
  mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (frequency_weight_one_le ab)
    (by linarith)) (sq_nonneg _)

private theorem difference_energy_bound (s : ℝ) (F G : (ℝ×ℝ)→ℂ) (ab : ℝ×ℝ) :
    weightedEnergy s (fun z => F z-G z) ab ≤ 2*(weightedEnergy s F ab+weightedEnergy s G ab) := by
  have hn : ‖F ab-G ab‖^2 ≤ 2*(‖F ab‖^2+‖G ab‖^2) := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F ab) (G ab)) 2
    nlinarith only [hp,sq_nonneg (‖F ab‖-‖G ab‖)]
  have hh := mul_le_mul_of_nonneg_left hn
    (Real.rpow_nonneg (zero_le_one.trans (frequency_weight_one_le ab)) (2*s))
  dsimp only [weightedEnergy]
  nlinarith only [hh]

private theorem frequency_tail_comparison {s t R : ℝ} (hst : s ≤ t) (hR : 1 ≤ R)
    (F : (ℝ×ℝ)→ℂ) (ab : ℝ×ℝ) (hab : ab∉Icc (-R) R ×ˢ Icc (-R) R) :
    weightedEnergy s F ab ≤ R^(2*s-2*t)*weightedEnergy t F ab := by
  have hw : 0<frequencyWeight ab := zero_lt_one.trans_le (frequency_weight_one_le ab)
  have hRw : R ≤ frequencyWeight ab := by
    by_contra! hh
    have ha : |ab.1| ≤ R := by dsimp only [frequencyWeight] at hh; linarith [abs_nonneg ab.2]
    have hb : |ab.2| ≤ R := by dsimp only [frequencyWeight] at hh; linarith [abs_nonneg ab.1]
    exact hab ⟨abs_le.mp ha,abs_le.mp hb⟩
  have hp := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hR) hRw (by linarith : 2*s-2*t ≤ 0)
  have he : (frequencyWeight ab)^(2*s)=(frequencyWeight ab)^(2*s-2*t)*(frequencyWeight ab)^(2*t) := by
    rw [←Real.rpow_add hw]
    congr 1
    ring
  unfold weightedEnergy
  rw [he,mul_assoc]
  exact mul_le_mul_of_nonneg_right hp (by positivity)

/-- Strong weighted L2 convergence of the full actual selected reciprocal kernel.
The limiting kernel is admitted at the same order, with no regularity premise. -/
theorem bagCubicReciprocalKernel_selected_energy_tendsto
    (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) (tau : {r : ℝ // 0<r}) :
    Integrable (fun ab : ℝ×ℝ => (1+|ab.1|+|ab.2|)^(2*s.1)*
      ‖bagCubicSharpReciprocalKernel ab.1 ab.2‖^2) ∧
    (∀ᶠ N : ℝ in atTop, Integrable (fun ab : ℝ×ℝ => (1+|ab.1|+|ab.2|)^(2*s.1)*
      ‖bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) ab.1 ab.2
        ((tau.1/N)*ab.1*ab.2)-bagCubicSharpReciprocalKernel ab.1 ab.2‖^2)) ∧
    Tendsto (fun N : ℝ => ∫ab : ℝ×ℝ, (1+|ab.1|+|ab.2|)^(2*s.1)*
      ‖bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N) ab.1 ab.2
        ((tau.1/N)*ab.1*ab.2)-bagCubicSharpReciprocalKernel ab.1 ab.2‖^2)
      atTop (𝓝 0) := by
  let t : {r : ℝ // r∈Ico (0 : ℝ) (3/2)} :=
    ⟨(s.1+3/2)/2,by constructor <;> linarith [s.2.1,s.2.2]⟩
  have hst : s.1<t.1 := by dsimp only [t]; linarith [s.2.2]
  let F := selectedKernel tau.1
  let G := sharpKernel
  let J := fun N => weightedEnergy s.1 (fun ab => F N ab-G ab)
  let JT := fun N => weightedEnergy t.1 (fun ab => F N ab-G ab)
  obtain ⟨C,hC,hCb⟩ := bagCubicReciprocalKernel_selected_uniform_energy t tau
  obtain ⟨B,hB,hGm,hGb,hFm⟩ := selected_kernel_measurable_bounded tau.1
  have hGN : Measurable (weightedEnergy t.1 G) := weighted_energy_measurable _ hGm
  have hGt : Integrable (weightedEnergy t.1 G) ∧ (∫ab, weightedEnergy t.1 G ab) ≤ C := by
    apply integral_limit_bound hC.le hGN (weighted_energy_nonneg _ _)
      (fun N => weighted_energy_nonneg t.1 (F N)) (fun ab => ?_) hCb
    simpa only [weightedEnergy,F,G,selectedKernel,sharpKernel] using (tendsto_const_nhds (x := (frequencyWeight ab)^(2*t.1))).mul
      ((bagCubicReciprocalKernel_selected_tendsto tau.1 ab.1 ab.2).norm.pow 2)
  have hGs : Integrable (weightedEnergy s.1 G) :=
    hGt.1.mono' (weighted_energy_measurable _ hGm).aestronglyMeasurable
      (Eventually.of_forall (fun ab => by
        rw [Real.norm_eq_abs,abs_of_nonneg (weighted_energy_nonneg _ _ _)]
        exact weighted_energy_mono hst.le G ab))
  have hJ : ∀ᶠ N : ℝ in atTop, Integrable (J N) ∧ Integrable (JT N) ∧ (∫ab, JT N ab) ≤ 4*C := by
    filter_upwards [hCb,hFm] with N hFN hmN
    change Integrable (weightedEnergy t.1 (F N)) ∧ (∫ab, weightedEnergy t.1 (F N) ab) ≤ C at hFN
    have hJT : Integrable (JT N) := ((hFN.1.add hGt.1).const_mul 2).mono'
      (weighted_energy_measurable _ (hmN.1.sub hGm)).aestronglyMeasurable
      (Eventually.of_forall (fun ab => by
        rw [Real.norm_eq_abs,abs_of_nonneg (weighted_energy_nonneg _ _ _)]
        exact difference_energy_bound t.1 (F N) G ab))
    have hJs : Integrable (J N) := hJT.mono'
      (weighted_energy_measurable _ (hmN.1.sub hGm)).aestronglyMeasurable
      (Eventually.of_forall (fun ab => by
        rw [Real.norm_eq_abs,abs_of_nonneg (weighted_energy_nonneg _ _ _)]
        exact weighted_energy_mono hst.le _ ab))
    refine ⟨hJs,hJT,?_⟩
    calc (∫ab, JT N ab) ≤ ∫ab, 2*(weightedEnergy t.1 (F N) ab+weightedEnergy t.1 G ab) :=
        integral_mono hJT ((hFN.1.add hGt.1).const_mul 2) (difference_energy_bound t.1 (F N) G)
      _ = 2*((∫ab, weightedEnergy t.1 (F N) ab)+(∫ab, weightedEnergy t.1 G ab)) := by
        rw [integral_const_mul,integral_add hFN.1 hGt.1]
      _  ≤  4*C := by linarith [hFN.2,hGt.2]
  refine ⟨hGs,hJ.mono (fun _ h => h.1),?_⟩
  change Tendsto (fun N : ℝ => ∫ab, J N ab) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp : Tendsto (fun R : ℝ => R^(2*s.1-2*t.1)*(4*C)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ)<2*t.1-2*s.1)).mul_const (4*C)
    simpa only [neg_sub,zero_mul] using hh
  obtain ⟨R,hR,hsmall⟩ : ∃R : ℝ, 1 ≤ R ∧ R^(2*s.1-2*t.1)*(4*C)<ε/2 :=
    ((eventually_ge_atTop (1 : ℝ)).and (hp.eventually (Iio_mem_nhds (by linarith : (0 : ℝ)<ε/2)))).exists
  let S : Set (ℝ×ℝ) := Icc (-R) R ×ˢ Icc (-R) R
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hloc := selected_local_energy_tendsto tau.1 s.1 R s.2.1 (zero_le_one.trans hR)
  filter_upwards [hJ,hloc.eventually (Iio_mem_nhds (by linarith : (0 : ℝ)<ε/2))] with N hJN hlocal
  have htail : (∫ab : ℝ×ℝ in Sᶜ, J N ab) ≤ R^(2*s.1-2*t.1)*(4*C) := by
    calc (∫ab : ℝ×ℝ in Sᶜ, J N ab) ≤ ∫ab : ℝ×ℝ in Sᶜ, R^(2*s.1-2*t.1)*JT N ab :=
        setIntegral_mono_on hJN.1.integrableOn (hJN.2.1.const_mul _).integrableOn hS.compl
          (fun ab hab => frequency_tail_comparison hst.le hR _ ab hab)
      _ = R^(2*s.1-2*t.1)*(∫ab : ℝ×ℝ in Sᶜ, JT N ab) := integral_const_mul _ _
      _  ≤  R^(2*s.1-2*t.1)*(∫ab : ℝ×ℝ, JT N ab) :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hJN.2.1
          (Eventually.of_forall (weighted_energy_nonneg _ _))) (by positivity)
      _  ≤  R^(2*s.1-2*t.1)*(4*C) := mul_le_mul_of_nonneg_left hJN.2.2 (by positivity)
  have hnon : 0 ≤ ∫ab, J N ab := integral_nonneg (weighted_energy_nonneg _ _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  rw [←integral_add_compl hS hJN.1]
  change (∫ab : ℝ×ℝ in S, J N ab)<ε/2 at hlocal
  linarith

end RHTower.BAGTrace
