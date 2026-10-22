import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalWeightedOrbit
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Original causal time transform with unbounded cusp weight

Spatial Fatou and temporal Fatou admit the actual weighted causal orbit.
Ratios of the bounded cusp profiles to their limiting weight recover strong
spatial convergence, hence Bochner measurability of the limiting time field.
The original uniform Plancherel estimate fixes its time-energy bound.

Bounded inverse-weight multiplication identifies its Laplace integral with
the weighted original frequency response. The full physical angular reader
therefore commutes with causal time integration on the native Green band.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace RHTower.D4BMOriginalCuspTime
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMJointWave D4BMModularCore
open D4BMNativeLaplace D4BMNativeCircle D4BMOriginalWeightedOrbit
noncomputable section
set_option autoImplicit false

private abbrev spatialMeasure := radialMeasure.prod D4BMModularCore.measure
private abbrev timeMeasure := volume.restrict (Ioi (0:ℝ))
private abbrev cutoff (n : ℕ) := cuspSpatialMultiply (n+1) (by positivity)
private def weighted (u : SpatialSpace) (p : ℝ×UpperHalfPlane) : ℂ :=
  (cuspWeightLimit p.2.im:ℂ)*u p

private theorem weight_positive (y : ℝ) (hy : 0<y) : 0<cuspWeightLimit y := by
  have h := (cuspWeightProfile_bounds 1 y (by norm_num) hy).1.trans
    (cuspWeightProfile_le_limit 1 y (by norm_num) hy)
  linarith [cuspWeightBase_one_le]

private theorem weighted_measurable (u : SpatialSpace) :
    AEStronglyMeasurable (weighted u) spatialMeasure := by
  have hw : Continuous (fun p : ℝ×UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)) := by
    unfold cuspWeightLimit cuspWeightCutoff
    fun_prop
  exact hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)

private theorem cutoff_coe (n : ℕ) (u : SpatialSpace) :
    cutoff n u =ᵐ[spatialMeasure]
      fun p => (cuspWeightProfile (n+1) p.2.im:ℂ)*u p := by
  have hc : ∀ᵐ p : ℝ×UpperHalfPlane ∂spatialMeasure, p.2∈ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [cuspSpatialMultiply_coe (n+1) (by positivity) u,hc] with p hp hf
  rw [hp]
  dsimp only [cuspWeightSymbol]
  rw [(modularCuspWeight_germ (n+1) p.2 hf).eq_of_nhds]

private theorem cutoff_pointwise (u : SpatialSpace) :
    ∀ᵐ p ∂spatialMeasure, Tendsto (fun n => cutoff n u p) atTop (𝓝 (weighted u p)) := by
  filter_upwards [ae_all_iff.mpr (fun n => cutoff_coe n u)] with p hp
  simp_rw [hp]
  exact ((Complex.continuous_ofReal.tendsto _).comp (cuspWeightProfile_tendsto p.2.im)).mul_const _

private theorem weighted_fatou (u : SpatialSpace) :
    eLpNorm (weighted u) 2 spatialMeasure ≤ atTop.liminf (fun n => ‖cutoff n u‖ₑ) := by
  have h := Lp.eLpNorm_lim_le_liminf_eLpNorm (p:=2)
    (fun n => Lp.aestronglyMeasurable (cutoff n u)) (weighted u) (cutoff_pointwise u)
  simpa only [← Lp.enorm_def] using h

private def ratio (n : ℕ) (p : ℝ×UpperHalfPlane) : ℂ :=
  (cuspWeightProfile (n+1) p.2.im/cuspWeightLimit p.2.im:ℝ)

private theorem ratio_measurable (n : ℕ) : Measurable (ratio n) := by
  have h0 : Continuous (fun p : ℝ×UpperHalfPlane => cuspWeightLimit p.2.im) := by
    unfold cuspWeightLimit cuspWeightCutoff
    fun_prop
  have h1 : Continuous (fun p : ℝ×UpperHalfPlane => cuspWeightProfile (n+1) p.2.im) := by
    unfold cuspWeightProfile cuspWeightCutoff
    apply Continuous.add continuous_const
    apply Continuous.mul
    · fun_prop
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        have := p.2.im_pos
        positivity
  exact (Complex.continuous_ofReal.comp (h1.div h0 (fun p => (weight_positive _ p.2.im_pos).ne'))).measurable

private theorem ratio_bound (n : ℕ) (p : ℝ×UpperHalfPlane) : ‖ratio n p‖≤1 := by
  have hw := weight_positive _ p.2.im_pos
  have h0 := (cuspWeightProfile_bounds (n+1) p.2.im (by positivity) p.2.im_pos).1
  have h1 := cuspWeightProfile_le_limit (n+1) p.2.im (by positivity) p.2.im_pos
  have hp : 0≤cuspWeightProfile (n+1) p.2.im := by linarith [cuspWeightBase_one_le]
  simp only [ratio,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hp hw.le)]
  exact (div_le_one hw).mpr h1

private theorem ratio_tendsto (p : ℝ×UpperHalfPlane) :
    Tendsto (fun n => ratio n p) atTop (𝓝 1) := by
  have h := (cuspWeightProfile_tendsto p.2.im).div_const (cuspWeightLimit p.2.im)
  rw [div_self (weight_positive _ p.2.im_pos).ne'] at h
  simpa only [ratio,Complex.ofReal_one,Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp h

/-- The bounded cusp profiles converge strongly on the domain of the literal unbounded weight. -/
private theorem cutoff_tendsto (u : SpatialSpace) (hu : MemLp (weighted u) 2 spatialMeasure) :
    Tendsto (fun n => cutoff n u) atTop (𝓝 (hu.toLp _)) := by
  let R (n : ℕ) : SpatialSpace →L[ℂ] SpatialSpace :=
    lpBoundedMulCLM (ratio_measurable n) (by norm_num : (0:ℝ)≤1) (ratio_bound n)
  let I : SpatialSpace →L[ℂ] SpatialSpace :=
    lpBoundedMulCLM (measurable_const (a:=(1:ℂ))) (by norm_num : (0:ℝ)≤1) (fun _ => by simp)
  have hi : I (hu.toLp _) = hu.toLp _ := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (measurable_const (a:=(1:ℂ)))
      (by norm_num : (0:ℝ)≤1) (fun _ => by simp) (hu.toLp _)] with p hp
    simpa only [one_mul] using hp
  have hr (n : ℕ) : R n (hu.toLp _) = cutoff n u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (ratio_measurable n)
      (by norm_num : (0:ℝ)≤1) (ratio_bound n) (hu.toLp _),hu.coeFn_toLp,cutoff_coe n u] with p h1 h2 h3
    rw [h1,h2,h3]
    dsimp only [ratio,weighted]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (weight_positive _ p.2.im_pos).ne']
  have ht := tendsto_lpBoundedMulCLM_apply (ratio_measurable) (measurable_const (a:=(1:ℂ)))
    (by norm_num : (0:ℝ)≤1) ratio_bound (fun _ => by simp) ratio_tendsto (hu.toLp _)
  change Tendsto (fun n => R n (hu.toLp _)) atTop (𝓝 (I (hu.toLp _))) at ht
  simpa only [hr,hi] using ht

private theorem rpow_liminf (f : ℕ→ℝ≥0∞) :
    (atTop.liminf f)^(2:ℝ) = atTop.liminf (fun n => (f n)^(2:ℝ)) := by
  have hm := ENNReal.strictMono_rpow_of_pos (by norm_num : (0:ℝ)<2)
  have hs := (ENNReal.rpow_left_bijective (by norm_num : (2:ℝ)≠0)).2
  apply (hm.orderIsoOfSurjective _ hs).liminf_apply

private theorem aemeasurable_liminf {f : ℕ→ℝ→ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) timeMeasure) :
    AEMeasurable (fun t => atTop.liminf (fun n => f n t)) timeMeasure := by
  apply (Measurable.liminf (fun n => (hf n).measurable_mk)).aemeasurable.congr
  filter_upwards [ae_all_iff.mpr (fun n => (hf n).ae_eq_mk)] with t ht
  simp_rw [ht]

private theorem weighted_time (U : ℝ→SpatialSpace)
    (hU : ∀ n, MemLp (fun t => cutoff n (U t)) 2 timeMeasure)
    (C : ℝ≥0∞) (hC : C<∞)
    (hbound : ∀ n, (∫⁻ t,‖cutoff n (U t)‖ₑ^(2:ℝ) ∂timeMeasure)≤C) :
    ∃ V : ℝ→SpatialSpace, MemLp V 2 timeMeasure ∧
      (∀ᵐ t ∂timeMeasure, V t =ᵐ[spatialMeasure] weighted (U t)) ∧
      (∀ᵐ t ∂timeMeasure, Tendsto (fun n => cutoff n (U t)) atTop (𝓝 (V t))) ∧
      (∫⁻ t,‖V t‖ₑ^(2:ℝ) ∂timeMeasure)≤C := by
  classical
  let f (n : ℕ) (t : ℝ) := ‖cutoff n (U t)‖ₑ^(2:ℝ)
  have hf (n : ℕ) : AEMeasurable (f n) timeMeasure :=
    (hU n).aestronglyMeasurable.enorm.pow_const _
  have hF : (∫⁻ t,atTop.liminf (fun n => f n t) ∂timeMeasure)≤C :=
    (lintegral_liminf_le' hf).trans (liminf_le_of_frequently_le' (.of_forall hbound))
  have hfinite := ae_lt_top' (aemeasurable_liminf hf) (hF.trans_lt hC).ne
  have hadmit : ∀ᵐ t ∂timeMeasure, MemLp (weighted (U t)) 2 spatialMeasure := by
    filter_upwards [hfinite] with t ht
    refine ⟨weighted_measurable _,(weighted_fatou _).trans_lt ?_⟩
    apply lt_top_iff_ne_top.mpr
    intro he
    have hs := rpow_liminf (fun n => ‖cutoff n (U t)‖ₑ)
    rw [he,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ)<2)] at hs
    change atTop.liminf (fun n => ‖cutoff n (U t)‖ₑ^(2:ℝ))<∞ at ht
    exact (not_lt_of_ge hs.le) ht
  let V (t : ℝ) : SpatialSpace :=
    if h : MemLp (weighted (U t)) 2 spatialMeasure then h.toLp _ else 0
  have hrep : ∀ᵐ t ∂timeMeasure, V t =ᵐ[spatialMeasure] weighted (U t) := by
    filter_upwards [hadmit] with t ht
    dsimp only [V]
    rw [dif_pos ht]
    exact ht.coeFn_toLp
  have ht : ∀ᵐ t ∂timeMeasure, Tendsto (fun n => cutoff n (U t)) atTop (𝓝 (V t)) := by
    filter_upwards [hadmit] with t ht
    dsimp only [V]
    rw [dif_pos ht]
    exact cutoff_tendsto _ ht
  have hm : AEStronglyMeasurable V timeMeasure :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hU n).aestronglyMeasurable) ht
  have henergy : (∫⁻ t,‖V t‖ₑ^(2:ℝ) ∂timeMeasure)≤C := by
    apply (le_of_eq (lintegral_congr_ae ?_)).trans hF
    filter_upwards [ht] with t ht
    exact ((ENNReal.continuous_rpow_const.tendsto _).comp
      (continuous_enorm.tendsto _ |>.comp ht)).liminf_eq.symm
  refine ⟨V,⟨hm,?_⟩,hrep,ht,henergy⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (henergy.trans_lt hC).ne

private theorem integral_enorm_sq {U : ℝ→SpatialSpace} (hU : MemLp U 2 timeMeasure) :
    (∫⁻ t,‖U t‖ₑ^(2:ℝ) ∂timeMeasure)=ENNReal.ofReal (∫ t,‖U t‖^2 ∂timeMeasure) := by
  have hi := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have h := ofReal_integral_eq_lintegral_ofReal hi (.of_forall (fun t => sq_nonneg ‖U t‖))
  simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2,ofReal_norm,ENNReal.rpow_two] using h.symm

/-- The original causal orbit has a genuine cusp-weighted time-L2 limit with its fixed energy
normalization. Both the field representative and the strong cutoff limit are retained. -/
theorem original_cusp_time_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (hca : 3/2<c) :
    ∃ V : ℝ→SpatialSpace,
      MemLp V 2 (volume.restrict (Ioi (0:ℝ))) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), V t =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => (cuspWeightLimit p.2.im:ℂ)*expRay (c:ℂ) t*causalJointForcedResponse q br amp t p) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
        Tendsto (fun n : ℕ => expRay (c:ℂ) t • cuspSpatialMultiply (n+1) (by positivity)
          (causalJointForcedResponse q br amp t)) atTop (𝓝 (V t))) ∧
      (∫ t in Ioi (0:ℝ),‖V t‖^2)≤(c*sourceBound q br amp c/(c^2-9/4))^2/(2*c) := by
  let U (t : ℝ) := expRay (c:ℂ) t • causalJointForcedResponse q br amp t
  let B := (c*sourceBound q br amp c/(c^2-9/4))^2/(2*c)
  have hc0 : 0<c := by linarith
  have hB : 0≤B := by dsimp only [B]; positivity
  have hU := causalJointForcedResponse_memLp_of_native q br amp c hc
  have hf (n : ℕ) : MemLp (fun t => cutoff n (U t)) 2 timeMeasure :=
    (cutoff n).comp_memLp' hU
  have hb (n : ℕ) : (∫⁻ t,‖cutoff n (U t)‖ₑ^(2:ℝ) ∂timeMeasure)≤ENNReal.ofReal B := by
    rw [integral_enorm_sq (hf n)]
    apply ENNReal.ofReal_le_ofReal
    have h := original_cusp_time_energy_uniform q br amp c hc hca (n+1) (by positivity)
    simpa only [U,cutoff,map_smul,norm_smul,mul_pow,norm_sq_expRay,Complex.ofReal_re] using h
  obtain ⟨V,hV,hrep,ht,he⟩ := weighted_time U hf (ENNReal.ofReal B) ENNReal.ofReal_lt_top hb
  refine ⟨V,hV,?_,?_,?_⟩
  · filter_upwards [hrep] with t ht
    filter_upwards [ht,Lp.coeFn_smul (expRay (c:ℂ) t) (causalJointForcedResponse q br amp t)] with p h1 h2
    rw [h1]
    dsimp only [weighted,U]
    rw [h2]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · simpa only [U,cutoff,map_smul] using ht
  · rw [integral_enorm_sq hV] at he
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

private def heightRatio (p : ℝ×UpperHalfPlane) : ℂ := (p.2.im/cuspWeightLimit p.2.im:ℝ)

private theorem heightRatio_measurable : Measurable heightRatio := by
  have hw : Continuous (fun p : ℝ×UpperHalfPlane => cuspWeightLimit p.2.im) := by
    unfold cuspWeightLimit cuspWeightCutoff
    fun_prop
  exact (Complex.continuous_ofReal.comp
    (UpperHalfPlane.continuous_im.comp continuous_snd |>.div hw
      (fun p => (weight_positive _ p.2.im_pos).ne'))).measurable

private theorem heightRatio_bound (p : ℝ×UpperHalfPlane) : ‖heightRatio p‖≤3 := by
  have hw := weight_positive _ p.2.im_pos
  simp only [heightRatio,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg p.2.im_pos.le hw.le)]
  exact (div_le_iff₀ hw).mpr (cuspWeightLimit_height_le _ p.2.im_pos)

private def weightInverse (p : ℝ×UpperHalfPlane) : ℂ := (cuspWeightLimit p.2.im:ℂ)⁻¹

private theorem weightInverse_measurable : Measurable weightInverse := by
  have hw : Continuous (fun p : ℝ×UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)) := by
    unfold cuspWeightLimit cuspWeightCutoff
    fun_prop
  exact hw.measurable.inv

private theorem weightInverse_bound (p : ℝ×UpperHalfPlane) : ‖weightInverse p‖≤1 := by
  have hw := weight_positive _ p.2.im_pos
  have h1 : 1≤cuspWeightLimit p.2.im :=
    cuspWeightBase_one_le.trans ((cuspWeightProfile_bounds 1 _ (by norm_num) p.2.im_pos).1.trans
      (cuspWeightProfile_le_limit 1 _ (by norm_num) p.2.im_pos))
  simp only [weightInverse,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
  exact inv_le_one_of_one_le₀ h1

private theorem expRay_join (w : ℂ) (c t : ℝ) :
    expRay (w-c) t*expRay (c:ℂ) t=expRay w t := by
  simp only [expRay,← Complex.exp_add]
  congr 1
  ring

/-- Unbounded cusp multiplication commutes with the original time transform after the actual
weighted time admission is derived. No change of the causal orbit is made. -/
theorem original_cusp_time_laplace (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : principalKernelGrowth q<w.re) :
    ∃ K : ℝ→SpatialSpace, IntegrableOn K (Ioi (0:ℝ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), K t =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => (cuspWeightLimit p.2.im:ℂ)*expRay w t*causalJointForcedResponse q br amp t p) ∧
      ((∫ t in Ioi (0:ℝ),K t : SpatialSpace) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => (cuspWeightLimit p.2.im:ℂ)*causalJointFrequencyResponse q br amp w p) := by
  obtain ⟨c,hc,hcw⟩ := exists_between hw
  have hca : 3/2<c := (actualPrincipalKernel_common_growth q).1.trans_lt hc
  obtain ⟨V,hV,hrep,-,-⟩ := original_cusp_time_limit q br amp c hc hca
  let K (t : ℝ) := expRay (w-c) t • V t
  have hE := memLp_two_expRay_restrict (show 0<(w-c).re by simpa using sub_pos.mpr hcw) 0
  have hK : IntegrableOn K (Ioi (0:ℝ)) := memLp_one_iff_integrable.mp (hV.smul hE)
  have hkrep : ∀ᵐ t ∂timeMeasure, K t =ᵐ[spatialMeasure]
      fun p => (cuspWeightLimit p.2.im:ℂ)*expRay w t*causalJointForcedResponse q br amp t p := by
    filter_upwards [hrep] with t ht
    filter_upwards [ht,Lp.coeFn_smul (expRay (w-c) t) (V t)] with p hp hs
    dsimp only [K]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hp]
    calc
      _ = (cuspWeightLimit p.2.im:ℂ)*(expRay (w-c) t*expRay (c:ℂ) t)*causalJointForcedResponse q br amp t p := by ring
      _ = _ := by rw [expRay_join]
  let I : SpatialSpace →L[ℂ] SpatialSpace :=
    lpBoundedMulCLM weightInverse_measurable (by norm_num : (0:ℝ)≤1) weightInverse_bound
  have hit : (fun t => I (K t)) =ᵐ[timeMeasure]
      fun t => expRay w t • causalJointForcedResponse q br amp t := by
    filter_upwards [hkrep] with t ht
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn weightInverse_measurable
      (by norm_num : (0:ℝ)≤1) weightInverse_bound (K t),ht,
      Lp.coeFn_smul (expRay w t) (causalJointForcedResponse q br amp t)] with p hi hk hs
    rw [hi,hk,hs]
    simp only [Pi.smul_apply,smul_eq_mul,weightInverse]
    field_simp [Complex.ofReal_ne_zero.mpr (weight_positive _ p.2.im_pos).ne']
  have hI : I (∫ t in Ioi (0:ℝ),K t)=causalJointFrequencyResponse q br amp w := by
    calc
      _ = ∫ t in Ioi (0:ℝ),I (K t) := (I.integral_comp_comm hK).symm
      _ = ∫ t in Ioi (0:ℝ),expRay w t • causalJointForcedResponse q br amp t := integral_congr_ae hit
      _ = _ := causalJointForcedResponse_laplace_of_native q br amp w hw
  refine ⟨K,hK,hkrep,?_⟩
  filter_upwards [lpBoundedMulCLM_coeFn weightInverse_measurable
    (by norm_num : (0:ℝ)≤1) weightInverse_bound (∫ t in Ioi (0:ℝ),K t)] with p hp
  change (I (∫ t in Ioi (0:ℝ),K t)) p = _ at hp
  rw [hI] at hp
  dsimp only [weightInverse] at hp
  rw [hp]
  field_simp [Complex.ofReal_ne_zero.mpr (weight_positive _ p.2.im_pos).ne']

/-- The actual height-weighted original time field is integrable on the entire native Laplace
half-plane, and its integral is the height-weighted original frequency response. -/
theorem original_height_time_laplace (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : principalKernelGrowth q<w.re) :
    ∃ H : ℝ→SpatialSpace, IntegrableOn H (Ioi (0:ℝ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), H t =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => expRay w t*(p.2.im:ℂ)*causalJointForcedResponse q br amp t p) ∧
      ((∫ t in Ioi (0:ℝ),H t : SpatialSpace) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => (p.2.im:ℂ)*causalJointFrequencyResponse q br amp w p) := by
  obtain ⟨K,hK,hrep,hint⟩ := original_cusp_time_laplace q br amp w hw
  let M : SpatialSpace →L[ℂ] SpatialSpace :=
    lpBoundedMulCLM heightRatio_measurable (by norm_num : (0:ℝ)≤3) heightRatio_bound
  refine ⟨fun t => M (K t),M.integrable_comp hK,?_,?_⟩
  · filter_upwards [hrep] with t ht
    filter_upwards [lpBoundedMulCLM_coeFn heightRatio_measurable
      (by norm_num : (0:ℝ)≤3) heightRatio_bound (K t),ht] with p hm hk
    rw [hm,hk]
    dsimp only [heightRatio]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (weight_positive _ p.2.im_pos).ne']
  · rw [M.integral_comp_comm hK]
    filter_upwards [lpBoundedMulCLM_coeFn heightRatio_measurable
      (by norm_num : (0:ℝ)≤3) heightRatio_bound (∫ t in Ioi (0:ℝ),K t),hint] with p hm hk
    rw [hm,hk]
    dsimp only [heightRatio]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (weight_positive _ p.2.im_pos).ne']

/-- The physical angular reader can be applied before the original causal time integration.
Its resulting radial function is exactly the previously identified physical Green response. -/
theorem original_physical_time_projection (q r : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : principalKernelGrowth q<w.re) (hwi : w.im≠0) (hwr : |w.re|<2) :
    ∃ H : ℝ→SpatialSpace, IntegrableOn H (Ioi (0:ℝ)) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), H t =ᵐ[radialMeasure.prod D4BMModularCore.measure]
        fun p => expRay w t*(p.2.im:ℂ)*causalJointForcedResponse q br amp t p) ∧
      IntegrableOn (fun t => physicalJointProjection r (H t)) (Ioi (0:ℝ)) ∧
      (∫ t in Ioi (0:ℝ),physicalJointProjection r (H t))=causalPhysicalProjection q r br amp w hw hwi hwr := by
  obtain ⟨H,hH,hrep,hint⟩ := original_height_time_laplace q br amp w hw
  refine ⟨H,hH,hrep,(physicalJointProjection r).integrable_comp hH,?_⟩
  rw [(physicalJointProjection r).integral_comp_comm hH]
  unfold causalPhysicalProjection
  congr 1
  apply Lp.ext
  filter_upwards [hint,(causalJointLaplace_height_memLp q br amp w hw hwi hwr).coeFn_toLp] with p hh hp
  rw [hh,hp,causalJointForcedResponse_laplace_of_native q br amp w hw]

end
end RHTower.D4BMOriginalCuspTime
