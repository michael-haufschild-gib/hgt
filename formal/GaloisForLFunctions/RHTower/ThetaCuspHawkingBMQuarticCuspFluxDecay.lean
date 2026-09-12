import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseMellinTransport

/-!
# Rapid complete cusp tails and the retained physical endpoint flux

Every complex-height-weighted original indicial source tail has a proved
inverse-height bound. The actual physical full-response endpoint flux therefore
splits into its explicit particular response, its retained native homogeneous
coefficient and a remainder tending to zero. Both response branches, all three
original physical weights and the complete signed Fourier tails are included.

The native coefficient and particular endpoint flux are not assigned zero.
No complete-action identification, clock invariance, extinction or RH is assumed
or asserted. The common Hawking clock is unchanged.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMQuarticCuspFluxDecay
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse D4BMCuspResponse
open D4BMQuarticResponseMellinTransport
noncomputable section
set_option autoImplicit false

private theorem weighted_mean_tail_sq_bounded (u w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖(y:ℂ)^w*mean (fun x => tail u ![x,y] ^2)‖ ≤ C := by
  obtain ⟨A,hA,hAt⟩ := weighted_tail_bounded u w 1 (by norm_num)
  obtain ⟨B,hB,hBt⟩ := weighted_tail_bounded u 0 1 (by norm_num)
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro y hy
  have he : (y:ℂ)^w*mean (fun x => tail u ![x,y] ^2) =
      ∫ x in Ioc (-1/2:ℝ) (1/2), ((y:ℂ)^w*tail u ![x,y])*tail u ![x,y] := by
    rw [mean,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he]
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2))) (C := A*B)
    (f := fun x => ((y:ℂ)^w*tail u ![x,y])*tail u ![x,y]) (by
      filter_upwards with x
      rw [norm_mul]
      have h1 := hAt ![x,y] hy
      have h0 := hBt ![x,y] hy
      simp only [Matrix.cons_val_one,Complex.cpow_zero,one_mul] at h1 h0
      exact mul_le_mul h1 h0 (norm_nonneg _) hA)
  norm_num [Measure.real,Real.volume_Ioc] at h
  simpa only [neg_div] using h

private theorem weighted_fluxSource_tail (q : XiZeroCopy) (b a : Bool) (w : ℂ)
    {y : ℝ} (hy : 3 < y) :
    (y:ℂ)^w*fluxSource q b a y = (parameter q b/2)*
      ((y:ℂ)^(w+root q b a)*mean (fun x => tail (center q) ![x,y] ^2))/(y:ℂ)^2 := by
  have hp : 0 < y := by linarith
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [fluxSource,globalForcing_average q b (by linarith),mean_forcing_high q b hy,
    mean_tail_sq (center q) hp]
  have hw : (y:ℂ)^(w+root q b a) =
      (y:ℂ)^w*(y:ℂ)^(root q b a-2)*(y:ℂ)^2 := by
    have he : (y:ℂ)^(2:ℂ)=(y:ℂ)^2 := by norm_cast
    rw [← he,← Complex.cpow_add _ _ hn,← Complex.cpow_add _ _ hn]
    congr 1
    ring
  rw [hw]
  field_simp [hn]
  ring

/-- Every complex height weight of the complete original flux source has an inverse-square bound. -/
theorem weighted_fluxSource_norm_bound (q : XiZeroCopy) (b a : Bool) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 3 < y →
      ‖(y:ℂ)^w*fluxSource q b a y‖ ≤ C/y^2 := by
  obtain ⟨A,hA,hAt⟩ := weighted_mean_tail_sq_bounded (center q) (w+root q b a)
  refine ⟨‖parameter q b/2‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  intro y hy
  rw [weighted_fluxSource_tail q b a w hy,norm_div,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (by linarith : 0 < y)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hAt y (by linarith)) (norm_nonneg _)) (sq_nonneg y)

/-- Every weighted original source-tail integral decays; no native coefficient is discarded. -/
theorem weighted_source_tail_norm_bound (q : XiZeroCopy) (b a : Bool) (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 3 < y →
      ‖(y:ℂ)^w*∫ t in Ioi y, fluxSource q b a t‖ ≤ C/y := by
  let v : ℝ := max w.re 0
  obtain ⟨C,hC,hbound⟩ := weighted_fluxSource_norm_bound q b a (v:ℂ)
  refine ⟨C,hC,?_⟩
  intro y hy
  have hp : 0 < y := by linarith
  have hi : IntegrableOn (fun t : ℝ => t^(-2:ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_iff hp).mpr (by norm_num)
  have hf : IntegrableOn (fluxSource q b a) (Ioi y) :=
    (fluxSource_integrable q b a).mono_set (fun _ ht => hy.trans ht)
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ t in Ioi y, ‖(y:ℂ)^w*fluxSource q b a t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi y, C*t^(-2:ℝ) := by
      apply integral_mono_ae (hf.const_mul _).norm (hi.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht3 : 3 < t := hy.trans ht
      have htp : 0 < t := hp.trans ht
      have hpow : y^w.re ≤ t^v :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)).trans
          (Real.rpow_le_rpow hp.le ht.le (le_max_right _ _))
      calc
        ‖(y:ℂ)^w*fluxSource q b a t‖ ≤ ‖(t:ℂ)^(v:ℂ)*fluxSource q b a t‖ := by
          rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp,
            Complex.norm_cpow_eq_rpow_re_of_pos htp,Complex.ofReal_re]
          exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ ≤ C/t^2 := hbound t ht3
        _ = C*t^(-2:ℝ) := by rw [Real.rpow_neg (by positivity),Real.rpow_two,div_eq_mul_inv]
    _ = C/y := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hp]
      have hr : y^(-1:ℝ)=y⁻¹ := by rw [Real.rpow_neg hp.le,Real.rpow_one]
      norm_num [hr,div_eq_mul_inv]

/-- The entire forced cusp tail vanishes after multiplication by any fixed complex power. -/
theorem weighted_source_tail_tendsto_zero (q : XiZeroCopy) (b a : Bool) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*∫ t in Ioi y, fluxSource q b a t) atTop (𝓝 0) := by
  obtain ⟨C,_,hC⟩ := weighted_source_tail_norm_bound q b a w
  have ht : Tendsto (fun y : ℝ => C/y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  apply squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  exact hC y hy

/-- The difference from the actual limiting Wronskian has arbitrary power decay. -/
theorem weighted_responseFlux_remainder_tendsto_zero
    (q : XiZeroCopy) (b a : Bool) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*(responseFlux q b a y-limitingFlux q b a))
      atTop (𝓝 0) := by
  have ht := (weighted_source_tail_tendsto_zero q b a w).neg
  apply (show Tendsto (fun y : ℝ => -((y:ℂ)^w*∫ t in Ioi y, fluxSource q b a t))
    atTop (𝓝 0) by simpa only [neg_zero] using ht).congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  rw [responseFlux_eq_limit_sub_tail q b a hy]
  ring


private theorem weighted_native_flux (q : XiZeroCopy) (b a : Bool) (w : ℂ)
    {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(w-root q b a)*responseFlux q b a y =
      (y:ℂ)^w*deriv (responseMean q b) y-
        root q b a*(y:ℂ)^(w-1)*responseMean q b y := by
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h0 : (y:ℂ)^(w-root q b a)*(y:ℂ)^(root q b a)=(y:ℂ)^w := by
    rw [← Complex.cpow_add _ _ hn,sub_add_cancel]
  have h1 : (y:ℂ)^(w-root q b a)*(y:ℂ)^(root q b a-1)=(y:ℂ)^(w-1) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  dsimp only [responseFlux]
  linear_combination deriv (responseMean q b) y*h0-root q b a*responseMean q b y*h1

private theorem native_weight_flux_decomposition (q : XiZeroCopy) (b : Bool) (w : ℂ)
    {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^w*deriv (responseMean q b) y-w*(y:ℂ)^(w-1)*responseMean q b y =
      (w-root q b false)/rootGap q b*((y:ℂ)^(w-root q b true)*responseFlux q b true y)+
      (root q b true-w)/rootGap q b*((y:ℂ)^(w-root q b false)*responseFlux q b false y) := by
  rw [weighted_native_flux q b true w hy,weighted_native_flux q b false w hy]
  field_simp [rootGap_ne_zero q b]
  dsimp only [D4BMCuspResponse.rootGap]
  ring

private theorem fullMean_sub_native (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 3 < y) :
    fullMean q b y-responseMean q b y=cuspResponse q b ![0,y] := by
  rw [fullMean_eq_cusp_data q b ⟨y,hy⟩,responseMean_native_decomposition q b hy]
  dsimp only [D4BMQuarticResponseCuspPair.fullResponseCuspMean]
  ring

private theorem fullMean_deriv_sub_native (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 3 < y) :
    deriv (fullMean q b) y-deriv (responseMean q b) y=
      deriv (fun t : ℝ => cuspResponse q b ![0,t]) y := by
  have he : (fun t : ℝ => fullMean q b t-responseMean q b t) =ᶠ[𝓝 y]
      (fun t : ℝ => cuspResponse q b ![0,t]) := by
    filter_upwards [eventually_gt_nhds hy] with t ht
    exact fullMean_sub_native q b ht
  have hp : 0 < y := by linarith
  have hM : DifferentiableAt ℝ (fullMean q b) y :=
    (average_hasDerivAt (fullAngular q b ∘ ofComplex)
      (fullAngular_smooth q b).planar_contDiffOn hp).differentiableAt
  have hm : DifferentiableAt ℝ (responseMean q b) y :=
    (average_hasDerivAt (responsePlanar q b) (responsePlanar_smooth q b) hp).differentiableAt
  exact (deriv_sub hM hm).symm.trans he.deriv_eq

/-- Explicit particular-response contribution to the actual physical endpoint flux. -/
def particularPhysicalFlux (q : XiZeroCopy) (b : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  (y:ℂ)^(physicalWeight q i)*deriv (fun t : ℝ => cuspResponse q b ![0,t]) y-
    physicalWeight q i*(y:ℂ)^(physicalWeight q i-1)*cuspResponse q b ![0,y]

/-- Native coefficient contribution, retained at its original physical testing weight. -/
def nativePhysicalFlux (q : XiZeroCopy) (b : Bool) (i : Fin 3) (y : ℝ) : ℂ :=
  (root q b false-physicalWeight q i)*limitingCoefficient q b false*
    (y:ℂ)^(physicalWeight q i-root q b true)

/-- Exact full physical endpoint flux: particular and native terms plus both complete forced tails. -/
theorem physicalFlux_exact_tail_decomposition (q : XiZeroCopy) (b : Bool) (i : Fin 3)
    {y : ℝ} (hy : 3 < y) :
    physicalFlux q b i y-particularPhysicalFlux q b i y-nativePhysicalFlux q b i y =
      -(physicalWeight q i-root q b false)/rootGap q b*
        ((y:ℂ)^(physicalWeight q i-root q b true)*∫ t in Ioi y, fluxSource q b true t)-
      (root q b true-physicalWeight q i)/rootGap q b*
        ((y:ℂ)^(physicalWeight q i-root q b false)*∫ t in Ioi y, fluxSource q b false t) := by
  have hv := fullMean_sub_native q b hy
  have hd := fullMean_deriv_sub_native q b hy
  have hn := native_weight_flux_decomposition q b (physicalWeight q i) (by linarith : 0 < y)
  rw [responseFlux_eq_limit_sub_tail q b true hy,
    responseFlux_eq_limit_sub_tail q b false hy,limitingFlux_first_zero q b] at hn
  have hsplit : physicalFlux q b i y-particularPhysicalFlux q b i y =
      (y:ℂ)^(physicalWeight q i)*deriv (responseMean q b) y-
        physicalWeight q i*(y:ℂ)^(physicalWeight q i-1)*responseMean q b y := by
    dsimp only [physicalFlux,particularPhysicalFlux]
    linear_combination (y:ℂ)^(physicalWeight q i)*hd-
      physicalWeight q i*(y:ℂ)^(physicalWeight q i-1)*hv
  rw [hsplit,hn]
  simp only [nativePhysicalFlux,limitingCoefficient,Bool.false_eq_true,if_false]
  ring

/-- Every physical cusp endpoint remainder tends to zero after subtracting its actual
particular response and its native homogeneous coefficient; neither term is assumed zero. -/
theorem physicalFlux_remainder_tendsto_zero (q : XiZeroCopy) (b : Bool) (i : Fin 3) :
    Tendsto (fun y : ℝ => physicalFlux q b i y-particularPhysicalFlux q b i y-
      nativePhysicalFlux q b i y) atTop (𝓝 0) := by
  have h1 := (weighted_source_tail_tendsto_zero q b true
    (physicalWeight q i-root q b true)).const_mul
      (-(physicalWeight q i-root q b false)/rootGap q b)
  have h0 := (weighted_source_tail_tendsto_zero q b false
    (physicalWeight q i-root q b false)).const_mul
      ((root q b true-physicalWeight q i)/rootGap q b)
  have ht := h1.sub h0
  simp only [mul_zero,sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  exact (physicalFlux_exact_tail_decomposition q b i hy).symm

end
end RHTower.D4BMQuarticCuspFluxDecay
