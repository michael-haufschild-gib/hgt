import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanMellinTransport
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwiningLine
import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorVector
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.FiniteEulerCalkinIndependence

/-!
# Exact Connes--Consani Fourier--Mellin scattering identity

This module proves the archimedean identity denoted `F_eR^w = I ∘ u_infinity^g` in
Connes--Consani's local trace-formula analysis. The proof establishes all critical-line
integrability and normalization on a dense even-Schwartz core, invokes the already formalized
archimedean Mellin functional equation there, and extends the operator equality to the full even
`L²` carrier by continuity. The endpoint theorem has no analytic, density, regularity, or
transform-intertwining hypothesis.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

theorem ccmArchimedeanMellinUnitary_eq_logFourier (f : evenSubspace) :
    archimedeanMellinUnitary f =
      dilationUnitary MellinL2.spectralNormalization
        MellinL2.spectralNormalization_pos
        (fourierUnitary (logEvenUnitary f)) := by
  change MellinL2.mellinUnitary
      (MellinL2.expPullbackUnitary.symm (logEvenUnitary f)) = _
  change dilationUnitary MellinL2.spectralNormalization
      MellinL2.spectralNormalization_pos
      (fourierUnitary
        (MellinL2.expPullbackUnitary
          (MellinL2.expPullbackUnitary.symm (logEvenUnitary f)))) = _
  rw [MellinL2.expPullbackUnitary.apply_symm_apply]

def ccmEvenSchwartzSource (g : 𝓢(ℝ, ℂ)) : evenSubspace :=
  ⟨(schwartzEvenPart g).toLp 2 volume,
    memLp_toLp_mem_evenSubspace ((schwartzEvenPart g).memLp 2 volume)
      (schwartzEvenPart_even g)⟩

theorem ccmEvenSchwartzSource_coeFn (g : 𝓢(ℝ, ℂ)) :
    (((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      schwartzEvenPart g :=
  (schwartzEvenPart g).coeFn_toLp 2 volume

theorem ccmEvenSchwartzSource_soninMellinEvaluation (g : 𝓢(ℝ, ℂ)) (w : ℂ) :
    soninMellinEvaluation w
        ((((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) : ℝ → ℂ)) =
      soninMellinEvaluation w (schwartzEvenPart g) := by
  unfold soninMellinEvaluation
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ccmEvenSchwartzSource_coeFn g)] with x hx
  rw [hx]

theorem ccmEvenProjectionToEven_surjective :
    Function.Surjective evenProjectionToEven := by
  intro f
  refine ⟨(f : SoninL2), ?_⟩
  apply Subtype.ext
  change evenProjection (f : SoninL2) = (f : SoninL2)
  rw [evenProjection_apply, (mem_evenSubspace_iff _).mp f.property]
  module

def ccmEvenSchwartzSourceCLM : 𝓢(ℝ, ℂ) →L[ℂ] evenSubspace :=
  evenProjectionToEven.comp (SchwartzMap.toLpCLM ℂ ℂ 2 volume)

theorem ccmEvenProjection_toLp (g : 𝓢(ℝ, ℂ)) :
    evenProjectionToEven (g.toLp 2 volume) = ccmEvenSchwartzSource g := by
  apply Subtype.ext
  change evenProjection (g.toLp 2 volume) =
    (schwartzEvenPart g).toLp 2 volume
  rw [evenProjection_apply]
  apply Lp.ext
  filter_upwards [g.coeFn_toLp 2 volume,
    l2Reflection_ae (g.toLp 2 volume),
    g.coeFn_toLp 2 volume |>.comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae,
    (schwartzEvenPart g).coeFn_toLp 2 volume,
    Lp.coeFn_add (g.toLp 2 volume) (l2Reflection (g.toLp 2 volume)),
    Lp.coeFn_smul (2 : ℂ)⁻¹
      (g.toLp 2 volume + l2Reflection (g.toLp 2 volume))]
      with x hg hrefl hgnegeven heven hadd hsmul
  have hneg : ((g.toLp 2 volume : SoninL2) : ℝ → ℂ) (-x) = g (-x) := by
    simpa only [Function.comp_apply] using hgnegeven
  rw [hsmul, Pi.smul_apply, hadd, Pi.add_apply, hg, hrefl, hneg, heven,
    smul_eq_mul]
  exact schwartzEvenPart_apply g x

@[simp] theorem ccmEvenSchwartzSourceCLM_apply (g : 𝓢(ℝ, ℂ)) :
    ccmEvenSchwartzSourceCLM g = ccmEvenSchwartzSource g := by
  exact ccmEvenProjection_toLp g

theorem ccmEvenSchwartzSource_denseRange : DenseRange ccmEvenSchwartzSource := by
  have hp : DenseRange evenProjectionToEven :=
    ccmEvenProjectionToEven_surjective.denseRange
  have hs : DenseRange (fun g : 𝓢(ℝ, ℂ) => g.toLp 2 volume) := by
    have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      (μ := volume) ENNReal.ofNat_ne_top
    change DenseRange (fun g : 𝓢(ℝ, ℂ) => g.toLp 2 volume) at hd
    exact hd
  have hc : DenseRange (fun g : 𝓢(ℝ, ℂ) => evenProjectionToEven (g.toLp 2 volume)) :=
    hp.comp hs evenProjectionToEven.continuous
  simpa only [ccmEvenProjection_toLp] using hc

theorem ccmEvenSchwartzSource_fourier (g : 𝓢(ℝ, ℂ)) :
    evenFourierTransform (ccmEvenSchwartzSource g) =
      ccmEvenSchwartzSource (𝓕 g) := by
  apply Subtype.ext
  rw [coe_evenFourierTransform_apply]
  change 𝓕 ((schwartzEvenPart g).toLp 2 volume) =
    (schwartzEvenPart (𝓕 g)).toLp 2 volume
  rw [SchwartzMap.toLp_fourier_eq, fourier_schwartzEvenPart]

theorem schwartz_integrableOn_norm_mul_rpow_Ioi
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (g : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun t : ℝ => ‖g t‖ * t ^ (-sigma)) (Ioi 0) := by
  have hcont (s : Set ℝ) (hs : s ⊆ Ioi (0 : ℝ)) :
      ContinuousOn (fun t : ℝ => ‖g t‖ * t ^ (-sigma)) s :=
    g.continuous.norm.continuousOn.mul
      (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (hs ht)))
  have hnear : IntegrableOn (fun t : ℝ => ‖g t‖ * t ^ (-sigma)) (Ioo 0 1) := by
    let C : ℝ := SchwartzMap.seminorm ℂ 0 0 g
    have hbase : IntegrableOn (fun t : ℝ => C * t ^ (-sigma)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)).const_mul C
    refine Integrable.mono' hbase
      ((hcont (Ioo 0 1) Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 ≤ t := ht.1.le
    have hrpow : 0 ≤ t ^ (-sigma) := Real.rpow_nonneg ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrpow)]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g t) hrpow
  have hfar : IntegrableOn (fun t : ℝ => ‖g t‖ * t ^ (-sigma)) (Ici 1) := by
    refine Integrable.mono' g.integrable.norm.integrableOn
      ((hcont (Ici 1) fun t ht => mem_Ioi.mpr (zero_lt_one.trans_le ht)).aestronglyMeasurable
        measurableSet_Ici) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hrpow0 : 0 ≤ t ^ (-sigma) := Real.rpow_nonneg ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrpow0)]
    calc
      ‖g t‖ * t ^ (-sigma) ≤ ‖g t‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr hsigma0)) (norm_nonneg _)
      _ = ‖g t‖ := mul_one _
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  exact hnear.union hfar

theorem ccmSchwartz_soninMellinEvaluation_fourier_reflection
    (g : 𝓢(ℝ, ℂ)) (tau : ℝ) :
    soninMellinEvaluation (linePt tau)
        (𝓕 (schwartzEvenPart g) : SchwartzMap ℝ ℂ) =
      soninMellinEvaluation (linePt (-tau)) (schwartzEvenPart g) := by
  let f : 𝓢(ℝ, ℂ) := schwartzEvenPart g
  have hf : Integrable (f : ℝ → ℂ) := f.integrable
  have hFf : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f : SchwartzMap ℝ ℂ).integrable
  have heven : ∀ t : ℝ, f (-t) = f t := schwartzEvenPart_even g
  have hint : IntegrableOn
      (fun t : ℝ => ‖f t‖ * t ^ (-(linePt (-tau)).re)) (Ioi 0) := by
    simpa only [linePt_re] using
      (schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) f)
  have hFint : IntegrableOn
      (fun t : ℝ => ‖(𝓕 (f : ℝ → ℂ)) t‖ *
        t ^ (-(1 - linePt (-tau)).re)) (Ioi 0) := by
    rw [show (𝓕 (f : ℝ → ℂ)) = ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) from
      (SchwartzMap.fourier_coe f).symm]
    have hbase := schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (𝓕 f : SchwartzMap ℝ ℂ)
    convert hbase using 1
    norm_num [Complex.sub_re, linePt_re]
  have h := soninMellinEvaluation_fourier
    (w := linePt (-tau)) (f := (f : ℝ → ℂ))
    (by rw [linePt_re]; norm_num) (by rw [linePt_re]; norm_num)
    hf hFf heven hint hFint
  have hline : 1 - linePt (-tau) = linePt tau := by
    unfold linePt
    push_cast
    ring
  have hFourier : (𝓕 (f : ℝ → ℂ)) = ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    exact (SchwartzMap.fourier_coe f).symm
  rw [hline, hFourier] at h
  exact h.symm

theorem ccmEvenSchwartzSource_integrableOn_criticalMellinNorm (g : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun x : ℝ =>
      ‖((((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) : ℝ → ℂ) x)‖ *
        x ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have hbase := schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (schwartzEvenPart g)
  refine hbase.congr ?_
  filter_upwards [ae_restrict_of_ae (ccmEvenSchwartzSource_coeFn g)] with x hx
  rw [hx]

theorem ccmEvenSchwartzSource_integrableOn_criticalMellinKernel (g : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun x : ℝ =>
      ((((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) : ℝ → ℂ) x) *
        soninMellinKernel (linePt 0) x) (Ioi 0) := by
  refine Integrable.mono' (ccmEvenSchwartzSource_integrableOn_criticalMellinNorm g) ?_ ?_
  · exact (((Lp.stronglyMeasurable
      (((ccmEvenSchwartzSource g : evenSubspace) : SoninL2))).aestronglyMeasurable.restrict).mul
        (aestronglyMeasurable_soninMellinKernel (linePt 0) measurableSet_Ioi
          (fun x hx => mem_Ioi.mpr hx)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_soninMellinKernel hx (linePt 0), linePt_re]

theorem ccmEvenSchwartzSource_burnolLogMellinDensity_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (burnolLogMellinDensity (1 / 2 : ℝ) (ccmEvenSchwartzSource g)) := by
  have hlog := (integrableOn_Ioi_iff_integrable_exp_smul
    (fun x : ℝ =>
      ((((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) : ℝ → ℂ) x) *
        soninMellinKernel (linePt 0) x)).mp
    (ccmEvenSchwartzSource_integrableOn_criticalMellinKernel g)
  refine hlog.congr ?_
  filter_upwards with t
  have h := exp_smul_mellinIntegrand_eq_character_mul_density
    (1 / 2 : ℝ) 0 t (ccmEvenSchwartzSource g)
  simpa [linePt, realProbCharacter] using h

theorem ccmEvenSchwartzSource_logEvenUnitary_ae_density (g : 𝓢(ℝ, ℂ)) :
    (((logEvenUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      fun t => ((Real.sqrt 2 : ℝ) : ℂ) *
        burnolLogMellinDensity (1 / 2 : ℝ) (ccmEvenSchwartzSource g) t := by
  filter_upwards [logEvenUnitary_ae (ccmEvenSchwartzSource g)] with t ht
  rw [ht]
  unfold burnolLogMellinDensity
  rw [show ((1 - (1 / 2 : ℝ)) * t : ℝ) = t / 2 by ring]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

theorem ccmEvenSchwartzSource_logEvenUnitary_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (((logEvenUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ)) := by
  have hd := ccmEvenSchwartzSource_burnolLogMellinDensity_integrable g
  have hmul := hd.const_mul ((Real.sqrt 2 : ℝ) : ℂ)
  exact hmul.congr (ccmEvenSchwartzSource_logEvenUnitary_ae_density g).symm

theorem ccmEvenSchwartzSource_fourierLogEven_ae (g : 𝓢(ℝ, ℂ)) :
    (((fourierUnitary (logEvenUnitary (ccmEvenSchwartzSource g)) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      𝓕 (((logEvenUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ)) := by
  have h := GaloisForLFunctions.RHTower.coeFn_fourier_toLp
    (ccmEvenSchwartzSource_logEvenUnitary_integrable g)
    (Lp.memLp (logEvenUnitary (ccmEvenSchwartzSource g)))
  rw [Lp.toLp_coeFn] at h
  change (((𝓕 (logEvenUnitary (ccmEvenSchwartzSource g)) : SoninL2) : ℝ → ℂ)) =ᵐ[volume] _
  exact h

def ccmEvenSchwartzMellinAmplitude (g : 𝓢(ℝ, ℂ)) (tau : ℝ) : ℂ :=
  (((Real.sqrt MellinL2.spectralNormalization * Real.sqrt 2 : ℝ) : ℂ) *
    (mellinCompletionFactor (linePt tau))⁻¹) *
      soninMellinEvaluation (linePt tau) (schwartzEvenPart g)

theorem archimedeanMellinUnitary_ccmEvenSchwartz_ae (g : 𝓢(ℝ, ℂ)) :
    (((archimedeanMellinUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      ccmEvenSchwartzMellinAmplitude g := by
  rw [ccmArchimedeanMellinUnitary_eq_logFourier]
  let c : ℝ := MellinL2.spectralNormalization
  have hc : 0 < c := MellinL2.spectralNormalization_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdil := dilation_ae c hc
    (fourierUnitary (logEvenUnitary (ccmEvenSchwartzSource g)))
  have hfour := (ccmEvenSchwartzSource_fourierLogEven_ae g).comp_tendsto
    (realMul_quasiMeasurePreserving c hcne).tendsto_ae
  filter_upwards [hdil, hfour] with tau hdil_tau hfour_tau
  change (((dilation c hc
    (fourierUnitary (logEvenUnitary (ccmEvenSchwartzSource g))) : SoninL2) : ℝ → ℂ) tau) = _
  rw [hdil_tau]
  have hFourierIntegral :
      (𝓕 (((logEvenUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ))) (c * tau) =
        ((Real.sqrt 2 : ℝ) : ℂ) *
          ∫ t : ℝ, realProbCharacter (-tau) t *
            burnolLogMellinDensity (1 / 2 : ℝ) (ccmEvenSchwartzSource g) t := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ccmEvenSchwartzSource_logEvenUnitary_ae_density g] with t ht
    rw [ht]
    simp only [smul_eq_mul]
    unfold c MellinL2.spectralNormalization realProbCharacter
    have hphase : -2 * Real.pi * t * ((2 * Real.pi)⁻¹ * tau) = -tau * t := by
      field_simp [Real.pi_ne_zero]
    rw [hphase]
    push_cast
    ring
  have hfour_tau' :
      (((fourierUnitary (logEvenUnitary (ccmEvenSchwartzSource g)) : SoninL2) : ℝ → ℂ) (c * tau)) =
        (𝓕 (((logEvenUnitary (ccmEvenSchwartzSource g) : SoninL2) : ℝ → ℂ))) (c * tau) := by
    simpa only [Function.comp_apply] using hfour_tau
  rw [hfour_tau', hFourierIntegral]
  have hsonin := soninMellinEvaluation_eq_logFourier
    (1 / 2 : ℝ) (-tau) (ccmEvenSchwartzSource g)
  have hline : (((1 / 2 : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * Complex.I) = linePt tau := by
    unfold linePt
    push_cast
    ring
  rw [hline] at hsonin
  rw [ccmEvenSchwartzSource_soninMellinEvaluation] at hsonin
  have hgamma : mellinCompletionFactor (linePt tau) ≠ 0 :=
    mellinCompletionFactor_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)
  unfold ccmEvenSchwartzMellinAmplitude
  rw [hsonin]
  field_simp [hgamma]
  unfold c
  push_cast
  ring

theorem mellinCompletionFactor_line_neg_div (tau : ℝ) :
    mellinCompletionFactor (linePt (-tau)) / mellinCompletionFactor (linePt tau) =
      zetaChi (linePt tau) := by
  unfold mellinCompletionFactor zetaChi
  rw [show linePt (-tau) = 1 - linePt tau by
    unfold linePt
    push_cast
    ring]
  rfl

theorem ccmArchimedeanScatteringPhase_neg (tau : ℝ) :
    ccmArchimedeanScatteringPhase (-tau) = zetaChi (linePt tau) := by
  unfold ccmArchimedeanScatteringPhase
  rw [linePt_neg, zetaChi_conj]
  simp

theorem ccmEvenSchwartzMellinAmplitude_fourier (g : 𝓢(ℝ, ℂ)) (tau : ℝ) :
    ccmEvenSchwartzMellinAmplitude (𝓕 g) tau =
      ccmArchimedeanScatteringPhase (-tau) *
        ccmEvenSchwartzMellinAmplitude g (-tau) := by
  unfold ccmEvenSchwartzMellinAmplitude
  rw [← fourier_schwartzEvenPart g,
    ccmSchwartz_soninMellinEvaluation_fourier_reflection,
    ccmArchimedeanScatteringPhase_neg, ← mellinCompletionFactor_line_neg_div]
  have hpos : mellinCompletionFactor (linePt tau) ≠ 0 :=
    mellinCompletionFactor_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)
  have hneg : mellinCompletionFactor (linePt (-tau)) ≠ 0 :=
    mellinCompletionFactor_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)
  field_simp [hpos, hneg]

theorem archimedeanMellinUnitary_evenFourierTransform_ccmEvenSchwartz (g : 𝓢(ℝ, ℂ)) :
    archimedeanMellinUnitary (evenFourierTransform (ccmEvenSchwartzSource g)) =
      l2Reflection (ccmArchimedeanScatteringL2Multiplier
        (archimedeanMellinUnitary (ccmEvenSchwartzSource g))) := by
  rw [ccmEvenSchwartzSource_fourier]
  apply Lp.ext
  have hamp_neg := (archimedeanMellinUnitary_ccmEvenSchwartz_ae g).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hphase_neg :=
    (ccmArchimedeanScatteringL2Multiplier_ae
      (archimedeanMellinUnitary (ccmEvenSchwartzSource g))).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [archimedeanMellinUnitary_ccmEvenSchwartz_ae (𝓕 g),
    l2Reflection_ae (ccmArchimedeanScatteringL2Multiplier
      (archimedeanMellinUnitary (ccmEvenSchwartzSource g))),
    hphase_neg, hamp_neg] with tau hleft href hphase hamp
  rw [hleft, href]
  rw [show ccmArchimedeanScatteringL2Multiplier
      (archimedeanMellinUnitary (ccmEvenSchwartzSource g)) (-tau) =
        ccmArchimedeanScatteringPhase (-tau) *
          archimedeanMellinUnitary (ccmEvenSchwartzSource g) (-tau) by
      simpa only [Function.comp_apply] using hphase]
  rw [show archimedeanMellinUnitary (ccmEvenSchwartzSource g) (-tau) =
      ccmEvenSchwartzMellinAmplitude g (-tau) by
      simpa only [Function.comp_apply] using hamp]
  exact ccmEvenSchwartzMellinAmplitude_fourier g tau

/-- Connes--Consani's exact archimedean Fourier--Mellin scattering identity. -/
theorem archimedeanMellinUnitary_evenFourierTransform (f : evenSubspace) :
    archimedeanMellinUnitary (evenFourierTransform f) =
      l2Reflection (ccmArchimedeanScatteringL2Multiplier
        (archimedeanMellinUnitary f)) := by
  let L : evenSubspace →L[ℂ] SoninL2 :=
    ccmArchimedeanMellinCLM.comp evenFourierTransform
  let R : evenSubspace →L[ℂ] SoninL2 :=
    l2Reflection.comp
      (ccmArchimedeanScatteringL2Multiplier.comp ccmArchimedeanMellinCLM)
  let P : evenSubspace → Prop := fun x => L x = R x
  apply DenseRange.induction_on (p := P) ccmEvenSchwartzSource_denseRange f
  · exact isClosed_eq L.continuous R.continuous
  · intro g
    exact archimedeanMellinUnitary_evenFourierTransform_ccmEvenSchwartz g

end RHTower
