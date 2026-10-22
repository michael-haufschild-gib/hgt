import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeSourceEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalTimeResponse
import GaloisForLFunctions.HTGeometry.UnitWaveDuhamel
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Exact physical identification of the original native principal source integrals.

The zero-mass sinc propagator is the averaged translation operator. A scalar Wronskian,
L² multiplier integration and retarded Fubini give its exact mass conversion with m=2*pi.
The original pointwise source equation then holds in the L² quotient and satisfies the
existing physical Volterra equation. Uniqueness identifies all three principal channels.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeResponse
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem mul_inner (φ : ℝ → ℂ) (hφ : Measurable φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ ξ, ‖φ ξ‖ ≤ C) (f g : FourierRealL2) :
    inner ℂ g (lpBoundedMulCLM (p := 2) (μ := volume) hφ hC hb f) =
      ∫ ξ, φ ξ*inner ℂ (g ξ) (f ξ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hφ hC hb f] with ξ hξ
  rw [hξ,RCLike.inner_apply',RCLike.inner_apply']
  ring

private theorem mul_time_continuous (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ξ, ‖φ (t,ξ)‖ ≤ C) (f : FourierRealL2) :
    Continuous (fun t => lpBoundedMulCLM (p := 2) (μ := volume)
      ((hφ.comp (continuous_const.prodMk continuous_id)).measurable) hC (hb t) f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_lpBoundedMulCLM_apply
    (fun t => (hφ.comp (continuous_const.prodMk continuous_id)).measurable)
    (hφ.comp (continuous_const.prodMk continuous_id)).measurable hC hb (hb t)
    (fun ξ => (hφ.comp (continuous_id.prodMk continuous_const)).continuousAt) f

private theorem mul_integral (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ξ, ‖φ (t,ξ)‖ ≤ C)
    (ψ : ℝ → ℂ) (hψ : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψB : ∀ ξ, ‖ψ ξ‖ ≤ B)
    {a b : ℝ} (hab : a ≤ b) (he : ∀ ξ, ψ ξ = ∫ t in a..b, φ (t,ξ)) (f : FourierRealL2) :
    (∫ t in a..b, lpBoundedMulCLM (p := 2) (μ := volume)
      ((hφ.comp (continuous_const.prodMk continuous_id)).measurable) hC (hb t) f) =
      lpBoundedMulCLM (p := 2) (μ := volume) hψ hB hψB f := by
  have hT := mul_time_continuous φ hφ hC hb f
  apply ext_inner_left ℂ
  intro g
  have hinner := (innerSL ℂ g).intervalIntegral_comp_comm (hT.intervalIntegrable (μ := volume) a b)
  simp only [innerSL_apply_apply] at hinner
  rw [← hinner]
  simp_rw [mul_inner]
  let μ := volume.restrict (Ioc a b)
  let w (ξ : ℝ) := inner ℂ (g ξ) (f ξ)
  have hw : Integrable w volume := L2.integrable_inner g f
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => φ z*w z.2) (μ.prod volume) :=
    hφ.measurable.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  have hi : Integrable (fun z : ℝ × ℝ => φ z*w z.2) (μ.prod volume) := by
    apply ((hw.norm.const_mul C).comp_snd μ).mono' hm
    apply Eventually.of_forall
    intro z
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (norm_nonneg _)
  rw [intervalIntegral.integral_of_le hab]
  change (∫ t, ∫ ξ, φ (t,ξ)*w ξ ∂volume ∂μ) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  dsimp only
  rw [integral_mul_const,he,intervalIntegral.integral_of_le hab]


private def sine (ω t : ℝ) : ℝ := t*Real.sinc (t*ω)

private theorem sine_eq {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    sine ω t = Real.sin (t*ω)/ω := by
  by_cases ht : t = 0
  · simp [sine,ht]
  · rw [sine,Real.sinc_of_ne_zero (mul_ne_zero ht hω)]
    field_simp

private theorem sine_zero_frequency (t : ℝ) : sine 0 t = t := by simp [sine]

private theorem sine_zero (ω : ℝ) : sine ω 0 = 0 := by simp [sine]

private theorem sine_continuous : Continuous (fun z : ℝ × ℝ => sine z.1 z.2) := by
  unfold sine
  fun_prop

private theorem sine_bound (ω t : ℝ) : |sine ω t| ≤ |t| := by
  rw [sine,abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t*ω)) (abs_nonneg t)

private theorem sine_deriv (ω t : ℝ) : HasDerivAt (sine ω) (Real.cos (t*ω)) t := by
  by_cases hω : ω = 0
  · have he : sine 0 = id := funext sine_zero_frequency
    simp only [hω,he,mul_zero,Real.cos_zero]
    exact hasDerivAt_id t
  · have hd := (((hasDerivAt_id t).mul_const ω).sin).div_const ω
    simp only [one_mul,mul_div_cancel_right₀ _ hω] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => sine_eq hω s))

private theorem cosine_deriv (ω t : ℝ) :
    HasDerivAt (fun s => Real.cos (s*ω)) (-ω^(2 : ℕ)*sine ω t) t := by
  have hd := ((hasDerivAt_id t).mul_const ω).cos
  apply hd.congr_deriv
  by_cases hω : ω = 0
  · simp [hω]
  · simp only [sine_eq hω,id_eq,one_mul]
    field_simp

private theorem sine_mass_identity (ω Ω T : ℝ) :
    sine ω T-sine Ω T =
      ∫ t in (0:ℝ)..T, (Ω^(2 : ℕ)-ω^(2 : ℕ))*sine Ω (T-t)*sine ω t := by
  let W (t : ℝ) := Real.cos ((T-t)*Ω)*sine ω t+sine Ω (T-t)*Real.cos (t*ω)
  have hd (t : ℝ) : HasDerivAt W ((Ω^(2 : ℕ)-ω^(2 : ℕ))*sine Ω (T-t)*sine ω t) t := by
    have h₁ := (cosine_deriv Ω (T-t)).scomp t ((hasDerivAt_const t T).sub (hasDerivAt_id t))
    have h₂ := (sine_deriv Ω (T-t)).scomp t ((hasDerivAt_const t T).sub (hasDerivAt_id t))
    convert! (h₁.mul (sine_deriv ω t)).add (h₂.mul (cosine_deriv ω t)) using 1
    simp only [Function.comp_apply,smul_eq_mul,zero_sub]
    ring
  have hi : IntervalIntegrable (fun t => (Ω^(2 : ℕ)-ω^(2 : ℕ))*sine Ω (T-t)*sine ω t) volume 0 T := by
    apply Continuous.intervalIntegrable
    have h₁ := sine_continuous.comp (show Continuous (fun t : ℝ => (Ω,T-t)) by fun_prop)
    have h₂ := sine_continuous.comp (show Continuous (fun t : ℝ => (ω,t)) by fun_prop)
    exact (continuous_const.mul h₁).mul h₂
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [W,sub_self,mul_zero,Real.cos_zero,sine_zero,one_mul,mul_one,zero_mul,add_zero,sub_zero,zero_add]
    using h.symm



private theorem fourier_integral (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ξ, ‖φ (t,ξ)‖ ≤ C)
    (ψ : ℝ → ℂ) (hψ : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψB : ∀ ξ, ‖ψ ξ‖ ≤ B)
    {a b : ℝ} (hab : a ≤ b) (he : ∀ ξ, ψ ξ = ∫ t in a..b, φ (t,ξ)) (f : FourierRealL2) :
    (∫ t in a..b, fourierMulCLM
      ((hφ.comp (continuous_const.prodMk continuous_id)).measurable) hC (hb t) f) =
      fourierMulCLM hψ hB hψB f := by
  simp_rw [fourierMulCLM_apply]
  rw [(fourierL2inv ℝ).intervalIntegral_comp_comm
    ((mul_time_continuous φ hφ hC hb (fourierL2 ℝ f)).intervalIntegrable (μ := volume) a b)]
  rw [mul_integral φ hφ hC hb ψ hψ hB hψB hab he]

private def freeSymbol (t ξ : ℝ) : ℂ := (sine (2*Real.pi*ξ) t:ℝ)

private theorem freeSymbol_continuous : Continuous (fun z : ℝ × ℝ => freeSymbol z.1 z.2) := by
  have h := sine_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (2*Real.pi*z.2,z.1)) by fun_prop)
  exact Complex.continuous_ofReal.comp h

private theorem freeSymbol_bound (t ξ : ℝ) : ‖freeSymbol t ξ‖ ≤ |t| := by
  simpa only [freeSymbol,Complex.norm_real,Real.norm_eq_abs] using sine_bound (2*Real.pi*ξ) t

/-- Zero-mass unit-speed sine propagator, with its continuous zero-frequency value. -/
def freeWaveSine (t : ℝ) : FourierRealL2 →L[ℂ] FourierRealL2 :=
  fourierMulCLM ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
    (abs_nonneg t) (freeSymbol_bound t)

private theorem freeWaveSine_norm (t : ℝ) : ‖freeWaveSine t‖ ≤ |t| :=
  norm_fourierMulCLM_le _ _ _

private def massiveSymbol (t ξ : ℝ) : ℂ := (sine (2*Real.pi*kgFreq ξ) t:ℝ)

private theorem massiveSymbol_continuous : Continuous (fun z : ℝ × ℝ => massiveSymbol z.1 z.2) := by
  have h := sine_continuous.comp
    (show Continuous (fun z : ℝ × ℝ => (2*Real.pi*kgFreq z.2,z.1)) from
      (continuous_const.mul (continuous_kgFreq.comp continuous_snd)).prodMk continuous_fst)
  exact Complex.continuous_ofReal.comp h

private theorem massiveSymbol_bound (t ξ : ℝ) : ‖massiveSymbol t ξ‖ ≤ |t| := by
  simpa only [massiveSymbol,Complex.norm_real,Real.norm_eq_abs] using sine_bound (2*Real.pi*kgFreq ξ) t

private theorem unitWaveSine_symbol (t : ℝ) : unitWaveSine t =
    fourierMulCLM ((massiveSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
      (abs_nonneg t) (massiveSymbol_bound t) := by
  rw [unitWaveSine,kgSinFreqOp]
  symm
  apply fourierMulCLM_smul _ _ zero_le_one (norm_kgSinOverFreq_le (2*Real.pi*t))
    (abs_nonneg t) (massiveSymbol_bound t)
  apply Eventually.of_forall
  intro ξ
  have hm : 2*Real.pi ≠ 0 := by positivity
  have hk : kgFreq ξ ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_kgFreq ξ)).ne'
  rw [massiveSymbol,sine_eq (mul_ne_zero hm hk)]
  dsimp only [kgSinOverFreq]
  push_cast
  field_simp

private theorem symbol_mass_identity (ξ T : ℝ) :
    freeSymbol T ξ-massiveSymbol T ξ =
      ∫ t in (0:ℝ)..T, ((2*Real.pi)^(2 : ℕ):ℂ)*massiveSymbol (T-t) ξ*freeSymbol t ξ := by
  have hk : (kgFreq ξ)^(2 : ℕ) = 1+ξ^(2 : ℕ) := by
    unfold kgFreq
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs,sq_abs]
  have hdiff : (2*Real.pi*kgFreq ξ)^(2 : ℕ)-(2*Real.pi*ξ)^(2 : ℕ) = (2*Real.pi)^(2 : ℕ) := by
    nlinarith [sq_nonneg (2*Real.pi)]
  have h := congrArg Complex.ofReal (sine_mass_identity (2*Real.pi*ξ) (2*Real.pi*kgFreq ξ) T)
  rw [hdiff,← intervalIntegral.integral_ofReal] at h
  simpa only [freeSymbol,massiveSymbol,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_ofNat] using h



private theorem sine_lipschitz (ω t s : ℝ) : |sine ω t-sine ω s| ≤ |t-s| := by
  by_cases hω : ω = 0
  · simp [hω,sine_zero_frequency]
  · rw [sine_eq hω,sine_eq hω,← sub_div,abs_div,div_le_iff₀ (abs_pos.mpr hω)]
    have h := Real.lipschitzWith_sin.dist_le_mul (t*ω) (s*ω)
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,← sub_mul,abs_mul] using h

private theorem freeWaveSine_operator_continuous : Continuous freeWaveSine := by
  have hl : LipschitzWith 1 freeWaveSine := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [dist_eq_norm,Real.dist_eq]
    simp only [NNReal.coe_one,one_mul]
    have hχ : ∀ ξ, ‖freeSymbol t ξ-freeSymbol s ξ‖ ≤ |t-s| := by
      intro ξ
      simpa only [freeSymbol,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        using sine_lipschitz (2*Real.pi*ξ) t s
    have he := fourierMulCLM_sub
      ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
      ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
      (((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).sub
        (freeSymbol_continuous.comp (continuous_const.prodMk continuous_id))).measurable)
      (abs_nonneg t) (freeSymbol_bound t) (abs_nonneg s) (freeSymbol_bound s)
      (abs_nonneg (t-s)) hχ (Eventually.of_forall (fun _ => rfl))
    change ‖fourierMulCLM _ (abs_nonneg t) (freeSymbol_bound t)-
      fourierMulCLM _ (abs_nonneg s) (freeSymbol_bound s)‖ ≤ _
    rw [← he]
    exact norm_fourierMulCLM_le _ _ _
  exact hl.continuous

private theorem scaled_massive_comp (c : ℝ) (hc : 0 ≤ c) (u v : ℝ)
    (χ : ℝ → ℂ) (hχ : Measurable χ) {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ ξ, ‖χ ξ‖ ≤ C)
    (he : ∀ ξ, χ ξ = (c:ℂ)*massiveSymbol u ξ*freeSymbol v ξ) :
    fourierMulCLM hχ hC hχC = (c:ℂ) • (unitWaveSine u).comp (freeWaveSine v) := by
  have hM := massiveSymbol_continuous.comp
    (show Continuous (fun ξ : ℝ => (u,ξ)) by fun_prop)
  have hm : Measurable (fun ξ => (c:ℂ)*massiveSymbol u ξ) := measurable_const.mul hM.measurable
  have hb : ∀ ξ, ‖(c:ℂ)*massiveSymbol u ξ‖ ≤ c*|u| := by
    intro ξ
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (massiveSymbol_bound u ξ) hc
  have hs := fourierMulCLM_smul hM.measurable hm (abs_nonneg u) (massiveSymbol_bound u)
    (mul_nonneg hc (abs_nonneg u)) hb (c:ℂ) (Eventually.of_forall (fun _ => rfl))
  rw [← unitWaveSine_symbol] at hs
  have hcomp := fourierMulCLM_comp hm
    ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable) hχ
    (mul_nonneg hc (abs_nonneg u)) hb (abs_nonneg v) (freeSymbol_bound v) hC hχC
    (Eventually.of_forall he)
  rw [hs] at hcomp
  exact hcomp.symm

/-- Exact mass conversion on every L² datum, with the original physical free propagator. -/
theorem freeWaveSine_mass_conversion {T : ℝ} (hT : 0 ≤ T) (f : FourierRealL2) :
    freeWaveSine T f = unitWaveSine T f+
      ((2*Real.pi)^(2 : ℕ):ℂ) • ∫ t in (0:ℝ)..T, unitWaveSine (T-t) (freeWaveSine t f) := by
  let c : ℝ := (2*Real.pi)^(2 : ℕ)
  have hc : 0 ≤ c := sq_nonneg _
  let clamp (t : ℝ) := max 0 (min t T)
  have hcl : ∀ t, 0 ≤ clamp t ∧ clamp t ≤ T := by
    intro t
    exact ⟨le_max_left _ _,max_le hT (min_le_right _ _)⟩
  have hce {t : ℝ} (ht : t ∈ Icc 0 T) : clamp t = t := by
    simp only [clamp,min_eq_left ht.2,max_eq_right ht.1]
  let φ (z : ℝ × ℝ) := (c:ℂ)*massiveSymbol (T-clamp z.1) z.2*freeSymbol (clamp z.1) z.2
  have hφ : Continuous φ := by
    have hM := massiveSymbol_continuous.comp
      (show Continuous (fun z : ℝ × ℝ => (T-clamp z.1,z.2)) by dsimp only [clamp]; fun_prop)
    have hF := freeSymbol_continuous.comp
      (show Continuous (fun z : ℝ × ℝ => (clamp z.1,z.2)) by dsimp only [clamp]; fun_prop)
    exact (continuous_const.mul hM).mul hF
  have hb : ∀ t ξ, ‖φ (t,ξ)‖ ≤ c*T^(2 : ℕ) := by
    intro t ξ
    have ht := hcl t
    dsimp only [φ]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    have hM := massiveSymbol_bound (T-clamp t) ξ
    have hF := freeSymbol_bound (clamp t) ξ
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at hM
    rw [abs_of_nonneg ht.1] at hF
    calc c*‖massiveSymbol (T-clamp t) ξ‖*‖freeSymbol (clamp t) ξ‖
        ≤ c*T*T := mul_le_mul
          (mul_le_mul_of_nonneg_left (hM.trans (by linarith [ht.1])) hc)
          (hF.trans ht.2) (norm_nonneg _) (mul_nonneg hc hT)
      _ = c*T^(2 : ℕ) := by ring
  let ψ (ξ : ℝ) := freeSymbol T ξ-massiveSymbol T ξ
  have hψ : Measurable ψ :=
    ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).sub
      (massiveSymbol_continuous.comp (continuous_const.prodMk continuous_id))).measurable
  have hψB : ∀ ξ, ‖ψ ξ‖ ≤ 2*T := by
    intro ξ
    exact (norm_sub_le _ _).trans (by
      have hF := freeSymbol_bound T ξ
      have hM := massiveSymbol_bound T ξ
      rw [abs_of_nonneg hT] at hF hM
      linarith)
  have he : ∀ ξ, ψ ξ = ∫ t in (0:ℝ)..T, φ (t,ξ) := by
    intro ξ
    change freeSymbol T ξ-massiveSymbol T ξ = _
    rw [symbol_mass_identity]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using ht
    dsimp only [φ]
    rw [hce ht']
    simp only [c,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hi := fourier_integral φ hφ (mul_nonneg hc (sq_nonneg T)) hb ψ hψ
    (mul_nonneg (by norm_num) hT) hψB hT he f
  have hs := fourierMulCLM_sub
    ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
    ((massiveSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable) hψ
    (abs_nonneg T) (freeSymbol_bound T) (abs_nonneg T) (massiveSymbol_bound T)
    (mul_nonneg (by norm_num) hT) hψB (Eventually.of_forall (fun _ => rfl))
  rw [← unitWaveSine_symbol] at hs
  rw [hs,sub_apply] at hi
  have hint : (∫ t in (0:ℝ)..T, fourierMulCLM
      ((hφ.comp (continuous_const.prodMk continuous_id)).measurable)
      (mul_nonneg hc (sq_nonneg T)) (hb t) f) =
      (c:ℂ) • ∫ t in (0:ℝ)..T, unitWaveSine (T-t) (freeWaveSine t f) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht' : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using ht
    have he' (ξ : ℝ) : φ (t,ξ) = (c:ℂ)*massiveSymbol (T-t) ξ*freeSymbol t ξ := by
      dsimp only [φ]
      rw [hce ht']
    rw [scaled_massive_comp c hc (T-t) t _ _ _ (hb t) he']
    rfl
  rw [hint] at hi
  change _ = _+((2*Real.pi)^(2 : ℕ):ℂ) • _
  have hc' : (c:ℂ) = ((2*Real.pi)^(2 : ℕ):ℂ) := by simp only [c,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [hc'] at hi
  change _ = freeWaveSine T f-unitWaveSine T f at hi
  exact (sub_eq_iff_eq_add.mp hi.symm).trans (add_comm _ _)



private theorem phase_integral (ω T : ℝ) :
    (∫ t in -T..T, Complex.exp ((t*ω:ℝ)*Complex.I)) = 2*(sine ω T:ℂ) := by
  by_cases hω : ω = 0
  · simp [hω,sine_zero_frequency,Complex.real_smul]
    ring_nf
  · rw [intervalIntegral.integral_comp_mul_right (fun x : ℝ => Complex.exp (x*Complex.I)) hω]
    rw [neg_mul,integral_exp_mul_I_eq_sinc]
    simp only [Complex.real_smul,Complex.ofReal_inv,sine,Complex.ofReal_mul]
    have hωc : (ω:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
    field_simp

private theorem modulation_integral (T ξ : ℝ) :
    (∫ t in -T..T, modulationSymbol t ξ) = 2*freeSymbol T ξ := by
  have he (t : ℝ) : modulationSymbol t ξ = Complex.exp ((t*(2*Real.pi*ξ):ℝ)*Complex.I) := by
    unfold modulationSymbol
    congr 1
    ring
  simp_rw [he]
  exact phase_integral (2*Real.pi*ξ) T

private theorem translation_fourier (t : ℝ) (f : FourierRealL2) :
    translateL2 t f = fourierMulCLM (measurable_modulationSymbol t) zero_le_one
      (norm_modulationSymbol_le t) f := by
  have h : fourierL2 ℝ (translateL2 t f) = modulationMul t (fourierL2 ℝ f) :=
    fourierTransform_translateL2 t f
  have he := congrArg (fourierL2inv ℝ) h
  rw [fourierL2inv_fourierL2] at he
  exact he

/-- The zero-mass sine is the spatial interval operator, expressed intrinsically in L²
as the average of the original translation isometries. -/
theorem freeWaveSine_translation {T : ℝ} (hT : 0 ≤ T) (f : FourierRealL2) :
    freeWaveSine T f = (1/2:ℂ) • ∫ a in -T..T, translateL2 a f := by
  let φ (z : ℝ × ℝ) := modulationSymbol z.1 z.2
  have hφ : Continuous φ := by unfold φ modulationSymbol; fun_prop
  have hψ := (continuous_const : Continuous (fun _ : ℝ => (2:ℂ))).mul
    (freeSymbol_continuous.comp (show Continuous (fun ξ : ℝ => (T,ξ)) by fun_prop))
  have hb : ∀ ξ, ‖(2:ℂ)*freeSymbol T ξ‖ ≤ 2*T := by
    intro ξ
    rw [norm_mul,show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left
      ((freeSymbol_bound T ξ).trans_eq (abs_of_nonneg hT)) (by norm_num)
  have hi := fourier_integral φ hφ zero_le_one norm_modulationSymbol_le
    (fun ξ => 2*freeSymbol T ξ) hψ.measurable (mul_nonneg (by norm_num) hT) hb
    (by linarith : -T ≤ T) (fun ξ => (modulation_integral T ξ).symm) f
  have hs := fourierMulCLM_smul
    ((freeSymbol_continuous.comp (continuous_const.prodMk continuous_id)).measurable)
    hψ.measurable (abs_nonneg T) (freeSymbol_bound T) (mul_nonneg (by norm_num) hT) hb
    (2:ℂ) (Eventually.of_forall (fun _ => rfl))
  rw [hs,smul_apply] at hi
  change _ = (2:ℂ) • freeWaveSine T f at hi
  have hleft : (∫ t in -T..T, fourierMulCLM
      ((hφ.comp (continuous_const.prodMk continuous_id)).measurable) zero_le_one
      (norm_modulationSymbol_le t) f) = ∫ t in -T..T, translateL2 t f := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (translation_fourier t f).symm
  rw [hleft] at hi
  rw [hi,smul_smul]
  norm_num


private theorem duhamel_triangle (f : ℝ → ℝ → FourierRealL2)
    (hf : Continuous (Function.uncurry f)) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, ∫ y in x..r, f x y) = ∫ y in l..r, ∫ x in l..y, f x y := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let g (x y : ℝ) := if x ≤ y then f x y else 0
  have hi : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hg : Integrable (Function.uncurry g) (μ.prod μ) := by
    convert! hi.indicator (measurableSet_le measurable_fst measurable_snd) using 1
  have hleft : (∫ x in l..r, ∫ y in x..r, f x y) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    have hset : Ioc l r ∩ Ici x = Icc x r := by
      ext y
      simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨hxy,hy⟩; exact ⟨hy,hxy.2⟩
      · rintro ⟨hxy,hy⟩; exact ⟨⟨hx.1.trans_le hxy,hy⟩,hxy⟩
    have he : g x = (Ici x).indicator (f x) := by
      funext y; rfl
    change _ = ∫ y in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx.2]
  have hright : (∫ y in l..r, ∫ x in l..y, f x y) = ∫ y, ∫ x, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only
    have hset : Ioc l r ∩ Iic y = Ioc l y := by
      ext x
      simp only [mem_inter_iff,mem_Ioc,mem_Iic]
      constructor
      · rintro ⟨hxy,hx⟩; exact ⟨hxy.1,hx⟩
      · rintro ⟨hx,hxy⟩; exact ⟨⟨hx,hxy.trans hy.2⟩,hxy⟩
    have he : (fun x => g x y) = (Iic y).indicator (fun x => f x y) := by
      funext x; rfl
    change _ = ∫ x in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Iic,hset,intervalIntegral.integral_of_le hy.1.le]
  rw [hleft,hright]
  exact integral_integral_swap hg

/-- Retarded Duhamel integral of the unit-speed zero-mass spatial interval operator. -/
def freeWaveDuhamel (F : ℝ → FourierRealL2) (T : ℝ) : FourierRealL2 :=
  ∫ t in (0:ℝ)..T, freeWaveSine (T-t) (F t)

private theorem freeWaveDuhamel_continuous (F : ℝ → FourierRealL2) (hF : Continuous F) :
    Continuous (freeWaveDuhamel F) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_id
  exact (freeWaveSine_operator_continuous.comp (continuous_fst.sub continuous_snd)).clm_apply
    (hF.comp continuous_snd)

private theorem duhamel_association (F : ℝ → FourierRealL2) (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ∫ a in (0:ℝ)..(T-t),
      unitWaveSine (T-t-a) (freeWaveSine a (F t))) =
      unitWaveDuhamel (freeWaveDuhamel F) T := by
  let k (t s : ℝ) := unitWaveSine (T-s) (freeWaveSine (s-t) (F t))
  have hk : Continuous (Function.uncurry k) :=
    unitWaveSine_continuous_comp _ _ (continuous_const.sub continuous_snd)
      ((freeWaveSine_operator_continuous.comp (continuous_snd.sub continuous_fst)).clm_apply
        (hF.comp continuous_fst))
  have he (t : ℝ) : (∫ a in (0:ℝ)..(T-t), unitWaveSine (T-t-a) (freeWaveSine a (F t))) =
      ∫ s in t..T, k t s := by
    have hs := intervalIntegral.integral_comp_add_right (f := k t) (a := (0:ℝ)) (b := T-t) t
    simp only [zero_add,sub_add_cancel] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro a ha
    dsimp only [k]
    rw [show T-t-a = T-(a+t) by ring,add_sub_cancel_right]
  simp_rw [he]
  rw [duhamel_triangle k hk hT]
  unfold unitWaveDuhamel freeWaveDuhamel
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only [k]
  exact (unitWaveSine (T-s)).intervalIntegral_comp_comm
    (((freeWaveSine_operator_continuous.comp (continuous_const.sub continuous_id)).clm_apply hF).intervalIntegrable (μ := volume) 0 s)

/-- The exact free-mass conversion for every continuous L² source.
The mass is that of the existing physical sine propagator, not an adjustable normalization. -/
theorem freeWaveDuhamel_mass_conversion (F : ℝ → FourierRealL2) (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) :
    freeWaveDuhamel F T = unitWaveDuhamel F T+
      ((2*Real.pi)^(2 : ℕ):ℂ) • unitWaveDuhamel (freeWaveDuhamel F) T := by
  have hM := unitWaveSine_continuous_comp (fun t => T-t) F (continuous_const.sub continuous_id) hF
  have hK : Continuous (fun z : ℝ × ℝ =>
      unitWaveSine (T-z.1-z.2) (freeWaveSine z.2 (F z.1))) :=
    unitWaveSine_continuous_comp _ _ ((continuous_const.sub continuous_fst).sub continuous_snd)
      ((freeWaveSine_operator_continuous.comp continuous_snd).clm_apply (hF.comp continuous_fst))
  have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun t a => unitWaveSine (T-t-a) (freeWaveSine a (F t))) hK
    (show Continuous (fun t : ℝ => T-t) from continuous_const.sub continuous_id)
  have he : freeWaveDuhamel F T = ∫ t in (0:ℝ)..T,
      unitWaveSine (T-t) (F t)+((2*Real.pi)^(2 : ℕ):ℂ) •
        ∫ a in (0:ℝ)..(T-t), unitWaveSine (T-t-a) (freeWaveSine a (F t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using ht
    exact freeWaveSine_mass_conversion (sub_nonneg.mpr ht'.2) (F t)
  have hadd := intervalIntegral.integral_add (hM.intervalIntegrable (μ := volume) 0 T)
    ((hI.const_smul ((2*Real.pi)^(2 : ℕ):ℂ)).intervalIntegrable (μ := volume) 0 T)
  simp only [Pi.smul_apply] at hadd
  rw [he,hadd,intervalIntegral.integral_smul,duhamel_association F hF hT]
  rfl

private theorem l2_integral_eq (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (u : ℝ → FourierRealL2) (hu : Continuous u) (v : FourierRealL2)
    {a b : ℝ} (hab : a ≤ b)
    (he : ∀ t ∈ Icc a b, (u t : ℝ → ℂ) =ᵐ[volume] fun x => f (t,x))
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x => ∫ t in a..b, f (t,x)) :
    (∫ t in a..b, u t) = v := by
  apply ext_inner_left ℂ
  intro g
  have hinner := (innerSL ℂ g).intervalIntegral_comp_comm (hu.intervalIntegrable (μ := volume) a b)
  simp only [innerSL_apply_apply] at hinner
  rw [← hinner,L2.inner_def]
  let μ := volume.restrict (Ioc a b)
  let k (z : ℝ × ℝ) := inner ℂ (g z.2) (f z)
  have hk : AEStronglyMeasurable k (μ.prod volume) :=
    (Lp.aestronglyMeasurable g).comp_snd.inner hf.measurable.aestronglyMeasurable
  have hslice (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x => k (t,x)) =ᵐ[volume] fun x => inner ℂ (g x) (u t x) := by
    filter_upwards [he t ht] with x hx
    dsimp only [k]; rw [hx]
  have hi : Integrable k (μ.prod volume) := by
    apply (integrable_prod_iff hk).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (L2.integrable_inner g (u t)).congr (hslice t ⟨ht.1.le,ht.2⟩).symm
    · have hbound : Integrable (fun t => ‖g‖^(2 : ℕ)+‖u t‖^(2 : ℕ)) μ :=
        ((continuous_const.add (hu.norm.pow 2)).intervalIntegrable (μ := volume) a b).1
      apply hbound.mono' hk.norm.integral_prod_right'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have heq := integral_congr_ae ((hslice t ⟨ht.1.le,ht.2⟩).fun_comp norm)
      simp only [Function.comp_apply] at heq
      rw [heq]
      have hg := (Lp.memLp g).norm.integrable_sq
      have hu' := (Lp.memLp (u t)).norm.integrable_sq
      calc
        (∫ x, ‖inner ℂ (g x) (u t x)‖) ≤ ∫ x, ‖g x‖^(2 : ℕ)+‖u t x‖^(2 : ℕ) := by
          apply integral_mono (L2.integrable_inner g (u t)).norm (hg.add hu')
          intro x
          dsimp only [Pi.add_apply]
          have hn := norm_inner_le_norm (g x) (u t x) (𝕜 := ℂ)
          nlinarith [sq_nonneg (‖g x‖-‖u t x‖)]
        _ = ‖g‖^(2 : ℕ)+‖u t‖^(2 : ℕ) := by
          rw [integral_add hg hu',← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq,
            ← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hleft : (∫ t in a..b, inner ℂ g (u t)) = ∫ t, ∫ x, k (t,x) ∂volume ∂μ := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [L2.inner_def]
    exact integral_congr_ae (hslice t ⟨ht.1.le,ht.2⟩).symm
  rw [hleft,integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx,intervalIntegral.integral_of_le hab]
  dsimp only [k]
  have hfx : IntegrableOn (fun t => f (t,x)) (Ioc a b) volume :=
    ((hf.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))).intervalIntegrable (μ := volume) a b).1
  exact (innerSL ℂ (g x)).integral_comp_comm hfx

private theorem translate_continuous (u : FourierRealL2) : Continuous (fun t => translateL2 t u) := by
  simp_rw [translation_fourier]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_fourierMulCLM_apply
  intro ξ
  exact (show Continuous (fun t : ℝ => modulationSymbol t ξ) by
    unfold modulationSymbol; fun_prop).continuousAt

private theorem box_memLp (f : ℝ → ℂ) (hf : Continuous f) {R T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ x, R < |x| → f x = 0) : MemLp (fun x => ∫ t in -T..T, f (x+t)) 2 volume := by
  have hc : Continuous (fun x => ∫ t in -T..T, f (x+t)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x t => f (x+t)) (hf.comp (continuous_fst.add continuous_snd)) continuous_const
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-(R+T)) (R+T)) isCompact_Icc
  intro x hx
  have hx' : R+T < |x| := by
    by_contra h; exact hx (abs_le.mp (le_of_not_gt h))
  refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
  intro t ht
  have ht' : t ∈ Icc (-T) T := by simpa [uIcc_of_le (by linarith : -T ≤ T)] using ht
  apply hz
  have hb := abs_sub_le x (x+t) 0
  rw [show x-(x+t) = -t by ring,abs_neg,sub_zero,sub_zero] at hb
  have ha : |t| ≤ T := abs_le.mpr ht'
  linarith

private theorem freeWaveSine_interval_ae (f : ℝ → ℂ) (hf : Continuous f)
    (u : FourierRealL2) (he : (u : ℝ → ℂ) =ᵐ[volume] f)
    {R T : ℝ} (hT : 0 ≤ T) (hz : ∀ x, R < |x| → f x = 0) :
    (freeWaveSine T u : ℝ → ℂ) =ᵐ[volume]
      fun x => (1/2:ℂ)*∫ y in x-T..x+T, f y := by
  let v := (box_memLp f hf hT hz).toLp (fun x => ∫ t in -T..T, f (x+t))
  have hv := (box_memLp f hf hT hz).coeFn_toLp
  have hi : (∫ t in -T..T, translateL2 t u) = v := by
    apply l2_integral_eq (fun z => f (z.2+z.1))
      (hf.comp (continuous_snd.add continuous_fst)) _ (translate_continuous u) v
      (by linarith)
    · intro t ht
      filter_upwards [coeFn_translateL2 t u,
        (measurePreserving_add_right volume t).quasiMeasurePreserving.ae he] with x hx hy
      exact hx.trans hy
    · exact hv
  rw [freeWaveSine_translation hT u,hi]
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) v,hv] with x hs hx
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hx]
  congr 1
  have h := intervalIntegral.integral_comp_add_left (f := f) (a := -T) (b := T) x
  simpa only [sub_eq_add_neg] using h

open D4BMJointSource D4BMModularCore

private theorem source_continuous (s a : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s a z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  exact h₁.sub h₂

private theorem source_zero_outside (s a : ℂ) {τ x : ℝ} (hx : τ < |x|) :
    oddSource s a τ x = 0 := by
  by_cases hn : x ≤ 0
  · simp only [oddSource,min_eq_left hn,min_eq_right (neg_nonneg.mpr hn),source_boundary,sub_zero]
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonpos hn] at hx
    linarith
  · have hp : 0 ≤ x := le_of_not_ge hn
    simp only [oddSource,min_eq_right hp,min_eq_left (neg_nonpos.mpr hp),source_boundary,zero_sub]
    apply neg_eq_zero.mpr
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonneg hp] at hx
    linarith

private theorem potential_exact (q : XiZeroCopy) (i : Fin 3) (x : ℝ) :
    principalWavePotential q i x-((2*Real.pi)^(2 : ℕ):ℂ) =
      (-principalExponent q i)*(-principalExponent q i+1)/(Real.cosh x:ℂ)^(2 : ℕ) := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hh : horizonCoordinate x = 1/(Real.cosh x)^(2 : ℕ) := by
    unfold horizonCoordinate radialUnit
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [principalWavePotential,hh]
  push_cast
  ring

private def nativeValue (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ x : ℝ) : ℂ :=
  principalAmplitude q i*radialResponse (-principalExponent q i) (physicalRate q branch) a τ x

private theorem nativeValue_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => nativeValue q branch a i z.1 z.2) :=
  continuous_const.mul (radialResponse_continuous _ _ _)

private theorem nativeValue_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    (nativePrincipalResponse q branch a i τ : ℝ → ℂ) =ᵐ[volume] nativeValue q branch a i τ := by
  filter_upwards [Lp.coeFn_smul (principalAmplitude q i)
    (radialResponseVector (-principalExponent q i) (physicalRate q branch) a τ),
    (radialResponse_memLp (-principalExponent q i) (physicalRate q branch) a τ).coeFn_toLp]
    with x hs hx
  change (principalAmplitude q i • radialResponseVector _ _ _ τ) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  exact congrArg (fun z => principalAmplitude q i*z) hx

private def effectiveValue (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (z : ℝ × ℝ) : ℂ :=
  principalAmplitude q i*oddSource (physicalRate q branch) a z.1 z.2+
    (principalWavePotential q i z.2-((2*Real.pi)^(2 : ℕ):ℂ))*nativeValue q branch a i z.1 z.2

private def effectiveVector (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) : FourierRealL2 :=
  principalTimeForcing q branch a i τ+principalWavePotentialOp q i (nativePrincipalResponse q branch a i τ)-
    ((2*Real.pi)^(2 : ℕ):ℂ) • nativePrincipalResponse q branch a i τ

private theorem effectiveValue_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (effectiveValue q branch a i) := by
  have hp : Continuous (fun z : ℝ × ℝ => principalWavePotential q i z.2) := by
    unfold principalWavePotential
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp (horizonCoordinate_continuous.comp continuous_snd)))
  exact (continuous_const.mul (source_continuous _ _)).add
    ((hp.sub continuous_const).mul (nativeValue_continuous q branch a i))

private theorem effectiveVector_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (effectiveVector q branch a i) :=
  ((principalTimeForcing_continuous q branch a i).add
    ((principalWavePotentialOp q i).continuous.comp (nativePrincipalResponse_continuous q branch a i))).sub
    ((nativePrincipalResponse_continuous q branch a i).const_smul ((2*Real.pi)^(2 : ℕ):ℂ))

private theorem effectiveVector_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    (effectiveVector q branch a i τ : ℝ → ℂ) =ᵐ[volume] fun x => effectiveValue q branch a i (τ,x) := by
  let u := nativePrincipalResponse q branch a i τ
  let f := principalTimeForcing q branch a i τ
  let p := principalWavePotentialOp q i u
  filter_upwards [Lp.coeFn_sub (f+p) (((2*Real.pi)^(2 : ℕ):ℂ) • u),Lp.coeFn_add f p,
    Lp.coeFn_smul ((2*Real.pi)^(2 : ℕ):ℂ) u,principalWavePotentialOp_ae q i u,
    principalForcing_ae_oddSource q branch a i τ,nativeValue_ae q branch a i τ] with x hsub hadd hsmul hp hf hu
  change (f+p-((2*Real.pi)^(2 : ℕ):ℂ) • u) x = _
  rw [hsub]
  dsimp only [Pi.sub_apply]
  rw [hadd]
  dsimp only [Pi.add_apply]
  rw [hsmul,hp]
  change f x+principalWavePotential q i x*u x-((2*Real.pi)^(2 : ℕ):ℂ)*u x = _
  rw [hf,hu]
  dsimp only [effectiveValue]
  ring

private theorem effectiveValue_zero_outside (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    {τ x : ℝ} (hx : max τ 0 < |x|) : effectiveValue q branch a i (τ,x) = 0 := by
  simp only [effectiveValue,nativeValue,
    source_zero_outside _ _ ((le_max_left τ 0).trans_lt hx),
    radialResponse_zero_outside _ _ _ τ x hx,mul_zero,add_zero]

private theorem nativeValue_free (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    nativeValue q branch a i τ x = ∫ σ in (0:ℝ)..τ,
      (1/2:ℂ)*∫ y in x-(τ-σ)..x+(τ-σ), effectiveValue q branch a i (σ,y) := by
  unfold nativeValue
  rw [radialResponse_freeDuhamel _ _ _ hτ]
  simp only [effectiveValue,nativeValue,potential_exact]
  simp_rw [show ∀ σ y, principalAmplitude q i*oddSource (physicalRate q branch) a σ y+
      ((-principalExponent q i)*(-principalExponent q i+1)/(Real.cosh y:ℂ)^(2 : ℕ))*
        (principalAmplitude q i*radialResponse (-principalExponent q i) (physicalRate q branch) a σ y) =
      principalAmplitude q i*(oddSource (physicalRate q branch) a σ y+
        (-principalExponent q i)*(-principalExponent q i+1)/(Real.cosh y:ℂ)^(2 : ℕ)*
          radialResponse (-principalExponent q i) (physicalRate q branch) a σ y) by intros; ring]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

private theorem native_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    {τ : ℝ} (hτ : τ ≤ 0) : nativePrincipalResponse q branch a i τ = 0 := by
  apply Lp.ext
  filter_upwards [nativeValue_ae q branch a i τ,Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
  rw [hx,hz]
  simp only [nativeValue,radialResponse_zero_of_nonpos _ _ _ τ x hτ,mul_zero,Pi.zero_apply]

private theorem effective_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    {τ : ℝ} (hτ : τ ≤ 0) : effectiveVector q branch a i τ = 0 := by
  simp only [effectiveVector,principalTimeForcing_zero_of_nonpos q branch a i τ hτ,
    native_nonpos q branch a i hτ,map_zero,smul_zero,add_zero,sub_zero]

private theorem native_free_L2 (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (T : ℝ) :
    nativePrincipalResponse q branch a i T = freeWaveDuhamel (effectiveVector q branch a i) T := by
  by_cases hT : 0 ≤ T
  · let k (z : ℝ × ℝ) := (1/2:ℂ)*∫ y in z.2-(T-z.1)..z.2+(T-z.1),
      effectiveValue q branch a i (z.1,y)
    have hraw : Continuous (fun p : (ℝ × ℝ) × ℝ => effectiveValue q branch a i (p.1.1,p.2)) :=
      (effectiveValue_continuous q branch a i).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) (f := fun z : ℝ × ℝ => fun y => effectiveValue q branch a i (z.1,y)) hraw
      (show Continuous (fun z : ℝ × ℝ => z.2+(T-z.1)) by fun_prop)
    have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) (f := fun z : ℝ × ℝ => fun y => effectiveValue q branch a i (z.1,y)) hraw
      (show Continuous (fun z : ℝ × ℝ => z.2-(T-z.1)) by fun_prop)
    have hk : Continuous k := by
      have he (z : ℝ × ℝ) : k z = (1/2:ℂ)*((∫ y in (0:ℝ)..z.2+(T-z.1), effectiveValue q branch a i (z.1,y))-
          ∫ y in (0:ℝ)..z.2-(T-z.1), effectiveValue q branch a i (z.1,y)) := by
        dsimp only [k]
        have hc : Continuous (fun y => effectiveValue q branch a i (z.1,y)) :=
          (effectiveValue_continuous q branch a i).comp (continuous_const.prodMk continuous_id)
        exact congrArg (fun w : ℂ => (1/2:ℂ)*w) (intervalIntegral.integral_interval_sub_left
          (hc.intervalIntegrable (μ := volume) 0 (z.2+(T-z.1)))
          (hc.intervalIntegrable (μ := volume) 0 (z.2-(T-z.1)))).symm
      simp_rw [funext he]
      exact continuous_const.mul (h₁.sub h₂)
    symm
    apply l2_integral_eq k hk _
      ((freeWaveSine_operator_continuous.comp (continuous_const.sub continuous_id)).clm_apply
        (effectiveVector_continuous q branch a i)) _ hT
    · intro t ht
      exact freeWaveSine_interval_ae _
        ((effectiveValue_continuous q branch a i).comp (continuous_const.prodMk continuous_id))
        _ (effectiveVector_ae q branch a i t) (sub_nonneg.mpr ht.2)
        (fun x hx => effectiveValue_zero_outside q branch a i hx)
    · filter_upwards [nativeValue_ae q branch a i T] with x hx
      exact hx.trans (nativeValue_free q branch a i hT x)
  · rw [native_nonpos q branch a i (le_of_not_ge hT)]
    symm
    unfold freeWaveDuhamel
    refine (intervalIntegral.integral_congr (g := fun _ => (0:FourierRealL2)) ?_).trans (by simp)
    intro t ht
    have ht' : t ≤ 0 := (show t ∈ Icc T 0 by simpa [uIcc_of_ge (le_of_not_ge hT)] using ht).2
    dsimp only
    rw [effective_nonpos q branch a i ht',map_zero]

private theorem massive_add (F G : ℝ → FourierRealL2) (hF : Continuous F) (hG : Continuous G) (T : ℝ) :
    unitWaveDuhamel (fun t => F t+G t) T = unitWaveDuhamel F T+unitWaveDuhamel G T := by
  unfold unitWaveDuhamel
  simp_rw [map_add]
  exact intervalIntegral.integral_add
    ((unitWaveSine_continuous_comp _ F (continuous_const.sub continuous_id) hF).intervalIntegrable 0 T)
    ((unitWaveSine_continuous_comp _ G (continuous_const.sub continuous_id) hG).intervalIntegrable 0 T)

private theorem massive_smul (c : ℂ) (F : ℝ → FourierRealL2) (T : ℝ) :
    unitWaveDuhamel (fun t => c • F t) T = c • unitWaveDuhamel F T := by
  unfold unitWaveDuhamel
  simp_rw [map_smul,intervalIntegral.integral_smul]

/-- The original Riemann-kernel source integral equals the constructed physical causal response
in every one of the three principal channels, with no inverse-identification hypothesis. -/
theorem nativePrincipalResponse_eq_principalTimeResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    nativePrincipalResponse q branch a i = principalTimeResponse q branch a i := by
  apply principalTimeResponse_unique q branch a i _ (nativePrincipalResponse_continuous q branch a i)
  intro T
  by_cases hT : 0 ≤ T
  · have he : freeWaveDuhamel (effectiveVector q branch a i) = nativePrincipalResponse q branch a i := by
      funext t; exact (native_free_L2 q branch a i t).symm
    have h := freeWaveDuhamel_mass_conversion _ (effectiveVector_continuous q branch a i) hT
    rw [he] at h
    have ha := massive_add (effectiveVector q branch a i)
      (fun t => ((2*Real.pi)^(2 : ℕ):ℂ) • nativePrincipalResponse q branch a i t)
      (effectiveVector_continuous q branch a i)
      ((nativePrincipalResponse_continuous q branch a i).const_smul ((2*Real.pi)^(2 : ℕ):ℂ)) T
    rw [massive_smul] at ha
    rw [← ha] at h
    have hi : (fun t => effectiveVector q branch a i t+
        ((2*Real.pi)^(2 : ℕ):ℂ) • nativePrincipalResponse q branch a i t) =
        fun t => principalTimeForcing q branch a i t+principalWavePotentialOp q i (nativePrincipalResponse q branch a i t) := by
      funext t
      exact sub_add_cancel _ _
    rw [hi] at h
    exact h.trans (massive_add (principalTimeForcing q branch a i)
      (fun t => principalWavePotentialOp q i (nativePrincipalResponse q branch a i t))
      (principalTimeForcing_continuous q branch a i)
      ((principalWavePotentialOp q i).continuous.comp (nativePrincipalResponse_continuous q branch a i)) T)
  · have ht := le_of_not_ge hT
    rw [native_nonpos q branch a i ht,
      unitWaveDuhamel_zero_of_nonpos _ (principalTimeForcing_zero_of_nonpos q branch a i) T ht,zero_add]
    symm
    refine (intervalIntegral.integral_congr (g := fun _ => (0:FourierRealL2)) ?_).trans (by simp)
    intro t ht'
    have ht₀ : t ≤ 0 := (show t ∈ Icc T 0 by simpa [uIcc_of_ge ht] using ht').2
    dsimp only
    rw [native_nonpos q branch a i ht₀,map_zero,map_zero]

end
end RHTower.D4BMNativeResponse
