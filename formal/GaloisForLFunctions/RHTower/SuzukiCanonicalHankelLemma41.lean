import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelKernelInversion
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Suzuki (2012), Lemma 4.1: literal kernel equals spectral unitary

This module closes the remaining operator seam in Lemma 4.1.  It proves that the literal arithmetic
kernel output is in L² and equals the previously constructed spectral Hankel unitary on every
compactly supported smooth logarithmic source.  The proof uses the exact contour inversion from
`SuzukiCanonicalHankelKernelInversion`, Plancherel, and the corpus's explicit positive-half-line
carrier.  No proxy operator, assumed transform law, numerical computation, RH premise, or new axiom
occurs.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform Convolution ENNReal

namespace RHTower
noncomputable section

theorem suzuki_fourierUnitary_symm_eq_reflection_fourier (f : SoninL2) :
    fourierUnitary.symm f = l2Reflection (fourierUnitary f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary.apply_symm_apply, fourierUnitary_l2Reflection]
  rw [show fourierUnitary (fourierUnitary f) = l2Reflection f by
    simpa [fourierUnitary] using l2_fourier_fourier f]
  exact (l2Reflection_involutive f).symm

theorem suzuki_l2_fourierInv_coeFn_eq_l1_fourierInv_of_integrable
    (f : SoninL2) (hf : Integrable (f : ℝ → ℂ)) :
    (fourierUnitary.symm f : ℝ → ℂ) =ᵐ[volume]
      fun x => FourierTransform.fourierInv (f : ℝ → ℂ) x := by
  rw [suzuki_fourierUnitary_symm_eq_reflection_fourier]
  have href := l2Reflection_ae (fourierUnitary f)
  have hfourier := l2_fourier_coeFn_eq_l1_fourier_of_integrable f hf
  have hfourierNeg := hfourier.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [href, hfourierNeg] with x hrefx hfx
  rw [hrefx]
  change fourierUnitary f (-x) = _ at hfx
  rw [hfx]
  change Real.Lp.fourierTransform
      ((memLp_one_iff_integrable.mpr hf).toLp (f : ℝ → ℂ)) (-x) = _
  rw [Real.Lp.fourierTransform_apply]
  rw [Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_congr_ae
    (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)) (-x)

def suzukiBoundaryLogHankelSymbol
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (xi : ℝ) : ℂ :=
  suzukiCanonicalTheta omega ((-2 * Real.pi * xi : ℝ) : ℂ) *
    deningerMeyerStrongLogMellin g
      (((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I)

theorem integrable_suzukiBoundaryLogHankelSymbol
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget) :
    Integrable (suzukiBoundaryLogHankelSymbol omega g) := by
  let C : ℝ :=
    (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 0 g t) +
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 0 g t
  have hscale : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hmajorant : Integrable (fun xi : ℝ =>
      C * (1 + (2 * Real.pi * xi) ^ 2)⁻¹) := by
    exact (integrable_inv_one_add_sq.comp_mul_left' hscale).const_mul C
  have hcontinuous : Continuous (suzukiBoundaryLogHankelSymbol omega g) := by
    unfold suzukiBoundaryLogHankelSymbol
    exact ((continuous_suzukiThetaBoundary hinner).comp (by fun_prop)).mul
      ((differentiable_deningerMeyerStrongLogMellin g.property).continuous.comp
        (by fun_prop))
  apply Integrable.mono' hmajorant hcontinuous.aestronglyMeasurable
  filter_upwards [] with xi
  rw [suzukiBoundaryLogHankelSymbol, norm_mul]
  have hM := norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
    (c := 0) (sigma := 0) g (by norm_num) (by norm_num) le_rfl
      (2 * Real.pi * xi)
  have htheta : ‖suzukiCanonicalTheta omega ((-2 * Real.pi * xi : ℝ) : ℂ)‖ = 1 := by
    simpa only [suzukiThetaBoundary] using
      norm_suzukiThetaBoundary hinner (-2 * Real.pi * xi)
  rw [htheta, one_mul]
  simpa only [ofReal_zero, zero_add, C] using hM

theorem memLp_two_suzukiBoundaryLogHankelSymbol
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget) :
    MemLp (suzukiBoundaryLogHankelSymbol omega g) 2 volume := by
  let C : ℝ :=
    (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 0 g t) +
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 0 g t
  have hC : 0 ≤ C := by
    dsimp only [C]
    apply add_nonneg <;> apply integral_nonneg <;> intro t <;>
      simp only [deningerMeyerQuadraticStripMajorant0,
        deningerMeyerQuadraticStripMajorant2] <;> positivity
  apply memLp_two_of_integrable_of_norm_le
    (integrable_suzukiBoundaryLogHankelSymbol hinner g) (C := C)
  intro xi
  rw [suzukiBoundaryLogHankelSymbol, norm_mul]
  have htheta : ‖suzukiCanonicalTheta omega ((-2 * Real.pi * xi : ℝ) : ℂ)‖ = 1 := by
    simpa only [suzukiThetaBoundary] using
      norm_suzukiThetaBoundary hinner (-2 * Real.pi * xi)
  rw [htheta, one_mul]
  have hM := norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
    (c := 0) (sigma := 0) g (by norm_num) (by norm_num) le_rfl
      (2 * Real.pi * xi)
  calc
    ‖deningerMeyerStrongLogMellin (↑g) (↑(2 * Real.pi * xi) * I)‖ ≤
        C * (1 + (2 * Real.pi * xi) ^ 2)⁻¹ := by
          simpa only [ofReal_zero, zero_add, C] using hM
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (2 * Real.pi * xi)])) hC
    _ = C := mul_one C

theorem fourierInv_suzukiBoundaryLogHankelSymbol_eq_literal
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) (r : ℝ) :
    FourierTransform.fourierInv (suzukiBoundaryLogHankelSymbol omega g) r =
      suzukiLiteralLogHankel omega g r := by
  have hc0 : 0 ≤ c := by linarith
  have hshift := integral_suzukiCanonicalHankelContourIntegrand_shift
    hc0 hinner g r
  have hhigh := integral_suzukiCanonicalHankelContourIntegrand_eq_literalLogHankel
    homega hc hinner g hg r
  have hboundary :
      (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (u : ℂ)) =
        (2 * Real.pi : ℂ) * suzukiLiteralLogHankel omega g r := by
    rw [← hshift]
    exact hhigh
  have hdilation := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => suzukiCanonicalHankelContourIntegrand omega g r (u : ℂ))
      (-2 * Real.pi)
  have habs : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hboundaryInv :
      (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (u : ℂ)) =
        (2 * Real.pi : ℂ) *
          FourierTransform.fourierInv (suzukiBoundaryLogHankelSymbol omega g) r := by
    rw [Real.fourierInv_eq']
    calc
      (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (u : ℂ)) =
        (2 * Real.pi : ℂ) *
          ∫ xi : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
            ((-2 * Real.pi * xi : ℝ) : ℂ) := by
              rw [hdilation, habs, Complex.real_smul]
              push_cast
              field_simp [Real.pi_ne_zero]
      _ = (2 * Real.pi : ℂ) *
          ∫ xi : ℝ, Complex.exp
              (((2 * Real.pi * inner ℝ xi r : ℝ) : ℂ) * Complex.I) •
                suzukiBoundaryLogHankelSymbol omega g xi := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with xi
            rw [suzukiCanonicalHankelContourIntegrand,
              suzukiBoundaryLogHankelSymbol]
            simp only [smul_eq_mul, Real.inner_apply]
            have hMarg : -Complex.I * ((-2 * Real.pi * xi : ℝ) : ℂ) =
                (((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) := by
              apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
            rw [hMarg]
            have hexp : (((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) * (r : ℂ) =
                (((2 * Real.pi * xi * r : ℝ) : ℂ) * Complex.I) := by
              apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
            rw [hexp]
            ring
  have hne : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  apply (mul_left_cancel₀ hne)
  exact hboundaryInv.symm.trans hboundary

theorem memLp_two_suzukiLiteralLogHankel
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    MemLp (suzukiLiteralLogHankel omega g) 2 volume := by
  let hsymbol2 := memLp_two_suzukiBoundaryLogHankelSymbol hinner g
  let symbolL2 : SoninL2 := hsymbol2.toLp (suzukiBoundaryLogHankelSymbol omega g)
  have hsymbolL1 : Integrable (symbolL2 : ℝ → ℂ) :=
    (integrable_suzukiBoundaryLogHankelSymbol hinner g).congr hsymbol2.coeFn_toLp.symm
  have hinvAE := suzuki_l2_fourierInv_coeFn_eq_l1_fourierInv_of_integrable
    symbolL2 hsymbolL1
  have hpoint : (fun r => FourierTransform.fourierInv
      (suzukiBoundaryLogHankelSymbol omega g) r) =
      suzukiLiteralLogHankel omega g := by
    funext r
    exact fourierInv_suzukiBoundaryLogHankelSymbol_eq_literal
      homega hc hinner g hg r
  have hsymbolCoe : (symbolL2 : ℝ → ℂ) =ᵐ[volume]
      suzukiBoundaryLogHankelSymbol omega g := hsymbol2.coeFn_toLp
  have hinvCongr : (fun r => FourierTransform.fourierInv (symbolL2 : ℝ → ℂ) r) =
      fun r => FourierTransform.fourierInv (suzukiBoundaryLogHankelSymbol omega g) r := by
    funext r
    rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
    exact Real.fourier_congr_ae hsymbolCoe (-r)
  have houtAE : (fourierUnitary.symm symbolL2 : ℝ → ℂ) =ᵐ[volume]
      suzukiLiteralLogHankel omega g := by
    filter_upwards [hinvAE] with r hr
    rw [hr, congrFun hinvCongr r, congrFun hpoint r]
  have hmeas : AEStronglyMeasurable (suzukiLiteralLogHankel omega g) volume := by
    exact (Lp.aestronglyMeasurable (fourierUnitary.symm symbolL2)).congr houtAE
  exact (Lp.memLp (fourierUnitary.symm symbolL2)).congr_norm hmeas
    (houtAE.fun_comp fun z : ℂ => ‖z‖)

def suzukiStrongLogSchwartz (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) : SchwartzMap ℝ ℂ :=
  hg.toSchwartzMap g.property.smooth

def suzukiStrongLogL2 (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) : SoninL2 :=
  (suzukiStrongLogSchwartz g hg).toLp 2 volume

theorem suzukiStrongLogL2_ae (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    (suzukiStrongLogL2 g hg : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) := by
  exact (suzukiStrongLogSchwartz g hg).coeFn_toLp 2 volume

theorem fourier_suzukiStrongLog_eq_mellin
    (g : DeningerMeyerStrongLogTarget) (xi : ℝ) :
    FourierTransform.fourier (g : ℝ → ℂ) xi =
      deningerMeyerStrongLogMellin g
        (-Complex.I * ((2 * Real.pi * xi : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul, smul_eq_mul]
  congr 1
  congr 1
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

theorem suzukiShiftedFourier_logEven_symm (q : SoninL2) :
    suzukiShiftedFourierUnitary (logEvenUnitary.symm q) =
      spectralReflectionUnitary
        (dilationUnitary MellinL2.spectralNormalization
          MellinL2.spectralNormalization_pos (fourierUnitary q)) := by
  simp [suzukiShiftedFourierUnitary, archimedeanMellinUnitary,
    evenToMultiplicativeHaarUnitary, MellinL2.mellinUnitary,
    MellinL2.rawMellinUnitary, fourierUnitary]

def suzukiBoundaryLogHankelSymbolL2
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget) : SoninL2 :=
  (memLp_two_suzukiBoundaryLogHankelSymbol hinner g).toLp
    (suzukiBoundaryLogHankelSymbol omega g)

def suzukiLiteralLogHankelL2
    (omega c : ℝ) (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) : SoninL2 :=
  (memLp_two_suzukiLiteralLogHankel homega hc hinner g hg).toLp
    (suzukiLiteralLogHankel omega g)

theorem suzukiLiteralLogHankelL2_eq_fourierUnitary_symm_symbolL2
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    suzukiLiteralLogHankelL2 omega c homega hc hinner g hg =
      fourierUnitary.symm (suzukiBoundaryLogHankelSymbolL2 omega hinner g) := by
  apply Lp.ext
  let hsymbol2 := memLp_two_suzukiBoundaryLogHankelSymbol hinner g
  have hsymbolCoe :
      (suzukiBoundaryLogHankelSymbolL2 omega hinner g : ℝ → ℂ) =ᵐ[volume]
        suzukiBoundaryLogHankelSymbol omega g := hsymbol2.coeFn_toLp
  have hsymbolL1 : Integrable
      (suzukiBoundaryLogHankelSymbolL2 omega hinner g : ℝ → ℂ) :=
    (integrable_suzukiBoundaryLogHankelSymbol hinner g).congr hsymbolCoe.symm
  have hinvAE := suzuki_l2_fourierInv_coeFn_eq_l1_fourierInv_of_integrable
    (suzukiBoundaryLogHankelSymbolL2 omega hinner g) hsymbolL1
  have hliteralAE :
      (suzukiLiteralLogHankelL2 omega c homega hc hinner g hg : ℝ → ℂ) =ᵐ[volume]
        suzukiLiteralLogHankel omega g :=
    (memLp_two_suzukiLiteralLogHankel homega hc hinner g hg).coeFn_toLp
  filter_upwards [hliteralAE, hinvAE] with r hlit hinv
  rw [hlit, hinv]
  rw [← fourierInv_suzukiBoundaryLogHankelSymbol_eq_literal
    homega hc hinner g hg r,
    Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  exact (Real.fourier_congr_ae hsymbolCoe (-r)).symm

theorem suzuki_reflection_dilation_symbolL2_eq_theta_dilation_fourier
    {omega : ℝ} (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    spectralReflectionUnitary
        (dilationUnitary MellinL2.spectralNormalization
          MellinL2.spectralNormalization_pos
          (suzukiBoundaryLogHankelSymbolL2 omega hinner g)) =
      suzukiThetaBoundaryMulUnitary omega hinner
        (dilationUnitary MellinL2.spectralNormalization
          MellinL2.spectralNormalization_pos
          (fourierUnitary (suzukiStrongLogL2 g hg))) := by
  let a : ℝ := MellinL2.spectralNormalization
  have ha : 0 < a := MellinL2.spectralNormalization_pos
  have hsymbolCoe :
      (suzukiBoundaryLogHankelSymbolL2 omega hinner g : ℝ → ℂ) =ᵐ[volume]
        suzukiBoundaryLogHankelSymbol omega g :=
    (memLp_two_suzukiBoundaryLogHankelSymbol hinner g).coeFn_toLp
  have hsymbolScale := hsymbolCoe.comp_tendsto
    (realMul_quasiMeasurePreserving a ha.ne').tendsto_ae
  have hsymbolScaleNeg := hsymbolScale.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hleftReflection := spectralReflectionUnitary_ae
    (dilationUnitary a ha (suzukiBoundaryLogHankelSymbolL2 omega hinner g))
  have hleftDilation := (dilation_ae a ha
    (suzukiBoundaryLogHankelSymbolL2 omega hinner g)).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  let G : SchwartzMap ℝ ℂ := suzukiStrongLogSchwartz g hg
  have hFqEq : fourierUnitary (suzukiStrongLogL2 g hg) = (𝓕 G).toLp 2 volume := by
    exact SchwartzMap.toLp_fourier_eq G
  have hFqCoe : (fourierUnitary (suzukiStrongLogL2 g hg) : ℝ → ℂ) =ᵐ[volume]
      (𝓕 G : SchwartzMap ℝ ℂ) := by
    rw [hFqEq]
    exact (𝓕 G).coeFn_toLp 2 volume
  have hFqScale := hFqCoe.comp_tendsto
    (realMul_quasiMeasurePreserving a ha.ne').tendsto_ae
  have hrightDilation := dilation_ae a ha (fourierUnitary (suzukiStrongLogL2 g hg))
  have hrightMul := suzukiThetaBoundaryMulUnitary_ae omega hinner
    (dilationUnitary a ha (fourierUnitary (suzukiStrongLogL2 g hg)))
  apply Lp.ext
  filter_upwards [hleftReflection, hleftDilation, hsymbolScaleNeg,
    hrightMul, hrightDilation, hFqScale] with u hleft hleftD hsymbol hright hrightD hFq
  rw [hleft]
  change dilationUnitary a ha (suzukiBoundaryLogHankelSymbolL2 omega hinner g) (-u) = _
  rw [show dilationUnitary a ha (suzukiBoundaryLogHankelSymbolL2 omega hinner g) (-u) =
      (Real.sqrt a : ℂ) *
        suzukiBoundaryLogHankelSymbolL2 omega hinner g (a * -u) by
          rw [dilationUnitary_apply]
          simpa only [Function.comp_apply] using hleftD]
  rw [show suzukiBoundaryLogHankelSymbolL2 omega hinner g (a * -u) =
      suzukiBoundaryLogHankelSymbol omega g (a * -u) by
        simpa only [Function.comp_apply] using hsymbol]
  rw [hright]
  change (Real.sqrt a : ℂ) * suzukiBoundaryLogHankelSymbol omega g (a * -u) =
    suzukiCanonicalTheta omega (u : ℂ) *
      dilationUnitary a ha (fourierUnitary (suzukiStrongLogL2 g hg)) u
  rw [show dilationUnitary a ha (fourierUnitary (suzukiStrongLogL2 g hg)) u =
      (Real.sqrt a : ℂ) * fourierUnitary (suzukiStrongLogL2 g hg) (a * u) by
        rw [dilationUnitary_apply]
        simpa only [Function.comp_apply] using hrightD]
  rw [show fourierUnitary (suzukiStrongLogL2 g hg) (a * u) =
      (𝓕 G : SchwartzMap ℝ ℂ) (a * u) by
        simpa only [Function.comp_apply] using hFq]
  have hFG : (𝓕 G : SchwartzMap ℝ ℂ) (a * u) =
      deningerMeyerStrongLogMellin g
        (-Complex.I * ((2 * Real.pi * (a * u) : ℝ) : ℂ)) := by
    change FourierTransform.fourier (g : ℝ → ℂ) (a * u) = _
    exact fourier_suzukiStrongLog_eq_mellin g (a * u)
  rw [hFG, suzukiBoundaryLogHankelSymbol]
  have hscale : 2 * Real.pi * a = 1 := by
    dsimp only [a, MellinL2.spectralNormalization]
    field_simp [Real.pi_ne_zero]
  have hthetaArg : -2 * Real.pi * (a * -u) = u := by
    calc
      -2 * Real.pi * (a * -u) = (2 * Real.pi * a) * u := by ring
      _ = u := by rw [hscale, one_mul]
  have hleftMArg : ((2 * Real.pi * (a * -u) : ℝ) : ℂ) * Complex.I =
      -Complex.I * (u : ℂ) := by
    rw [← mul_assoc, hscale]
    push_cast
    ring
  have hrightMArg : -Complex.I * ((2 * Real.pi * (a * u) : ℝ) : ℂ) =
      -Complex.I * (u : ℂ) := by
    rw [← mul_assoc, hscale]
    norm_num
  rw [hthetaArg, hleftMArg, hrightMArg]
  ring

theorem suzukiCanonicalHankelUnitary_eq_literal_on_compact_smooth_log_core
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    suzukiCanonicalHankelUnitary omega hinner
        (logEvenUnitary.symm (suzukiStrongLogL2 g hg)) =
      logEvenUnitary.symm
        (suzukiLiteralLogHankelL2 omega c homega hc hinner g hg) := by
  apply suzukiShiftedFourierUnitary.injective
  rw [suzukiShiftedFourier_canonicalHankel,
    suzukiShiftedFourier_logEven_symm,
    suzukiShiftedFourier_logEven_symm]
  have hreflection (v : SuzukiSpectralL2) :
      spectralReflectionUnitary (spectralReflectionUnitary v) = v := by
    change l2Reflection (l2Reflection v) = v
    exact l2Reflection_involutive v
  rw [hreflection]
  have hFliteral :
      fourierUnitary (suzukiLiteralLogHankelL2 omega c homega hc hinner g hg) =
        suzukiBoundaryLogHankelSymbolL2 omega hinner g := by
    rw [suzukiLiteralLogHankelL2_eq_fourierUnitary_symm_symbolL2
      homega hc hinner g hg]
    exact fourierUnitary.apply_symm_apply _
  rw [hFliteral]
  exact (suzuki_reflection_dilation_symbolL2_eq_theta_dilation_fourier
    hinner g hg).symm

/-! ## Source-faithful `C_c^∞` formulation -/

/-- Every compactly supported smooth logarithmic test belongs to the all-exponential strong
target.  This removes the subtype-packaging assumption from the statement of Suzuki's test core. -/
theorem deningerMeyerStrongLogDecay_of_contDiff_hasCompactSupport
    {g : ℝ → ℂ} (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    DeningerMeyerStrongLogDecay g where
  smooth := hsmooth
  decayTop := by
    intro n a
    have hderivCompact : HasCompactSupport (iteratedDeriv n g) := by
      induction n with
      | zero => simpa only [iteratedDeriv_zero] using hcompact
      | succ n ih =>
          rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ]
          exact ih.deriv
    have heventCocompact : iteratedDeriv n g =ᶠ[cocompact ℝ] 0 := by
      rw [← Filter.coclosedCompact_eq_cocompact]
      exact hasCompactSupport_iff_eventuallyEq.mp hderivCompact
    have heventTop : iteratedDeriv n g =ᶠ[atTop] 0 :=
      heventCocompact.filter_mono atTop_le_cocompact
    apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [heventTop] with t ht
    change iteratedDeriv n g t = 0 at ht
    simp [ht]
  decayBot := by
    intro n b
    have hderivCompact : HasCompactSupport (iteratedDeriv n g) := by
      induction n with
      | zero => simpa only [iteratedDeriv_zero] using hcompact
      | succ n ih =>
          rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ]
          exact ih.deriv
    have heventCocompact : iteratedDeriv n g =ᶠ[cocompact ℝ] 0 := by
      rw [← Filter.coclosedCompact_eq_cocompact]
      exact hasCompactSupport_iff_eventuallyEq.mp hderivCompact
    have heventBot : iteratedDeriv n g =ᶠ[atBot] 0 :=
      heventCocompact.filter_mono atBot_le_cocompact
    apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [heventBot] with t ht
    change iteratedDeriv n g t = 0 at ht
    simp [ht]

/-- Arbitrary `C_c^∞(ℝ)` source packaged in the exact strong logarithmic target. -/
def suzukiCompactSmoothStrongLogTarget
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) : DeningerMeyerStrongLogTarget :=
  ⟨g, deningerMeyerStrongLogDecay_of_contDiff_hasCompactSupport hsmooth hcompact⟩

/-- `L²(dt)` class of an arbitrary compactly supported smooth logarithmic source. -/
def suzukiCompactSmoothLogL2
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) : SoninL2 :=
  suzukiStrongLogL2
    (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact

/-- Literal logarithmic Hankel output for an arbitrary compactly supported smooth source. -/
def suzukiCompactSmoothLiteralLogHankelL2
    (omega c : ℝ) (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) : SoninL2 :=
  suzukiLiteralLogHankelL2 omega c homega hc hinner
    (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact

/-- **Suzuki (2012), Lemma 4.1, literal-kernel identification on `C_c^∞`.**
The spectral unitary is exactly the `L²` extension of the literal `h_ω(xy)` integral after the
unitary logarithmic half-density coordinate change. -/
theorem suzuki2012_lemma_four_one_literal_kernel_on_compact_smooth_log_core
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    suzukiCanonicalHankelUnitary omega hinner
        (logEvenUnitary.symm (suzukiCompactSmoothLogL2 g hsmooth hcompact)) =
      logEvenUnitary.symm
        (suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
          g hsmooth hcompact) := by
  exact suzukiCanonicalHankelUnitary_eq_literal_on_compact_smooth_log_core
    homega hc hinner
      (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact

/-- Source vector on Suzuki's literal `L²((0,∞),dx)` carrier corresponding to a logarithmic
compact-smooth half-density. -/
def suzukiCompactSmoothPositiveL2
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) : SuzukiPositiveL2 :=
  suzukiPositiveHalfLineUnitary
    (logEvenUnitary.symm (suzukiCompactSmoothLogL2 g hsmooth hcompact))

/-- Literal output vector on Suzuki's positive-half-line carrier. -/
def suzukiCompactSmoothLiteralPositiveHankelL2
    (omega c : ℝ) (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) : SuzukiPositiveL2 :=
  suzukiPositiveHalfLineUnitary
    (logEvenUnitary.symm
      (suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
        g hsmooth hcompact))

/-- **Suzuki (2012), Lemma 4.1 on the literal positive-half-line carrier.** -/
theorem suzuki2012_lemma_four_one_positive_half_line_literal_kernel
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    suzukiCanonicalPositiveHankelUnitary omega hinner
        (suzukiCompactSmoothPositiveL2 g hsmooth hcompact) =
      suzukiCompactSmoothLiteralPositiveHankelL2 omega c homega hc hinner
        g hsmooth hcompact := by
  simp only [suzukiCompactSmoothPositiveL2,
    suzukiCompactSmoothLiteralPositiveHankelL2]
  change suzukiPositiveHalfLineUnitary
      (suzukiCanonicalHankelUnitary omega hinner
        (logEvenUnitary.symm (suzukiCompactSmoothLogL2 g hsmooth hcompact))) = _
  rw [suzuki2012_lemma_four_one_literal_kernel_on_compact_smooth_log_core
    homega hc hinner g hsmooth hcompact]
  rfl

end
end RHTower
