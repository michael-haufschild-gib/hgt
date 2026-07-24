import GaloisForLFunctions.RHTower.XiWardEdgeMassQuantization
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyContraction

/-!
# Infinitesimal Julia-defect index quantization

The strict-right Xi phase is an unconditional Schur family for nonnegative
aperture.  This file identifies the exact first variation of its Julia defect.
If

`V_w(a) = 1 - Phi_w(a)`,

then

`1 - |Phi_w(a)|² = 2 Re V_w(a) - |V_w(a)|²`.

Since `V_w(0)=0` and `V'_w(0)=r(w)`, the infinitesimal defect density is
`2 Re r(w)`.  On the Euler edge each strict-right Schwarz pair therefore
carries the universal charge `8π`.  This is a genuine index law: height and
transverse displacement change the shape of the defect profile but not its
total charge.
-/

open Complex Filter MeasureTheory Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Julia defect of the strict-right boundary phase along the real aperture
ray. -/
def xiWardBoundaryPhaseDefect (w : ℂ) (a : ℝ) : ℝ :=
  1 - Complex.normSq
    (xiRightWardBoundarySourcePhaseCrossRatio (I * w) (a : ℂ))

/-- The transported defect vanishes at aperture zero. -/
theorem mobiusGammaXiAntiCausalWardTransportV_zero
    {w : ℂ} (hw : 0 < w.re) :
    mobiusGammaXiAntiCausalWardTransportV w 0 = 0 := by
  have hproduct : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ :=
      (xiRightCanonicalProduct_eq_zero_iff_exists (I * w)).mp hzero
    have hright := q.2
    change xiSpectralPoint q.1 = I * w at hq
    rw [hq] at hright
    have hIIw : I * (I * w) = -w := by
      rw [← mul_assoc, I_mul_I, neg_one_mul]
    rw [hIIw] at hright
    simp only [neg_re] at hright
    linarith
  rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw]
  simp [xiRightWardBoundarySourcePhaseCrossRatio,
    xiRightWardSourcePhase_zero hproduct]

/-- Exact Cayley polarization identity for the phase defect. -/
theorem xiWardBoundaryPhaseDefect_eq_transport
    {w : ℂ} (hw : 0 < w.re) (a : ℝ) :
    xiWardBoundaryPhaseDefect w a =
      2 * (mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)).re -
        Complex.normSq
          (mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)) := by
  let V := mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)
  have hV :
      V =
        1 - xiRightWardBoundarySourcePhaseCrossRatio
          (I * w) (a : ℂ) :=
    mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw _
  have hphase :
      xiRightWardBoundarySourcePhaseCrossRatio (I * w) (a : ℂ) =
        1 - V := by
    rw [hV]
    ring
  rw [xiWardBoundaryPhaseDefect, hphase]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im]
  ring

/-- Schur contractivity makes the finite-aperture phase defect nonnegative. -/
theorem xiWardBoundaryPhaseDefect_nonneg
    {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ xiWardBoundaryPhaseDefect w a := by
  have hnorm :=
    norm_xiRightWardBoundarySourcePhaseCrossRatio_le_one hw ha
  rw [xiWardBoundaryPhaseDefect, ← Complex.sq_norm]
  nlinarith [norm_nonneg
    (xiRightWardBoundarySourcePhaseCrossRatio (I * w) (a : ℂ))]

private theorem hasDerivAt_realAperture_of_complex_zero
    {f : ℂ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun x : ℝ => f x) f' 0 := by
  have houter : HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      (Complex.ofRealCLM 0) := by
    simpa using h.hasFDerivAt.restrictScalars ℝ
  have hcomp := houter.comp (0 : ℝ) Complex.ofRealCLM.hasFDerivAt
  show HasFDerivAt (fun x : ℝ => f x)
    (ContinuousLinearMap.toSpanSingleton ℝ f') 0
  convert hcomp using 1

/-- **Infinitesimal Julia-defect law.**  The aperture derivative of the
phase defect is exactly twice the real Ward response. -/
theorem hasDerivAt_xiWardBoundaryPhaseDefect_zero
    {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (xiWardBoundaryPhaseDefect w)
      (2 * (continuedXiAntiCausalWardResponse w).re) 0 := by
  let V : ℝ → ℂ :=
    fun a => mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)
  have hV : HasDerivAt V (continuedXiAntiCausalWardResponse w) 0 :=
    hasDerivAt_realAperture_of_complex_zero
      (hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw)
  have hV0 : V 0 = 0 := by
    exact mobiusGammaXiAntiCausalWardTransportV_zero hw
  have hre : HasDerivAt (fun a : ℝ => (V a).re)
      (continuedXiAntiCausalWardResponse w).re 0 := by
    simpa only [Function.comp_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hV
  have hnorm :
      HasDerivAt (fun a : ℝ => Complex.normSq (V a)) 0 0 := by
    have hre' := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hV
    have him' := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hV
    have h := (hre'.mul hre').add (him'.mul him')
    rw [show (fun a : ℝ => Complex.normSq (V a)) =
        (fun a : ℝ =>
          (V a).re * (V a).re + (V a).im * (V a).im) by
      funext a
      rw [Complex.normSq_apply]]
    convert h using 1
    simp [hV0]
  have hcalc := (hre.const_mul 2).sub hnorm
  rw [show xiWardBoundaryPhaseDefect w =
      fun a : ℝ =>
        2 * (V a).re - Complex.normSq (V a) by
    funext a
    exact xiWardBoundaryPhaseDefect_eq_transport hw a]
  convert hcalc using 1
  ring

/-- Pointwise Euler-edge density of the infinitesimal Julia defect. -/
def xiWardInfinitesimalDefectDensity (t : ℝ) : ℝ :=
  2 * (continuedXiAntiCausalWardResponse
    ((1 / 2 : ℂ) + I * (t : ℂ))).re

/-- On the Euler edge the derivative of the Julia defect is the declared
nonnegative defect density. -/
theorem hasDerivAt_xiWardBoundaryPhaseDefect_eulerEdge_zero
    (t : ℝ) :
    HasDerivAt
      (xiWardBoundaryPhaseDefect
        ((1 / 2 : ℂ) + I * (t : ℂ)))
      (xiWardInfinitesimalDefectDensity t) 0 := by
  apply hasDerivAt_xiWardBoundaryPhaseDefect_zero
  norm_num [Complex.add_re, Complex.mul_re]

/-- One strict-right Schwarz pair carries exactly `8π` of infinitesimal
Julia-defect mass on the Euler edge. -/
theorem lintegral_infinitesimalDefect_xiAntiCausalWardSchwarzPair_eulerEdge
    (q : XiRightUpperZeroCopy) :
    ∫⁻ t : ℝ, ENNReal.ofReal
        (2 * (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ENNReal.ofReal (8 * π) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal
      ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) :=
    ENNReal.continuous_ofReal.comp
      (re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous q)
      |>.measurable
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [MeasureTheory.lintegral_const_mul _ hmeas,
    lintegral_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge]
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have h4 : ENNReal.ofReal (4 : ℝ) = 4 := by norm_num
  have h8 : ENNReal.ofReal (8 : ℝ) = 8 := by norm_num
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    h2, h4, h8]
  ring

/-- **Infinitesimal defect index theorem.**  Total Euler-edge Julia-defect
mass is quantized in universal packets of `8π`, one for each strict-right
upper Schwarz pair. -/
theorem lintegral_xiWardInfinitesimalDefectDensity :
    ∫⁻ t : ℝ, ENNReal.ofReal (xiWardInfinitesimalDefectDensity t) =
      ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (8 * π) := by
  rw [show (∫⁻ t : ℝ,
      ENNReal.ofReal (xiWardInfinitesimalDefectDensity t)) =
      2 * ∑' _ : XiRightUpperZeroCopy,
        ENNReal.ofReal (4 * π) by
    simp_rw [xiWardInfinitesimalDefectDensity,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
      lintegral_re_continuedXiAntiCausalWardResponse_eulerEdge]]
  have hterm :
      ENNReal.ofReal (8 * π) =
        2 * ENNReal.ofReal (4 * π) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have h4 : ENNReal.ofReal (4 : ℝ) = 4 := by norm_num
    have h8 : ENNReal.ofReal (8 : ℝ) = 8 := by norm_num
    rw [h4, h8]
    ring
  rw [show (fun _ : XiRightUpperZeroCopy =>
      ENNReal.ofReal (8 * π)) =
      (fun _ : XiRightUpperZeroCopy =>
        2 * ENNReal.ofReal (4 * π)) by
    funext q
    exact hterm]
  rw [ENNReal.tsum_mul_left]

end

end RHTower
