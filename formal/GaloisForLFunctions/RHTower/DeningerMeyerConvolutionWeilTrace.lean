import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionTraceClass
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma41
import GaloisForLFunctions.RHTower.DeningerMeyerCausalConjugation
import Zeta23.WeilEF.Main

/-! # Whole-line operator traces and the complete arithmetic Weil functional

Centering a literal compact source transports its full-Jordan convolution
trace to the unconditional explicit formula. The test may cross time zero;
the archimedean term and both polar terms are retained.
-/

noncomputable section
open Complex MeasureTheory Set Zeta23 ContinuousLinearMap

namespace RHTower

def deningerWeilConvolutionSource {a : ℝ} (k : SuzukiSmoothCompactTest a) :
    DeningerMeyerStrongLogTarget :=
  ⟨fun t => Complex.exp (-(t : ℂ)/2) * k t,
    deningerMeyerStrongLogDecay_of_contDiff_hasCompactSupport
      ((Complex.ofRealCLM.contDiff.neg.div_const (2 : ℂ)).cexp.mul k.smooth)
      k.hasCompactSupport.mul_left⟩

theorem deningerWeilConvolutionSource_mellin {a : ℝ} (k : SuzukiSmoothCompactTest a) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerWeilConvolutionSource k) s =
      paperFT k (-I*(s-1/2)) := by
  apply integral_congr_ae
  filter_upwards with t
  change (t : ℂ)^0 * Complex.exp (s*t) * (Complex.exp (-(t : ℂ)/2)*k t) =
    k t * Complex.exp (I*(-I*(s-1/2))*t)
  have he : I*(-I*(s-1/2)) = s-1/2 := by ring_nf; rw [I_sq]; ring
  rw [pow_zero, one_mul, he]
  calc Complex.exp (s*t) * (Complex.exp (-(t : ℂ)/2)*k t) =
      k t * (Complex.exp (s*t)*Complex.exp (-(t : ℂ)/2)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

private theorem trace_copies_carrier (g : DeningerMeyerStrongLogTarget) :
    (∑' q : XiZeroCopy, deningerMeyerStrongLogMellin g (q.1 : ℂ)) =
      ∑' rho : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult rho : ℂ)*deningerMeyerStrongLogMellin g (rho : ℂ) := by
  rw [(deningerMeyerHilbertConvolution_summable_diagonal g).tsum_sigma,
    ← xiDivisorZetaCarrierEquiv.tsum_eq
      (fun rho => (zetaZeroConfig.mult rho : ℂ)*deningerMeyerStrongLogMellin g (rho : ℂ))]
  apply tsum_congr
  intro rho
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

/-- Ordinary trace of the actual source operator equals the full arithmetic functional. -/
theorem deningerWeilConvolutionSource_opTrace {a : ℝ} (k : SuzukiSmoothCompactTest a) :
    opTrace (deningerMeyerHilbertConvolution (deningerWeilConvolutionSource k)) =
      EF.literatureRHS k := by
  rw [deningerMeyerHilbertConvolution_opTrace, trace_copies_carrier]
  have he (rho : zetaZeroConfig.carrier) :
      deningerMeyerStrongLogMellin (deningerWeilConvolutionSource k) (rho : ℂ) =
        paperFT k (gammaOf rho) := by
    rw [deningerWeilConvolutionSource_mellin]
    congr 1
    simp only [gammaOf, div_eq_mul_inv, Complex.inv_I]
    ring
  simp_rw [he]
  exact (WeilEF.EF_lit_zetaZeroConfig k
    (k.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) k.hasCompactSupport).2

/-- The two endpoint terms, every prime power, and the complete Gamma integral appear together. -/
theorem deningerWeilConvolutionSource_full_formula {a : ℝ} (k : SuzukiSmoothCompactTest a) :
    opTrace (deningerMeyerHilbertConvolution (deningerWeilConvolutionSource k)) =
      paperFT k (I/2) + paperFT k (-I/2) -
        (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n))) +
        (1/(2*Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) :=
  deningerWeilConvolutionSource_opTrace k

/-- The arithmetic Hermitian reflection on original sources. -/
def deningerMeyerSourceSharp (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget := deningerMeyerStrongLogJ (deningerMeyerStrongLogConj g)

theorem deningerMeyerSourceSharp_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceSharp g) s =
      star (deningerMeyerStrongLogMellin g (star (1-s))) := by
  rw [deningerMeyerSourceSharp, deningerMeyerStrongLogMellin_J, deningerMeyerStrongLogMellin_conj]

/-- The full Weil pairing is an ordinary composition trace of actual source convolutions. -/
theorem deningerWeilConvolutionSource_pair_trace {a : ℝ} (k h : SuzukiSmoothCompactTest a) :
    opTrace ((deningerMeyerHilbertConvolution (deningerWeilConvolutionSource k)).comp
      (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp (deningerWeilConvolutionSource h)))) =
        zetaZeroConfig.W k h := by
  rw [← deningerMeyerHilbertConvolution_mul, deningerMeyerHilbertConvolution_opTrace,
    trace_copies_carrier, ZeroConfig.W]
  apply tsum_congr
  intro rho
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin,
    deningerWeilConvolutionSource_mellin, deningerWeilConvolutionSource_mellin]
  have he : -I*((rho : ℂ)-1/2) = gammaOf rho := by
    simp only [gammaOf, div_eq_mul_inv, Complex.inv_I]; ring
  have hc : -I*(star (1-(rho : ℂ))-1/2) = star (gammaOf rho) := by
    change -I*((starRingEnd ℂ) (1-(rho : ℂ))-1/2) = (starRingEnd ℂ) (gammaOf rho)
    simp only [gammaOf, div_eq_mul_inv, Complex.inv_I, map_mul, map_sub, map_one,
      map_inv₀, map_ofNat, map_neg, Complex.conj_I]
    ring
  rw [he, hc]
  simp only [ZeroConfig.Wsummand, mul_assoc]
  rfl

theorem deningerWeilConvolutionSource_pair_full_arithmetic {a : ℝ}
    (k h : SuzukiSmoothCompactTest a) :
    opTrace ((deningerMeyerHilbertConvolution (deningerWeilConvolutionSource k)).comp
      (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp (deningerWeilConvolutionSource h)))) =
        EF.literatureRHS (EF.weilTest k h) := by
  rw [deningerWeilConvolutionSource_pair_trace, ZeroConfig.W]
  have he := (WeilEF.EF_lit_zetaZeroConfig (EF.weilTest k h)
    (EF.weilTest_contDiff (k.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      h.continuous k.hasCompactSupport)
    (EF.weilTest_hasCompactSupport k.hasCompactSupport h.hasCompactSupport)).2
  rw [← he]
  apply tsum_congr
  intro rho
  rw [EF.paperFT_weilTest k.continuous h.continuous k.hasCompactSupport h.hasCompactSupport]
  simp only [ZeroConfig.Wsummand, mul_assoc]

/-- The actual mixed CCM form has the same full-Jordan source-operator realization. -/
theorem deningerWeilConvolutionSource_ccm_trace {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    opTrace ((deningerMeyerHilbertConvolution
      (deningerWeilConvolutionSource v.toSuzukiSmoothCompactTest)).comp
        (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp
          (deningerWeilConvolutionSource u.toSuzukiSmoothCompactTest)))) =
      ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector := by
  rw [deningerWeilConvolutionSource_pair_trace, ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil]
  rfl

/- Arithmetic sharp above is not asserted to be the Hilbert adjoint. -/

end RHTower
