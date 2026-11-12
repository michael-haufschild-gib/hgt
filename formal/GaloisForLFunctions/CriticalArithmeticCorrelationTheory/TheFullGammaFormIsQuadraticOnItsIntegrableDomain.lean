import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.RHTower.TiltedWeilNyquistInertia

/-!
# Polarization of the full Gamma integral

Finite diagonal Gamma integrals control the mixed integral by the elementary
inequality `2|Re(z conj w)| ≤ |z|² + |w|²`. Thus the actual integrable domain
is closed under real variations, and its full form is a quadratic polynomial.
-/

noncomputable section
open MeasureTheory Filter Topology Zeta23 Complex
open _root_.RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

/-- The real scalar product of the two literal paper Fourier transforms. -/
def gammaFourierPair (f g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (paperFT (cx f) r).re * (paperFT (cx g) r).re +
    (paperFT (cx f) r).im * (paperFT (cx g) r).im

/-- The mixed full Gamma form in the paper's Fourier normalization. -/
def gammaMixedForm (f g : ℝ → ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r, gammaFourierPair f g r * EF.gammaBracket r

private theorem abs_gammaFourierPair_le (f g : ℝ → ℝ) (r : ℝ) :
    |gammaFourierPair f g r| ≤
      (‖paperFT (cx f) r‖ ^ 2 + ‖paperFT (cx g) r‖ ^ 2) / 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  dsimp only [gammaFourierPair]
  apply abs_le.mpr
  constructor
  · nlinarith only [sq_nonneg ((paperFT (cx f) r).re + (paperFT (cx g) r).re),
      sq_nonneg ((paperFT (cx f) r).im + (paperFT (cx g) r).im)]
  · nlinarith only [sq_nonneg ((paperFT (cx f) r).re - (paperFT (cx g) r).re),
      sq_nonneg ((paperFT (cx f) r).im - (paperFT (cx g) r).im)]

/-- Finite diagonal energies pay the full mixed Gamma integral. -/
theorem integrable_gammaFourierPair {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hγf : Integrable (fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r))
    (hγg : Integrable (fun r : ℝ => ‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r)) :
    Integrable (fun r => gammaFourierPair f g r * EF.gammaBracket r) := by
  have hfc := continuous_paperFT_cx hf
  have hgc := continuous_paperFT_cx hg
  have hpc : Continuous (gammaFourierPair f g) :=
    (hfc.re.mul hgc.re).add (hfc.im.mul hgc.im)
  apply ((hγf.norm.add hγg.norm).div_const 2).mono'
    (hpc.mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
  refine Eventually.of_forall fun r => ?_
  change ‖gammaFourierPair f g r * EF.gammaBracket r‖ ≤
    (‖‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r‖ +
      ‖‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r‖) / 2
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg (‖paperFT (cx f) r‖)),
    abs_of_nonneg (sq_nonneg (‖paperFT (cx g) r‖))]
  calc
    _ ≤ ((‖paperFT (cx f) r‖ ^ 2 + ‖paperFT (cx g) r‖ ^ 2) / 2) * |EF.gammaBracket r| :=
      mul_le_mul_of_nonneg_right (abs_gammaFourierPair_le f g r) (abs_nonneg _)
    _ = _ := by ring

/-- Real variations commute with the paper Fourier transform on its L¹ domain. -/
theorem paperFT_cx_add_const_mul {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (c r : ℝ) :
    paperFT (cx fun t => f t + c * g t) r =
      paperFT (cx f) r + (c : ℂ) * paperFT (cx g) r := by
  have h := _root_.RHTower.WeilSpectral.paperFT_add_smul_real
    (hf.ofReal (𝕜 := ℂ)) (hg.ofReal (𝕜 := ℂ)) (c : ℂ) r
  convert h using 1
  congr 1
  funext t
  simp only [cx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_mul]

private theorem gamma_variation_identity {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (c r : ℝ) :
    ‖paperFT (cx fun t => f t + c * g t) r‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r +
      (2 * c) * (gammaFourierPair f g r * EF.gammaBracket r) +
      c ^ 2 * (‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r) := by
  rw [paperFT_cx_add_const_mul hf hg]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add, sub_zero, gammaFourierPair]
  ring

/-- The finite Gamma domain is stable under every real affine variation. -/
theorem integrable_gamma_add_const_mul {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hγf : Integrable (fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r))
    (hγg : Integrable (fun r : ℝ => ‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r)) (c : ℝ) :
    Integrable (fun r : ℝ => ‖paperFT (cx fun t => f t + c * g t) r‖ ^ 2 * EF.gammaBracket r) := by
  have hm := integrable_gammaFourierPair hf hg hγf hγg
  apply ((hγf.add (hm.const_mul (2 * c))).add (hγg.const_mul (c ^ 2))).congr
  exact Eventually.of_forall fun r => (gamma_variation_identity hf hg c r).symm

/-- The actual full Gamma form is quadratic on its integrable domain. -/
theorem archForm_add_const_mul_of_integrable {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hγf : Integrable (fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r))
    (hγg : Integrable (fun r : ℝ => ‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r)) (c : ℝ) :
    archForm (fun t => f t + c * g t) =
      archForm f + 2 * c * gammaMixedForm f g + c ^ 2 * archForm g := by
  have hm := integrable_gammaFourierPair hf hg hγf hγg
  change (1 / (2 * Real.pi)) *
    (∫ r : ℝ, ‖paperFT (cx fun t => f t + c * g t) r‖ ^ 2 * EF.gammaBracket r) =
      (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r) +
      2 * c * ((1 / (2 * Real.pi)) * (∫ r, gammaFourierPair f g r * EF.gammaBracket r)) +
      c ^ 2 * ((1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r))
  simp_rw [gamma_variation_identity hf hg]
  rw [integral_add (hγf.add (hm.const_mul (2 * c))) (hγg.const_mul (c ^ 2)),
    integral_add hγf (hm.const_mul (2 * c)), integral_const_mul, integral_const_mul]
  ring

/-- Scaling of the literal Gamma integral requires no smoothness hypothesis. -/
theorem archForm_const_mul_unrestricted (f : ℝ → ℝ) (c : ℝ) :
    archForm (fun t => c * f t) = c ^ 2 * archForm f := by
  have hft (r : ℝ) : paperFT (cx fun t => c * f t) r =
      (c : ℂ) * paperFT (cx f) r := by
    rw [show (cx fun t => c * f t) = (fun t => (c : ℂ) * cx f t) from
      funext fun t => by simp only [cx, Complex.ofReal_mul],
      _root_.RHTower.paperFT_const_mul]
  have he (r : ℝ) : ‖paperFT (cx fun t => c * f t) r‖ ^ 2 * EF.gammaBracket r =
      c ^ 2 * (‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r) := by
    rw [hft, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  change (1 / (2 * Real.pi)) *
    (∫ r : ℝ, ‖paperFT (cx fun t => c * f t) r‖ ^ 2 * EF.gammaBracket r) =
      c ^ 2 * ((1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r))
  simp_rw [he]
  rw [integral_const_mul]
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
