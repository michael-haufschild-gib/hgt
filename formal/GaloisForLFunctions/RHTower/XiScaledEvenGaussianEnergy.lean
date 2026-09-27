import GaloisForLFunctions.RHTower.XiGaussianHeatTraceDisproof
import GaloisForLFunctions.HTGeometry.ComplexGaussianPolynomialTranslation

/-!
# Full complex Gaussian energy of actual scaled Xi coordinates

The even polynomial Gaussian is evaluated at every complex spectral point,
with analytic multiplicity. Its square is an existing actual polynomial heat
term, so absolute convergence follows at every positive scale without RH.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The entire even polynomial Gaussian evaluated at an actual complex Xi coordinate. -/
def xiScaledEvenGaussianAmplitude (P : Polynomial ℝ) (r : {r : ℝ // 0 < r})
    (q : XiZeroCopy) : ℂ :=
  (evenSquarePolynomial P).eval₂ (algebraMap ℝ ℂ) ((r : ℝ) * xiSpectralPoint q) *
    Complex.exp (-(π : ℂ) * ((r : ℝ) * xiSpectralPoint q) ^ 2)

/-- The exact full positive norm energy, including all divisor copies. -/
def xiScaledEvenGaussianEnergy (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiScaledEvenGaussianAmplitude P r q‖ ^ 2

/-- Squaring the complete amplitude gives the literal existing polynomial Gaussian heat term. -/
theorem xiScaledEvenGaussianAmplitude_sq (P : Polynomial ℝ) (r : {r : ℝ // 0 < r})
    (q : XiZeroCopy) :
    xiScaledEvenGaussianAmplitude P r q ^ 2 =
      xiPolynomialGaussianHeatTerm (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (2 * π * (r : ℝ) ^ 2) q := by
  have heval : (evenSquarePolynomial P).eval₂ (algebraMap ℝ ℂ)
      ((r : ℝ) * xiSpectralPoint q) =
      evalRealPolynomial (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (xiSpectralPoint q ^ 2) := by
    rw [evenSquarePolynomial, evalRealPolynomial, Polynomial.eval_map,
      Polynomial.eval₂_comp, Polynomial.eval₂_comp]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, coe_algebraMap, Complex.ofReal_pow, mul_pow]
  rw [xiScaledEvenGaussianAmplitude, heval, mul_pow,
    xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm]
  congr 1
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The full energy series converges absolutely at every positive scale. -/
theorem summable_xiScaledEvenGaussianAmplitude_norm_sq (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : XiZeroCopy => ‖xiScaledEvenGaussianAmplitude P r q‖ ^ 2) := by
  have h := (summable_xiPolynomialGaussianHeatTerm
    (show 0 < 2 * π * (r : ℝ) ^ 2 from
      mul_pos (mul_pos (by positivity) Real.pi_pos) (pow_pos r.property 2))
    (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))).norm
  apply h.congr
  intro q
  rw [← xiScaledEvenGaussianAmplitude_sq, norm_pow]

/-- Nonnegativity of the complete norm energy needs no spectral reality assumption. -/
theorem xiScaledEvenGaussianEnergy_nonneg (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}) :
    0 ≤ xiScaledEvenGaussianEnergy P r := tsum_nonneg fun _ => sq_nonneg _

/-- Real and imaginary scaled coordinates give the exact same entire amplitude. -/
theorem xiScaledEvenGaussianAmplitude_vertical (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    xiScaledEvenGaussianAmplitude P r q =
      (evenSquarePolynomial P).eval₂ (algebraMap ℝ ℂ)
        ((((r : ℝ) * (xiSpectralPoint q).re : ℝ) : ℂ) +
          (((r : ℝ) * (xiSpectralPoint q).im : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(π : ℂ) *
          ((((r : ℝ) * (xiSpectralPoint q).re : ℝ) : ℂ) +
            (((r : ℝ) * (xiSpectralPoint q).im : ℝ) : ℂ) * Complex.I) ^ 2) := by
  have hz : ((r : ℝ) : ℂ) * xiSpectralPoint q =
      ((((r : ℝ) * (xiSpectralPoint q).re : ℝ) : ℂ) +
        (((r : ℝ) * (xiSpectralPoint q).im : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [xiScaledEvenGaussianAmplitude, hz]

end RHTower
