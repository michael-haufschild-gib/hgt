import GaloisForLFunctions.RHTower.OneDimensionalPowerSeriesPolynomial
import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicSublinearGate

/-!
# The oriented finite-coefficient current of a Xi Taylor polynomial

The imaginary logarithmic derivative of a polynomial is its oriented Hermitian coefficient
current divided by the squared modulus of its value.  Clearing this positive denominator gives an
exact finite coefficient inequality that implies the anisotropic sublinear-flux condition.

This module is an algebraic normal form for the open source theorem.  It does not prove that the
canonical Xi coefficients satisfy the current inequality.
-/

open Complex Filter Polynomial

namespace RHTower

noncomputable section

/-- The orientation-sensitive Hermitian current of a complex polynomial at one point. -/
def orientedPolynomialCurrent (P : Polynomial ℂ) (z : ℂ) : ℝ :=
  (P.derivative.eval z * (starRingEnd ℂ) (P.eval z)).im

/-- The imaginary logarithmic derivative is the oriented polynomial current divided by the
squared modulus. -/
theorem polynomial_logDeriv_im_eq_orientedCurrent_div_normSq
    (P : Polynomial ℂ) (z : ℂ) :
    (logDeriv (fun w : ℂ => P.eval w) z).im =
      orientedPolynomialCurrent P z / Complex.normSq (P.eval z) := by
  rw [logDeriv_apply, (P.hasDerivAt z).deriv]
  rw [Complex.div_im]
  unfold orientedPolynomialCurrent
  rw [mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A strict denominator-cleared current bound forces the corresponding logarithmic-derivative
bound and automatically excludes a zero at the evaluation point. -/
theorem polynomial_logDeriv_im_lt_of_orientedCurrent_lt
    (P : Polynomial ℂ) (z : ℂ) {B : ℝ}
    (hcurrent : orientedPolynomialCurrent P z < B * Complex.normSq (P.eval z)) :
    P.eval z ≠ 0 ∧ (logDeriv (fun w : ℂ => P.eval w) z).im < B := by
  have hz : P.eval z ≠ 0 := by
    intro hz
    simp [orientedPolynomialCurrent, hz] at hcurrent
  refine ⟨hz, ?_⟩
  rw [polynomial_logDeriv_im_eq_orientedCurrent_div_normSq P z]
  exact (div_lt_iff₀ (Complex.normSq_pos.mpr hz)).mpr hcurrent

/-- The ordinary polynomial whose coefficients are the first `n` one-dimensional Cauchy--Taylor
coefficients of `XiC`. -/
def xiCTaylorPolynomial (n : ℕ) : Polynomial ℂ :=
  fmlsPolynomial (cauchyPowerSeries XiC 0 1) n

theorem xiCTaylorPolynomial_eval (n : ℕ) (z : ℂ) :
    (xiCTaylorPolynomial n).eval z = xiCTaylorApprox n z := by
  exact fmlsPolynomial_eval (cauchyPowerSeries XiC 0 1) n z

theorem xiCTaylorPolynomial_derivative_eval (n : ℕ) (z : ℂ) :
    (xiCTaylorPolynomial n).derivative.eval z = deriv (xiCTaylorApprox n) z := by
  have hfun : (fun w : ℂ => (xiCTaylorPolynomial n).eval w) = xiCTaylorApprox n := by
    funext w
    exact xiCTaylorPolynomial_eval n w
  rw [← hfun]
  exact ((xiCTaylorPolynomial n).hasDerivAt z).deriv.symm

/-- The oriented current of the finite Xi Taylor polynomial is exactly the denominator-cleared
imaginary logarithmic derivative of the canonical Taylor approximant. -/
theorem xiCTaylor_orientedCurrent_eq
    (n : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorPolynomial n) z =
      (deriv (xiCTaylorApprox n) z *
        (starRingEnd ℂ) (xiCTaylorApprox n z)).im := by
  simp only [orientedPolynomialCurrent, xiCTaylorPolynomial_eval,
    xiCTaylorPolynomial_derivative_eval]

/-- Source-facing finite coefficient condition.  At every left-strip anisotropic mesh point, the
oriented current of the actual finite Xi Taylor polynomial is eventually smaller than every
positive linear rate times its squared value. -/
def XiCTaylorAnisotropicOrientedCoefficientSublinearUpper (N : ℕ → ℕ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        orientedPolynomialCurrent
            (xiCTaylorPolynomial (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (N (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n))

/-- The denominator-cleared oriented coefficient inequality forces sublinear upper flux for the
canonical finite Xi Taylor logarithmic derivatives. -/
theorem xiCTaylorAnisotropicLogDerivSublinearUpper_of_orientedCoefficient
    {N : ℕ → ℕ}
    (hcoeff : XiCTaylorAnisotropicOrientedCoefficientSublinearUpper N) :
    XiCTaylorAnisotropicLogDerivSublinearUpper N := by
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  have hcurrent := hcoeff sigma hsigmaPos hsigmaHalf epsilon hepsilon
  filter_upwards [hcurrent] with n hn
  let P : Polynomial ℂ :=
    xiCTaylorPolynomial (N (xiCTaylorAnisotropicScheduleStage sigma n))
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  have hflux := polynomial_logDeriv_im_lt_of_orientedCurrent_lt P z hn
  have hq : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hfun : (fun w : ℂ => P.eval w) =
      xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)) := by
    funext w
    exact xiCTaylorPolynomial_eval _ w
  change (logDeriv
      (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n))) z).im /
      ((n + 1 : ℕ) : ℝ) < epsilon
  rw [← hfun]
  rw [div_lt_iff₀ hq]
  simpa only [mul_comm] using hflux.2

/-- A super-accurate schedule satisfying the finite oriented coefficient inequality proves RH. -/
theorem riemannHypothesis_of_xiCTaylorAnisotropicOrientedCoefficientSublinearUpper
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (hcoeff : XiCTaylorAnisotropicOrientedCoefficientSublinearUpper N) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorAnisotropicLogDerivSublinearUpper hN
    (xiCTaylorAnisotropicLogDerivSublinearUpper_of_orientedCoefficient hcoeff)

end

end RHTower
