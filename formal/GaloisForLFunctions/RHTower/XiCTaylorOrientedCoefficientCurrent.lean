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

/-- A polynomial obtained from real coefficients has zero oriented current on the real axis. -/
theorem orientedPolynomialCurrent_map_real_eq_zero
    (Q : Polynomial ℝ) (x : ℝ) :
    orientedPolynomialCurrent (Q.map (algebraMap ℝ ℂ)) (x : ℂ) = 0 := by
  unfold orientedPolynomialCurrent
  rw [Polynomial.derivative_map]
  change
    (((Q.derivative.map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) x)) *
      (starRingEnd ℂ) ((Q.map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) x))).im = 0
  rw [Polynomial.eval_map_apply, Polynomial.eval_map_apply]
  simp

/-- The oriented current is minus one half of the vertical derivative of the squared modulus.
This is the value-coordinate form of the upper-current problem and requires no nonvanishing
hypothesis. -/
theorem hasDerivAt_normSq_polynomial_vertical
    (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.normSq
        (P.eval ((x : ℂ) + (t : ℂ) * I)))
      (-2 * orientedPolynomialCurrent P ((x : ℂ) + (y : ℂ) * I)) y := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * I
  have hz : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using h.const_add (x : ℂ)
  have hf : HasDerivAt
      (fun t : ℝ => P.eval ((x : ℂ) + (t : ℂ) * I))
      (P.derivative.eval z * I) y := by
    simpa [z] using (P.hasDerivAt z).comp y hz
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hf
  have h := (hre.mul hre).add (him.mul him)
  rw [show (fun t : ℝ => Complex.normSq
      (P.eval ((x : ℂ) + (t : ℂ) * I))) =
      fun t : ℝ =>
        (P.eval ((x : ℂ) + (t : ℂ) * I)).re ^ 2 +
          (P.eval ((x : ℂ) + (t : ℂ) * I)).im ^ 2 by
    funext t
    rw [Complex.normSq_apply]
    ring]
  convert h using 1
  · funext t
    simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, pow_two]
    change _ =
      (P.eval ((x : ℂ) + (t : ℂ) * I)).re *
          (P.eval ((x : ℂ) + (t : ℂ) * I)).re +
        (P.eval ((x : ℂ) + (t : ℂ) * I)).im *
          (P.eval ((x : ℂ) + (t : ℂ) * I)).im
    rfl
  · dsimp [z]
    unfold orientedPolynomialCurrent
    simp only [mul_re, mul_im, I_re, I_im, mul_zero, mul_one,
      Complex.conj_re, Complex.conj_im]
    ring

/-- The vertical derivative of the oriented current is the finite complex Laguerre defect.
Together with `hasDerivAt_normSq_polynomial_vertical`, this identifies the exact curvature that
would be needed to propagate a current sign between horizontal fibres. -/
theorem hasDerivAt_orientedPolynomialCurrent_vertical
    (P : Polynomial ℂ) (x y : ℝ) :
    HasDerivAt
      (fun t : ℝ => orientedPolynomialCurrent P
        ((x : ℂ) + (t : ℂ) * I))
      ((P.derivative.derivative.eval ((x : ℂ) + (y : ℂ) * I) *
          (starRingEnd ℂ) (P.eval ((x : ℂ) + (y : ℂ) * I))).re -
        Complex.normSq
          (P.derivative.eval ((x : ℂ) + (y : ℂ) * I))) y := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * I
  have hz : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using h.const_add (x : ℂ)
  have hP : HasDerivAt
      (fun t : ℝ => P.eval ((x : ℂ) + (t : ℂ) * I))
      (P.derivative.eval z * I) y := by
    simpa [z] using (P.hasDerivAt z).comp y hz
  have hPd : HasDerivAt
      (fun t : ℝ => P.derivative.eval ((x : ℂ) + (t : ℂ) * I))
      (P.derivative.derivative.eval z * I) y := by
    simpa [z] using (P.derivative.hasDerivAt z).comp y hz
  have hconj : HasDerivAt
      (fun t : ℝ => (starRingEnd ℂ)
        (P.eval ((x : ℂ) + (t : ℂ) * I)))
      ((starRingEnd ℂ) (P.derivative.eval z * I)) y := by
    simpa only [Complex.conjCLE_apply] using
      Complex.conjCLE.hasFDerivAt.comp_hasDerivAt y hP
  have hprod := hPd.mul hconj
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hprod
  convert him using 1
  dsimp [z]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- For a polynomial with real coefficients, the current on a vertical fibre is the integral from
the real axis of its finite complex Laguerre defect. -/
theorem orientedPolynomialCurrent_map_real_eq_integral_verticalLaguerreDefect
    (Q : Polynomial ℝ) (x y : ℝ) :
    orientedPolynomialCurrent (Q.map (algebraMap ℝ ℂ))
        ((x : ℂ) + (y : ℂ) * I) =
      ∫ t : ℝ in 0..y,
        (((Q.map (algebraMap ℝ ℂ)).derivative.derivative.eval
              ((x : ℂ) + (t : ℂ) * I) *
            (starRingEnd ℂ)
              ((Q.map (algebraMap ℝ ℂ)).eval
                ((x : ℂ) + (t : ℂ) * I))).re -
          Complex.normSq
            ((Q.map (algebraMap ℝ ℂ)).derivative.eval
              ((x : ℂ) + (t : ℂ) * I))) := by
  let P : Polynomial ℂ := Q.map (algebraMap ℝ ℂ)
  let g : ℝ → ℝ := fun t =>
    ((P.derivative.derivative.eval ((x : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (P.eval ((x : ℂ) + (t : ℂ) * I))).re -
      Complex.normSq (P.derivative.eval ((x : ℂ) + (t : ℂ) * I)))
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt
        (fun s : ℝ => orientedPolynomialCurrent P
          ((x : ℂ) + (s : ℂ) * I)) (g t) t := by
    intro t _ht
    exact hasDerivAt_orientedPolynomialCurrent_vertical P x t
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hg.intervalIntegrable 0 y)
  have hzero : orientedPolynomialCurrent P (x : ℂ) = 0 := by
    exact orientedPolynomialCurrent_map_real_eq_zero Q x
  change orientedPolynomialCurrent P ((x : ℂ) + (y : ℂ) * I) =
    ∫ t : ℝ in 0..y, g t
  rw [hftc]
  simp only [ofReal_zero, zero_mul, add_zero, hzero, sub_zero]

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
