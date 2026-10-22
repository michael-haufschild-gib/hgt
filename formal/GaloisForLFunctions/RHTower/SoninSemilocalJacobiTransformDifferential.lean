import GaloisForLFunctions.RHTower.SoninSemilocalJacobiRecurrence
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Differential recurrence for the archimedean Jacobi Fourier transforms

With `φ(t) = cosh(t)^(-1/2)`, this module differentiates the closed forms
`F_n(t) = i^n c_n φ(t) tanh(t)^n`, where `c_n` is the factorial normalization with
`c_n^2 = (2n)! / (2^n n!)^2` and `a_n = sqrt((n + 1/2)(n + 1))` is the Jacobi recurrence
coefficient. It proves `φ' = -(1/2) φ tanh`, `tanh' = 1 - tanh^2`, and the resulting
three-term differential recurrence `F_(n+1)' = i (a_n F_n + a_(n+1) F_(n+2))`.

## Main results

- `hasDerivAt_semilocalArchimedeanCharacteristic`: `φ'(t) = -(1/2) φ(t) tanh t`.
- `hasDerivAt_semilocalArchimedeanJacobiShape`: the derivative of `φ(t) tanh(t)^n` is
  `φ(t) (n tanh(t)^(n-1) - (n + 1/2) tanh(t)^(n+1))`.
- `hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm`: the corresponding derivative of `F_n`.
- `hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm_succ_recurrence`:
  `F_(n+1)'(t) = i (a_n F_n(t) + a_(n+1) F_(n+2)(t))` for every `n` and real `t`.

## Hypotheses

All results are unconditional; they hold for every `n : ℕ` and every real `t`.
-/

noncomputable section

namespace RHTower

/-- The archimedean characteristic `φ(t) = cosh(t)^(-1/2)` satisfies
`φ'(t) = -(1/2) φ(t) tanh t`. -/
theorem hasDerivAt_semilocalArchimedeanCharacteristic (t : ℝ) :
    HasDerivAt semilocalArchimedeanCharacteristic
      (-(1 / 2 : ℝ) * semilocalArchimedeanCharacteristic t * Real.tanh t) t := by
  unfold semilocalArchimedeanCharacteristic
  have hraw := (Real.hasDerivAt_cosh t).rpow_const
    (p := (-(1 : ℝ) / 2)) (Or.inl (Real.cosh_pos t).ne')
  convert hraw using 1
  rw [Real.rpow_sub (Real.cosh_pos t), Real.rpow_one,
    Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos t).ne']

/-- The real hyperbolic tangent has derivative `1 - tanh(t)^2`. -/
theorem hasDerivAt_tanh_one_sub_sq (t : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have hfun : Real.tanh = Real.sinh / Real.cosh := by
    funext x
    exact Real.tanh_eq_sinh_div_cosh x
  rw [hfun]
  have hraw := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t)
    (Real.cosh_pos t).ne'
  have hval :
      (Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) /
          Real.cosh t ^ 2 =
        1 - (Real.sinh t / Real.cosh t) ^ 2 := by
    field_simp [(Real.cosh_pos t).ne']
  rw [hval] at hraw
  exact hraw

/-- The real profile `φ(t) tanh(t)^n` of the `n`-th archimedean Jacobi Fourier transform. -/
def semilocalArchimedeanJacobiShape (n : ℕ) (t : ℝ) : ℝ :=
  semilocalArchimedeanCharacteristic t * Real.tanh t ^ n

/-- Derivative of the Jacobi profile:
`(φ tanh^n)' = φ (n tanh^(n-1) - (n + 1/2) tanh^(n+1))`. -/
theorem hasDerivAt_semilocalArchimedeanJacobiShape (n : ℕ) (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiShape n)
      (semilocalArchimedeanCharacteristic t *
        ((n : ℝ) * Real.tanh t ^ (n - 1) -
          ((n : ℝ) + 1 / 2) * Real.tanh t ^ (n + 1))) t := by
  have hraw := (hasDerivAt_semilocalArchimedeanCharacteristic t).mul
    ((hasDerivAt_tanh_one_sub_sq t).pow n)
  apply hraw.congr_deriv
  cases n <;> simp [pow_succ] <;> ring

/-- The closed form `F_n(t) = i^n c_n φ(t) tanh(t)^n` has derivative
`i^n c_n φ(t) (n tanh(t)^(n-1) - (n + 1/2) tanh(t)^(n+1))`. -/
theorem hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm
    (n : ℕ) (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiFourierClosedForm n)
      ((Complex.I ^ n * (semilocalArchimedeanJacobiNormalization n : ℂ)) *
        (semilocalArchimedeanCharacteristic t *
          ((n : ℝ) * Real.tanh t ^ (n - 1) -
            ((n : ℝ) + 1 / 2) * Real.tanh t ^ (n + 1)) : ℝ)) t := by
  have hcomplex := (hasDerivAt_semilocalArchimedeanJacobiShape n t).ofReal_comp
  have hscaled := hcomplex.const_mul
    (Complex.I ^ n * (semilocalArchimedeanJacobiNormalization n : ℂ))
  have hfun : semilocalArchimedeanJacobiFourierClosedForm n =
      fun y => (Complex.I ^ n * (semilocalArchimedeanJacobiNormalization n : ℂ)) *
        (semilocalArchimedeanJacobiShape n y : ℂ) := by
    funext y
    rw [semilocalArchimedeanJacobiFourierClosedForm,
      semilocalArchimedeanJacobiShape]
    push_cast
    ring
  rw [hfun]
  apply hscaled.congr_deriv
  ring

/-- At index `n + 1` the derivative value of `F_(n+1)` equals `i (a_n F_n(t) + a_(n+1) F_(n+2)(t))`,
using the normalization identities `(n+1) c_(n+1) = a_n c_n` and `c_(n+2) a_(n+1) = c_(n+1) (n + 3/2)`. -/
theorem semilocalArchimedeanJacobiFourierClosedForm_derivativeValue_succ
    (n : ℕ) (t : ℝ) :
    (Complex.I ^ (n + 1) *
        (semilocalArchimedeanJacobiNormalization (n + 1) : ℂ)) *
      (semilocalArchimedeanCharacteristic t *
        (((n + 1 : ℕ) : ℝ) * Real.tanh t ^ n -
          (((n + 1 : ℕ) : ℝ) + 1 / 2) * Real.tanh t ^ (n + 2)) : ℝ) =
      Complex.I *
        ((semilocalArchimedeanJacobiCoefficient n : ℂ) *
            semilocalArchimedeanJacobiFourierClosedForm n t +
          (semilocalArchimedeanJacobiCoefficient (n + 1) : ℂ) *
            semilocalArchimedeanJacobiFourierClosedForm (n + 2) t) := by
  have hback := semilocalArchimedeanJacobi_succ_mul_normalization n
  have hforward :=
    semilocalArchimedeanJacobiNormalization_succ_mul_coefficient (n + 1)
  have hbackC := congrArg Complex.ofReal hback
  have hforwardC := congrArg Complex.ofReal hforward
  norm_num at hbackC hforwardC
  have hIpow : Complex.I ^ (n + 2) = -(Complex.I ^ n) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    calc
      Complex.I ^ n * Complex.I * Complex.I =
          Complex.I ^ n * (Complex.I * Complex.I) := by ring
      _ = -(Complex.I ^ n) := by rw [Complex.I_mul_I]; ring
  rw [semilocalArchimedeanJacobiFourierClosedForm,
    semilocalArchimedeanJacobiFourierClosedForm]
  rw [show Complex.I ^ (n + 1) = Complex.I ^ n * Complex.I by rw [pow_succ],
    hIpow]
  push_cast
  calc
    Complex.I ^ n * Complex.I *
          (semilocalArchimedeanJacobiNormalization (n + 1) : ℂ) *
          ((semilocalArchimedeanCharacteristic t : ℂ) *
            (((n : ℂ) + 1) * Complex.tanh t ^ n -
              ((n : ℂ) + 1 + 1 / 2) * Complex.tanh t ^ (n + 2))) =
        Complex.I *
          ((((n : ℂ) + 1) *
                (semilocalArchimedeanJacobiNormalization (n + 1) : ℂ)) *
              (Complex.I ^ n *
                (semilocalArchimedeanCharacteristic t : ℂ) *
                Complex.tanh t ^ n) -
            (((semilocalArchimedeanJacobiNormalization (n + 1) : ℂ) *
                ((n : ℂ) + 1 + 1 / 2)) *
              (Complex.I ^ n *
                (semilocalArchimedeanCharacteristic t : ℂ) *
                Complex.tanh t ^ (n + 2)))) := by ring
    _ = Complex.I *
          (((semilocalArchimedeanJacobiCoefficient n : ℂ) *
                (semilocalArchimedeanJacobiNormalization n : ℂ)) *
              (Complex.I ^ n *
                (semilocalArchimedeanCharacteristic t : ℂ) *
                Complex.tanh t ^ n) -
            (((semilocalArchimedeanJacobiNormalization (n + 2) : ℂ) *
                (semilocalArchimedeanJacobiCoefficient (n + 1) : ℂ)) *
              (Complex.I ^ n *
                (semilocalArchimedeanCharacteristic t : ℂ) *
                Complex.tanh t ^ (n + 2)))) := by
      rw [hbackC, hforwardC]
    _ = Complex.I *
        ((semilocalArchimedeanJacobiCoefficient n : ℂ) *
            (Complex.I ^ n *
              (semilocalArchimedeanJacobiNormalization n : ℂ) *
              (semilocalArchimedeanCharacteristic t : ℂ) *
              Complex.tanh t ^ n) +
          (semilocalArchimedeanJacobiCoefficient (n + 1) : ℂ) *
            (-(Complex.I ^ n) *
              (semilocalArchimedeanJacobiNormalization (n + 2) : ℂ) *
              (semilocalArchimedeanCharacteristic t : ℂ) *
              Complex.tanh t ^ (n + 2))) := by ring

/-- Three-term Jacobi differential recurrence: `F_(n+1)' = i (a_n F_n + a_(n+1) F_(n+2))`
with `a_n = sqrt((n + 1/2)(n + 1))`. -/
theorem hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm_succ_recurrence
    (n : ℕ) (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiFourierClosedForm (n + 1))
      (Complex.I *
        ((semilocalArchimedeanJacobiCoefficient n : ℂ) *
            semilocalArchimedeanJacobiFourierClosedForm n t +
          (semilocalArchimedeanJacobiCoefficient (n + 1) : ℂ) *
            semilocalArchimedeanJacobiFourierClosedForm (n + 2) t)) t := by
  convert hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm (n + 1) t using 1
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_assoc] using
    (semilocalArchimedeanJacobiFourierClosedForm_derivativeValue_succ n t).symm

end RHTower
