import GaloisForLFunctions.KodairaParshinAbc.Periods.EulerPolynomial

/-!
# Factorial regularization of formal differential equations

The coefficient transformation in Remark 3.3 of arXiv:2611.13126 sends
`Σ a_n q^n/n!` to `Σ a_n q^n`. It commutes with every polynomial in the
Euler operator, while multiplication by the coordinate gains an Euler
factor. The inverse transform is defined over all formal series; no
convergence or summability assumption enters these identities.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open PowerSeries HTGeometry

/-- Multiply the coefficient of degree `n` by `n!`. -/
def factorialRegularization (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial : ℂ) * PowerSeries.coeff n f

/-- The inverse factorial transform. -/
def formalBorel (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff n f / (n.factorial : ℂ)

@[simp] theorem coeff_factorialRegularization (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (factorialRegularization f) =
      (n.factorial : ℂ) * PowerSeries.coeff n f := by simp [factorialRegularization]

@[simp] theorem coeff_formalBorel (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (formalBorel f) =
      PowerSeries.coeff n f / (n.factorial : ℂ) := by simp [formalBorel]

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

theorem factorialRegularization_formalBorel (f : PowerSeries ℂ) :
    factorialRegularization (formalBorel f) = f := by
  ext n
  rw [coeff_factorialRegularization, coeff_formalBorel]
  exact mul_div_cancel₀ _ (factorial_cast_ne_zero n)

theorem formalBorel_factorialRegularization (f : PowerSeries ℂ) :
    formalBorel (factorialRegularization f) = f := by
  ext n
  rw [coeff_formalBorel, coeff_factorialRegularization]
  exact mul_div_cancel_left₀ _ (factorial_cast_ne_zero n)

/-- Regularization commutes with every Euler polynomial, hence with every Euler iterate. -/
theorem factorialRegularization_eulerPolynomial (p : Polynomial ℂ) (f : PowerSeries ℂ) :
    factorialRegularization (eulerPolynomial p f) =
      eulerPolynomial p (factorialRegularization f) := by
  ext n
  simp only [coeff_factorialRegularization, coeff_eulerPolynomial]
  ring

/-- Multiplication by the coordinate gains the factor `θ+1` under regularization. -/
theorem factorialRegularization_mul_X (f : PowerSeries ℂ) :
    factorialRegularization (PowerSeries.X * f) =
      PowerSeries.X * (formalEulerOp (factorialRegularization f) + factorialRegularization f) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp only [coeff_factorialRegularization, coeff_succ_X_mul, map_add,
        coeff_formalEulerOp, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Ordinary differentiation becomes coefficient shift under regularization. -/
theorem factorialRegularization_derivative (f : PowerSeries ℂ) :
    PowerSeries.X * factorialRegularization (PowerSeries.derivative ℂ f) =
      factorialRegularization f - PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext n
  cases n with
  | zero => simp [factorialRegularization]
  | succ n =>
      simp only [coeff_succ_X_mul, coeff_factorialRegularization, coeff_derivative,
        map_sub, coeff_C, Nat.succ_ne_zero, if_false, sub_zero,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end GaloisForLFunctions.KodairaParshinAbc.Periods
