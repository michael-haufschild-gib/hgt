import GaloisForLFunctions.HTGeometry.FormalEulerOperator

/-!
# Polynomial calculus for the Euler operator

Since `θ=q d/dq` is diagonal on monomials, `P(θ)` acts on the coefficient
of degree `n` by `P(n)`. Multiplication by `q` shifts `P(θ)` to `P(θ+1)`.
This is the operator identity behind the differing left and right Euler
factors of the regularized and local Picard--Fuchs equations.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open PowerSeries HTGeometry

/-- Polynomial functional calculus for the existing formal Euler operator. -/
def eulerPolynomial (p : Polynomial ℂ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.eval (n : ℂ) * PowerSeries.coeff n f

@[simp] theorem coeff_eulerPolynomial (p : Polynomial ℂ) (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (eulerPolynomial p f) = p.eval (n : ℂ) * PowerSeries.coeff n f := by
  simp [eulerPolynomial]

theorem eulerPolynomial_X (f : PowerSeries ℂ) :
    eulerPolynomial Polynomial.X f = formalEulerOp f := by
  ext n
  simp only [coeff_eulerPolynomial, Polynomial.eval_X, coeff_formalEulerOp]

theorem eulerPolynomial_one (f : PowerSeries ℂ) : eulerPolynomial 1 f = f := by
  ext n
  simp only [coeff_eulerPolynomial, Polynomial.eval_one, one_mul]

theorem eulerPolynomial_X_pow (j : ℕ) (f : PowerSeries ℂ) :
    eulerPolynomial (Polynomial.X ^ j) f = (formalEulerOp^[j]) f := by
  ext n
  simp only [coeff_eulerPolynomial, Polynomial.eval_pow, Polynomial.eval_X,
    coeff_formalEulerOp_iterate]

theorem eulerPolynomial_add (p q : Polynomial ℂ) (f : PowerSeries ℂ) :
    eulerPolynomial (p + q) f = eulerPolynomial p f + eulerPolynomial q f := by
  ext n
  simp only [coeff_eulerPolynomial, Polynomial.eval_add, map_add, add_mul]

/-- Multiplication of Euler polynomials is composition of their differential operators. -/
theorem eulerPolynomial_mul (p q : Polynomial ℂ) (f : PowerSeries ℂ) :
    eulerPolynomial (p * q) f = eulerPolynomial p (eulerPolynomial q f) := by
  ext n
  simp only [coeff_eulerPolynomial, Polynomial.eval_mul, mul_assoc]

/-- Moving a coordinate factor across the differential operator shifts its argument by one. -/
theorem eulerPolynomial_mul_X (p : Polynomial ℂ) (f : PowerSeries ℂ) :
    eulerPolynomial p (PowerSeries.X * f) =
      PowerSeries.X * eulerPolynomial (p.comp (Polynomial.X + 1)) f := by
  ext n
  cases n with
  | zero => simp [coeff_eulerPolynomial]
  | succ n =>
      simp only [coeff_eulerPolynomial, coeff_succ_X_mul, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
        Nat.cast_add, Nat.cast_one]

/-- The Euler commutator with the coordinate is the coordinate itself. -/
theorem formalEulerOp_mul_X (f : PowerSeries ℂ) :
    formalEulerOp (PowerSeries.X * f) =
      PowerSeries.X * (formalEulerOp f + f) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp only [coeff_formalEulerOp, coeff_succ_X_mul, map_add, Nat.cast_add, Nat.cast_one]
      ring

end GaloisForLFunctions.KodairaParshinAbc.Periods
