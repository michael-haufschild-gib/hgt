import GaloisForLFunctions.KodairaParshinAbc.Periods.FactorialRegularization
import GaloisForLFunctions.KodairaParshinAbc.Periods.LogarithmicPrimitive
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
# Projective hypersurface periods in every dimension

The factorial quotient `((r+2)d)!/(d!)^(r+2)` satisfies the Picard--Fuchs
recurrence of a degree-`r+2` hypersurface in projective `r+1`-space. The
proof is uniform in dimension and degree. The same period is the factorial
regularization of the sparse ambient series after the coordinate power map.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open PowerSeries HTGeometry

/-- Holomorphic hypersurface-period coefficients. -/
def projectivePeriodCoefficient (r d : ℕ) : ℂ :=
  (((r + 2) * d).factorial : ℂ) / (d.factorial : ℂ) ^ (r + 2)

/-- The Euler polynomial on the right side of the Picard--Fuchs recurrence. -/
def projectiveStepPolynomial (r : ℕ) : Polynomial ℂ :=
  Polynomial.C (r + 2 : ℂ) * ∏ j ∈ Finset.range (r + 1),
    (Polynomial.C (r + 2 : ℂ) * Polynomial.X + Polynomial.C (j + 1 : ℂ))

theorem eval_projectiveStepPolynomial (r d : ℕ) :
    (projectiveStepPolynomial r).eval (d : ℂ) =
      (r + 2 : ℂ) * ∏ j ∈ Finset.range (r + 1), ((r + 2 : ℂ) * d + (j + 1)) := by
  simp [projectiveStepPolynomial, Polynomial.eval_prod]

private theorem factorial_step (r d : ℕ) :
    (((r + 2) * (d + 1)).factorial : ℂ) =
      (((r + 2) * d).factorial : ℂ) *
        ((r + 2 : ℂ) * (d + 1)) *
        ∏ j ∈ Finset.range (r + 1), ((r + 2 : ℂ) * d + (j + 1)) := by
  have h := Nat.factorial_mul_ascFactorial ((r + 2) * d) (r + 2)
  rw [Nat.ascFactorial_succ, Nat.ascFactorial_eq_prod_range] at h
  have htop : (r + 2) * d + (r + 2) = (r + 2) * (d + 1) := by ring
  rw [htop] at h
  have hc := congrArg (fun k : ℕ => (k : ℂ)) h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_prod] at hc
  have hlin : (r + 2 : ℂ) * d + 1 + (r + 1) = (r + 2 : ℂ) * (d + 1) := by ring
  have hprod : (∏ j ∈ Finset.range (r + 1), ((r + 2 : ℂ) * d + 1 + j)) =
      ∏ j ∈ Finset.range (r + 1), ((r + 2 : ℂ) * d + (j + 1)) := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hlin, hprod] at hc
  simpa only [mul_assoc] using hc.symm

/-- The full Picard--Fuchs coefficient recurrence, at every degree and dimension. -/
theorem projectivePeriodCoefficient_recurrence (r d : ℕ) :
    (d + 1 : ℂ) ^ (r + 1) * projectivePeriodCoefficient r (d + 1) =
      (projectiveStepPolynomial r).eval (d : ℂ) * projectivePeriodCoefficient r d := by
  have hd : (d + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have hf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [projectivePeriodCoefficient, projectivePeriodCoefficient, factorial_step,
    eval_projectiveStepPolynomial, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ (d + 1 : ℂ)]
  field_simp
  ring

/-- The normalized holomorphic period. -/
def projectivePeriod (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (projectivePeriodCoefficient r)

@[simp] theorem coeff_projectivePeriod (r d : ℕ) :
    PowerSeries.coeff d (projectivePeriod r) = projectivePeriodCoefficient r d := by
  simp [projectivePeriod]

/-- A uniform Picard--Fuchs equation, containing the cubic, quartic and quintic operators. -/
theorem projectivePeriod_picardFuchs (r : ℕ) :
    (formalEulerOp^[r + 1]) (projectivePeriod r) =
      PowerSeries.X * eulerPolynomial (projectiveStepPolynomial r) (projectivePeriod r) := by
  ext d
  cases d with
  | zero => simp [coeff_formalEulerOp_iterate]
  | succ d =>
      simp only [coeff_formalEulerOp_iterate, coeff_succ_X_mul,
        coeff_eulerPolynomial, coeff_projectivePeriod, Nat.cast_add, Nat.cast_one]
      exact projectivePeriodCoefficient_recurrence r d

/-- The entire regular solution space is the line spanned by the normalized period. -/
theorem projectivePeriod_solution_iff (r : ℕ) (f : PowerSeries ℂ) :
    (formalEulerOp^[r + 1]) f =
        PowerSeries.X * eulerPolynomial (projectiveStepPolynomial r) f ↔
      f = PowerSeries.C (PowerSeries.constantCoeff f) * projectivePeriod r := by
  constructor
  · intro h
    ext n
    induction n with
    | zero => simp [projectivePeriod, projectivePeriodCoefficient]
    | succ n ih =>
        have hn : (n + 1 : ℂ) ^ (r + 1) ≠ 0 :=
          pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
        have hc := congrArg (PowerSeries.coeff (n + 1)) h
        simp only [coeff_formalEulerOp_iterate, coeff_succ_X_mul,
          coeff_eulerPolynomial, Nat.cast_add, Nat.cast_one] at hc
        apply mul_left_cancel₀ hn
        rw [coeff_C_mul, coeff_projectivePeriod] at ih ⊢
        rw [hc, ih]
        have hp := projectivePeriodCoefficient_recurrence r n
        linear_combination -PowerSeries.constantCoeff f * hp
  · intro h
    have hp := projectivePeriod_picardFuchs r
    ext n
    have hc := congrArg (PowerSeries.coeff n) hp
    rw [h]
    cases n with
    | zero => simp [coeff_formalEulerOp_iterate]
    | succ n =>
        simp only [coeff_formalEulerOp_iterate, coeff_succ_X_mul,
          coeff_eulerPolynomial, coeff_C_mul] at hc ⊢
        linear_combination PowerSeries.constantCoeff f * hc

/-- The sparse ambient period before factorial regularization. -/
def projectiveAmbientSeries (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if (r + 2) ∣ n then 1 / ((n / (r + 2)).factorial : ℂ) ^ (r + 2) else 0

/-- Factorial regularization and the projective coordinate power map agree exactly. -/
theorem projectiveAmbient_regularization (r : ℕ) :
    factorialRegularization (projectiveAmbientSeries r) =
      PowerSeries.expand (r + 2) (by omega) (projectivePeriod r) := by
  ext n
  rw [coeff_factorialRegularization, projectiveAmbientSeries, coeff_mk, coeff_expand]
  split_ifs with h
  · rw [coeff_projectivePeriod, projectivePeriodCoefficient, Nat.mul_div_cancel' h]
    ring
  · ring

/-- The local period consists of one logarithm and the canonical regular primitive. -/
def projectiveLocalPeriod (r : ℕ) : ℂ × PowerSeries ℂ :=
  (1, eulerPrimitive (projectivePeriod r))

theorem projectiveLocalPeriod_euler (r : ℕ) :
    logarithmicEuler (projectiveLocalPeriod r) = projectivePeriod r := by
  have h := logarithmicEuler_primitive (projectivePeriod r)
  simpa [projectiveLocalPeriod, projectivePeriod, projectivePeriodCoefficient] using h

/-- The uniform local period solves the operator with the Euler factor on the right. -/
theorem projectiveLocalPeriod_picardFuchs (r : ℕ) :
    (formalEulerOp^[r + 1]) (logarithmicEuler (projectiveLocalPeriod r)) =
      PowerSeries.X * eulerPolynomial (projectiveStepPolynomial r)
        (logarithmicEuler (projectiveLocalPeriod r)) := by
  rw [projectiveLocalPeriod_euler]
  exact projectivePeriod_picardFuchs r

end GaloisForLFunctions.KodairaParshinAbc.Periods

#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.eval_projectiveStepPolynomial
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectivePeriodCoefficient_recurrence
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.coeff_projectivePeriod
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectivePeriod_picardFuchs
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectivePeriod_solution_iff
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectiveAmbient_regularization
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectiveLocalPeriod_euler
#print axioms GaloisForLFunctions.KodairaParshinAbc.Periods.projectiveLocalPeriod_picardFuchs
