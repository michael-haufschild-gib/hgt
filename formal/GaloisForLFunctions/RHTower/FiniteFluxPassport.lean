import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Finite completed-flux passport realization

For a simple zero written locally as

`f(x) = x * exp(P(x))`,

the residue-filled negative logarithmic flux is exactly the polynomial

`-1 - x P'(x)`.

Conversely, every polynomial passport with constant coefficient `-1` has this form.  Thus the
finite completed-flux passport map is surjective before any global symmetry or positivity
constraints are imposed.  This is the local algebraic interface used by the positive finite-passport
classification theorem.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The polynomial residue-filled completed-flux passport associated with the logarithmic unit
polynomial `P`. -/
def polynomialCompletedFluxPassport (P : Polynomial ℂ) : Polynomial ℂ :=
  -C 1 - X * derivative P

@[simp] theorem polynomialCompletedFluxPassport_coeff_zero (P : Polynomial ℂ) :
    (polynomialCompletedFluxPassport P).coeff 0 = -1 := by
  simp [polynomialCompletedFluxPassport]

/-- Every positive-degree passport coefficient is independently controlled by the corresponding
coefficient of the logarithmic unit. -/
theorem polynomialCompletedFluxPassport_coeff_succ (P : Polynomial ℂ) (n : ℕ) :
    (polynomialCompletedFluxPassport P).coeff (n + 1) =
      -(n + 1 : ℂ) * P.coeff (n + 1) := by
  simp [polynomialCompletedFluxPassport, coeff_derivative, Polynomial.coeff_one]
  ring

/-- Coefficientwise polynomial antiderivative over `ℂ`, normalized to have zero constant term. -/
def polynomialAntiderivative (Q : Polynomial ℂ) : Polynomial ℂ :=
  Q.sum fun n a => monomial (n + 1) (a / (n + 1 : ℂ))

@[simp] theorem derivative_polynomialAntiderivative (Q : Polynomial ℂ) :
    derivative (polynomialAntiderivative Q) = Q := by
  classical
  rw [polynomialAntiderivative, Polynomial.sum_def, derivative_sum]
  simp_rw [derivative_monomial_succ]
  calc
    ∑ n ∈ Q.support, monomial n (Q.coeff n / (n + 1 : ℂ) * (n + 1 : ℂ)) =
        ∑ n ∈ Q.support, monomial n (Q.coeff n) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      field_simp
    _ = Q := by rw [← Polynomial.sum_def, Polynomial.sum_monomial_eq]

/-- The logarithmic unit polynomial reconstructed from a passport.  Division by `X` removes the
forced constant coefficient `-1`; antiderivation then inverts `P ↦ -1 - X P'`. -/
def polynomialLogUnitForPassport (H : Polynomial ℂ) : Polynomial ℂ :=
  -polynomialAntiderivative ((H + C 1) /ₘ X)

/-- **Polynomial passport surjectivity.** Every polynomial with constant coefficient `-1` is the
completed-flux passport of one logarithmic unit polynomial. -/
theorem polynomialCompletedFluxPassport_logUnit_eq
    (H : Polynomial ℂ) (h0 : H.coeff 0 = -1) :
    polynomialCompletedFluxPassport (polynomialLogUnitForPassport H) = H := by
  have hroot : (H + C 1).IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_add, eval_C,
      ← Polynomial.coeff_zero_eq_eval_zero H, h0]
    simp
  have hdiv : X * ((H + C 1) /ₘ X) = H + C 1 := by
    simpa using
      (Polynomial.mul_divByMonic_eq_iff_isRoot (p := H + C 1) (a := 0)).mpr hroot
  rw [polynomialCompletedFluxPassport, polynomialLogUnitForPassport,
    derivative_neg, derivative_polynomialAntiderivative]
  rw [show X * -((H + C 1) /ₘ X) = -(X * ((H + C 1) /ₘ X)) by ring, hdiv]
  ring

theorem exists_polynomialCompletedFluxPassport_eq
    (H : Polynomial ℂ) (h0 : H.coeff 0 = -1) :
    ∃ P : Polynomial ℂ, polynomialCompletedFluxPassport P = H :=
  ⟨polynomialLogUnitForPassport H, polynomialCompletedFluxPassport_logUnit_eq H h0⟩

/-- Entire simple-zero germ realizing the passport of `P`. -/
def simpleZeroExponentialRealizer (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  z * Complex.exp (P.eval z)

theorem hasDerivAt_simpleZeroExponentialRealizer (P : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (simpleZeroExponentialRealizer P)
      (Complex.exp (P.eval z) +
        z * (Complex.exp (P.eval z) * (derivative P).eval z)) z := by
  change HasDerivAt (fun x : ℂ => x * Complex.exp (P.eval x)) _ z
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (hasDerivAt_id z).mul ((P.hasDerivAt z).cexp)

theorem simpleZeroExponentialRealizer_analyticAt (P : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (simpleZeroExponentialRealizer P) z := by
  have hpoly : AnalyticAt ℂ (fun x : ℂ => P.eval x) z := by
    simpa only [aeval_def] using analyticAt_id.aeval_polynomial P
  exact analyticAt_id.mul hpoly.cexp

@[simp] theorem simpleZeroExponentialRealizer_zero (P : Polynomial ℂ) :
    simpleZeroExponentialRealizer P 0 = 0 := by
  simp [simpleZeroExponentialRealizer]

/-- The realized zero is simple. -/
theorem deriv_simpleZeroExponentialRealizer_zero_ne (P : Polynomial ℂ) :
    deriv (simpleZeroExponentialRealizer P) 0 ≠ 0 := by
  rw [(hasDerivAt_simpleZeroExponentialRealizer P 0).deriv]
  simpa only [zero_mul, add_zero] using Complex.exp_ne_zero (P.eval 0)

/-- Away from the removable center, the polynomial passport is the actual negative normalized
logarithmic derivative of the realized simple-zero germ. -/
theorem polynomialCompletedFluxPassport_eval_eq_neg_mul_logDeriv
    (P : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    (polynomialCompletedFluxPassport P).eval z =
      -z * deriv (simpleZeroExponentialRealizer P) z /
        simpleZeroExponentialRealizer P z := by
  rw [polynomialCompletedFluxPassport, eval_sub, eval_neg, eval_C, eval_mul, eval_X,
    (hasDerivAt_simpleZeroExponentialRealizer P z).deriv]
  unfold simpleZeroExponentialRealizer
  field_simp [hz, Complex.exp_ne_zero]
  ring

/-- **Local finite-passport realization.** Every polynomial completed-flux passport with the forced
simple-zero residue `-1` is realized exactly by an entire simple-zero germ. -/
theorem exists_simpleZeroExponentialRealizer_of_passport
    (H : Polynomial ℂ) (h0 : H.coeff 0 = -1) :
    ∃ P : Polynomial ℂ,
      (∀ z, AnalyticAt ℂ (simpleZeroExponentialRealizer P) z) ∧
      simpleZeroExponentialRealizer P 0 = 0 ∧
      deriv (simpleZeroExponentialRealizer P) 0 ≠ 0 ∧
      ∀ z ≠ 0,
        H.eval z = -z * deriv (simpleZeroExponentialRealizer P) z /
          simpleZeroExponentialRealizer P z := by
  refine ⟨polynomialLogUnitForPassport H,
    simpleZeroExponentialRealizer_analyticAt _,
    simpleZeroExponentialRealizer_zero _,
    deriv_simpleZeroExponentialRealizer_zero_ne _, ?_⟩
  intro z hz
  calc
    H.eval z =
        (polynomialCompletedFluxPassport (polynomialLogUnitForPassport H)).eval z := by
          rw [polynomialCompletedFluxPassport_logUnit_eq H h0]
    _ = -z * deriv (simpleZeroExponentialRealizer (polynomialLogUnitForPassport H)) z /
          simpleZeroExponentialRealizer (polynomialLogUnitForPassport H) z :=
      polynomialCompletedFluxPassport_eval_eq_neg_mul_logDeriv _ hz

end

end RHTower
