import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational-function partial invariants

The quotient-rule extension of `d/dX` to `K(X)` has kernel exactly `K` in characteristic zero.
This is the one-variable elimination step needed to remove the highest free jet from a rational
current-algebra invariant.  Iterating it over the finite variable support of a free-jet rational
function gives the algebraic core of the projective-horizon fixed-field argument.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The ordinary polynomial derivative, valued in the rational-function field. -/
def polynomialDerivativeToRatFunc
    (K : Type*) [Field K] : Derivation K K[X] (RatFunc K) :=
  Polynomial.mkDerivation K (1 : RatFunc K)

/-- The quotient-rule extension of the polynomial derivative to `K(X)`. -/
def ratFuncDerivative
    (K : Type*) [Field K] : Derivation K (RatFunc K) (RatFunc K) :=
  GaloisForLFunctions.fractionRingDerivation (polynomialDerivativeToRatFunc K)

@[simp] theorem polynomialDerivativeToRatFunc_apply
    {K : Type*} [Field K] (p : K[X]) :
    polynomialDerivativeToRatFunc K p =
      algebraMap K[X] (RatFunc K) p.derivative := by
  simp [polynomialDerivativeToRatFunc, Polynomial.mkDerivation_apply,
    Algebra.smul_def]

@[simp] theorem ratFuncDerivative_algebraMap
    {K : Type*} [Field K] (p : K[X]) :
    ratFuncDerivative K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  rw [ratFuncDerivative, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  exact polynomialDerivativeToRatFunc_apply p

/-- In characteristic zero, a rational function has zero derivative exactly when it is a
base-field constant. -/
theorem ratFuncDerivative_eq_zero_iff
    {K : Type*} [Field K] [CharZero K] (r : RatFunc K) :
    ratFuncDerivative K r = 0 ↔
      ∃ c : K, r = algebraMap K (RatFunc K) c := by
  constructor
  · intro hr
    let p := r.num
    let q := r.denom
    have hq : q ≠ 0 := r.denom_ne_zero
    have hqK : algebraMap K[X] (RatFunc K) q ≠ 0 :=
      RatFunc.algebraMap_ne_zero hq
    have hrel : algebraMap K[X] (RatFunc K) p =
        r * algebraMap K[X] (RatFunc K) q := by
      exact (div_eq_iff hqK).mp (RatFunc.num_div_denom r)
    have hderiv := congrArg (ratFuncDerivative K) hrel
    simp only [ratFuncDerivative_algebraMap, Derivation.leibniz,
      smul_eq_mul, hr, mul_zero, add_zero] at hderiv
    have hcrossK :
        algebraMap K[X] (RatFunc K) (p.derivative * q) =
          algebraMap K[X] (RatFunc K) (p * q.derivative) := by
      simp only [map_mul]
      rw [hderiv, hrel]
      ring
    have hcross : p.derivative * q = p * q.derivative :=
      RatFunc.algebraMap_injective K hcrossK
    have hcoprime : IsCoprime p q := r.isCoprime_num_denom
    have hpdiv : p ∣ p.derivative := by
      apply hcoprime.dvd_of_dvd_mul_left
      exact ⟨q.derivative, by simpa [mul_comm] using hcross⟩
    have hqdiv : q ∣ q.derivative := by
      apply hcoprime.symm.dvd_of_dvd_mul_left
      exact ⟨p.derivative, by simpa [mul_comm] using hcross.symm⟩
    have hpderiv : p.derivative = 0 := by
      by_cases hp : p = 0
      · simp [hp]
      · exact Polynomial.eq_zero_of_dvd_of_degree_lt hpdiv
          (Polynomial.degree_derivative_lt hp)
    have hqderiv : q.derivative = 0 :=
      Polynomial.eq_zero_of_dvd_of_degree_lt hqdiv
        (Polynomial.degree_derivative_lt hq)
    have hpC := Polynomial.eq_C_of_derivative_eq_zero hpderiv
    have hqC := Polynomial.eq_C_of_derivative_eq_zero hqderiv
    have hpC_r : r.num = Polynomial.C (r.num.coeff 0) := by
      simpa [p] using hpC
    have hqC_r : r.denom = Polynomial.C (r.denom.coeff 0) := by
      simpa [q] using hqC
    refine ⟨r.num.coeff 0 / r.denom.coeff 0, ?_⟩
    have hmapC (c : K) :
        algebraMap K[X] (RatFunc K) (Polynomial.C c) =
          algebraMap K (RatFunc K) c := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    calc
      r = algebraMap K[X] (RatFunc K) r.num /
          algebraMap K[X] (RatFunc K) r.denom := (RatFunc.num_div_denom r).symm
      _ = algebraMap K[X] (RatFunc K) (Polynomial.C (r.num.coeff 0)) /
          algebraMap K[X] (RatFunc K) (Polynomial.C (r.denom.coeff 0)) := by
            conv_lhs => rw [hpC_r, hqC_r]
      _ = algebraMap K (RatFunc K) (r.num.coeff 0) /
          algebraMap K (RatFunc K) (r.denom.coeff 0) := by rw [hmapC, hmapC]
      _ = algebraMap K (RatFunc K) (r.num.coeff 0 / r.denom.coeff 0) := by
            rw [map_div₀]
  · rintro ⟨c, rfl⟩
    exact (ratFuncDerivative K).map_algebraMap c

end

end GaloisForLFunctions.HTGeometry
