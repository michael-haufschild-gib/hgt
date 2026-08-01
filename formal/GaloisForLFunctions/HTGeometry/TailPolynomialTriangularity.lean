import GaloisForLFunctions.HTGeometry.DerivationPolynomialCoefficientwise
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The tail polynomial and the triangularity of its power coefficients

The tail of a truncated Taylor jet is the polynomial whose coefficients are the free parameters.
Differentiating in the `i`-th parameter multiplies by the `i`-th power of the formal variable, so
by the chain rule the derivative of a coefficient of a power of the tail is a shifted coefficient of
the next lower power.

Hence that derivative vanishes below the shift and equals the parameter power on the diagonal:
the change of parameters is triangular with a nonvanishing diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The tail polynomial: the free parameters read as the coefficients of a polynomial. -/
noncomputable def tailPoly (K : Type*) [Field K] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) K) :=
  ∑ i : Fin n, Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (i : ℕ)

theorem coeff_tailPoly (j : ℕ) :
    (tailPoly K n).coeff j =
      if h : j < n then MvPolynomial.X (⟨j, h⟩ : Fin n) else 0 := by
  classical
  rw [tailPoly, Polynomial.finsetSum_coeff]
  by_cases hj : j < n
  · rw [dif_pos hj, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
      intro hcon
      exact hb (Fin.ext hcon.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hj]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    intro hcon
    exact hj (hcon ▸ b.2)

/-- **Differentiating the tail in a parameter gives a power of the variable.** -/
theorem coeffwiseDerivation_pderiv_tailPoly (i : Fin n) :
    coeffwiseDerivation (MvPolynomial.pderiv i) (tailPoly K n) =
      (Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ (i : ℕ) := by
  classical
  refine Polynomial.ext fun j => ?_
  rw [coeff_coeffwiseDerivation, coeff_tailPoly, Polynomial.coeff_X_pow]
  by_cases hj : j < n
  · rw [dif_pos hj, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hij : j = (i : ℕ)
    · rw [if_pos (show (⟨j, hj⟩ : Fin n) = i from Fin.ext hij), if_pos hij]
    · rw [if_neg (show ¬((⟨j, hj⟩ : Fin n) = i) from fun hcon => hij (congrArg Fin.val hcon)),
        if_neg hij]
  · rw [dif_neg hj, map_zero, if_neg ?_]
    intro hcon
    exact hj (hcon ▸ i.2)

/-- **The chain rule for coefficients of powers of the tail.** -/
theorem pderiv_coeff_tailPoly_pow (i : Fin n) (m j : ℕ) :
    MvPolynomial.pderiv i (((tailPoly K n) ^ m).coeff j) =
      (m : MvPolynomial (Fin n) K) *
        (((tailPoly K n) ^ (m - 1)) *
          (Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ (i : ℕ)).coeff j := by
  have h := coeff_pow_coeffwise (MvPolynomial.pderiv i) (tailPoly K n) m j
  rw [coeffwiseDerivation_pderiv_tailPoly] at h
  rw [h, Polynomial.coeff_smul, nsmul_eq_mul]

/-- **Triangularity.**  Below the shift the derivative vanishes. -/
theorem pderiv_coeff_tailPoly_pow_eq_zero (i : Fin n) (m j : ℕ) (hij : j < (i : ℕ)) :
    MvPolynomial.pderiv i (((tailPoly K n) ^ m).coeff j) = 0 := by
  rw [pderiv_coeff_tailPoly_pow, mul_comm ((tailPoly K n) ^ (m - 1)),
    Polynomial.coeff_X_pow_mul' , if_neg (by omega), mul_zero]

/-- **The diagonal derivative.** -/
theorem pderiv_coeff_tailPoly_pow_diag (i : Fin n) (m : ℕ) :
    MvPolynomial.pderiv i (((tailPoly K n) ^ m).coeff (i : ℕ)) =
      (m : MvPolynomial (Fin n) K) * ((tailPoly K n) ^ (m - 1)).coeff 0 := by
  have hcoeff : (((tailPoly K n) ^ (m - 1)) *
      (Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ (i : ℕ)).coeff (i : ℕ) =
      ((tailPoly K n) ^ (m - 1)).coeff 0 := by
    rw [mul_comm]
    have h := Polynomial.coeff_X_pow_mul ((tailPoly K n) ^ (m - 1)) (i : ℕ) 0
    rwa [Nat.zero_add] at h
  rw [pderiv_coeff_tailPoly_pow, hcoeff]

theorem coeff_zero_tailPoly_pow (hn : 0 < n) (m : ℕ) :
    ((tailPoly K n) ^ m).coeff 0 = (MvPolynomial.X (⟨0, hn⟩ : Fin n)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Polynomial.mul_coeff_zero, ih, coeff_tailPoly, dif_pos hn, pow_succ]

end GaloisForLFunctions.HTGeometry
