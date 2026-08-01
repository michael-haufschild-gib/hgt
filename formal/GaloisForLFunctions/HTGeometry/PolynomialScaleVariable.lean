import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Substituting a scalar multiple of the variable

Replacing the variable by a scalar multiple of itself is a ring homomorphism of the polynomial ring
that multiplies the `j`-th coefficient by the `j`-th power of the scalar.  It is the operation that
records how a coefficient of a polynomial changes when the variable is rescaled.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A]

/-- Substituting a scalar multiple of the variable. -/
noncomputable def scaleVar (c : A) : Polynomial A →+* Polynomial A :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C c * Polynomial.X)

/-- **Rescaling the variable scales the coefficients by powers of the scalar.** -/
theorem coeff_scaleVar (c : A) (p : Polynomial A) (j : ℕ) :
    (scaleVar c p).coeff j = c ^ j * p.coeff j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial k a =>
      have hval : scaleVar c (Polynomial.monomial k a) =
          Polynomial.C (a * c ^ k) * Polynomial.X ^ k := by
        rw [scaleVar]
        simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, mul_pow,
          ← Polynomial.C_pow, Polynomial.C_mul]
        ring
      rw [hval, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
      by_cases h : j = k
      · subst h
        rw [if_pos rfl, if_pos rfl, mul_one]
        ring
      · rw [if_neg h, if_neg (fun hcon => h hcon.symm), mul_zero, mul_zero]

end GaloisForLFunctions.HTGeometry
