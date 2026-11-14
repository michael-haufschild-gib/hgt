import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# Coefficients under a power-map residue decomposition

If `deg f < p`, a coefficient of `f(X) g(X^p)` receives exactly one contribution:
the low digit selects a coefficient of `f`, and the quotient selects one of `g`.
This is the coefficient mechanism behind Frobenius digit factorizations.
-/

noncomputable section

namespace GaloisForLFunctions

open Polynomial

/-- Multiplication by a polynomial of degree below the substitution exponent separates digits. -/
theorem coeff_mul_expand_of_natDegree_lt {R : Type*} [CommSemiring R]
    {p : ℕ} (hp : 0 < p) (f g : R[X]) (hf : f.natDegree < p) (k : ℕ) :
    (f * Polynomial.expand R p g).coeff k = f.coeff (k % p) * g.coeff (k / p) := by
  classical
  rw [coeff_mul]
  rw [Finset.sum_eq_single (k % p, p * (k / p))]
  · rw [coeff_expand_mul' hp]
  · intro ij hij hne
    rcases ij with ⟨i, j⟩
    have hs : i + j = k := Finset.mem_antidiagonal.mp hij
    by_cases hi : i < p
    · rw [coeff_expand hp]
      have hj : ¬p ∣ j := by
        rintro ⟨r, rfl⟩
        apply hne
        have hmod : k % p = i := by
          rw [← hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
        have hdiv : k / p = r := by
          rw [← hs, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi, zero_add]
        simp only [hmod, hdiv]
      rw [if_neg hj, mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i), zero_mul]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (Nat.mod_add_div k p))).elim

end GaloisForLFunctions
