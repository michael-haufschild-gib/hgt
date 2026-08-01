import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The monic polynomial with indeterminate coefficients

Taking the coefficients themselves as variables gives the monic polynomial of degree `d` over the
polynomial ring in `d` indeterminates.  Its `k`-th coefficient is the `k`-th variable, it is monic,
and its degree is `d`.

Every monic polynomial of degree `d` is a specialisation of it, so statements about the change of
coefficients under a substitution can be proved once here.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [CommRing K] {d : ℕ}

/-- The monic polynomial whose coefficients are the variables. -/
noncomputable def universalMonic (K : Type*) [CommRing K] (d : ℕ) :
    Polynomial (MvPolynomial (Fin d) K) :=
  Polynomial.X ^ d + ∑ k : Fin d, Polynomial.C (MvPolynomial.X k) * Polynomial.X ^ (k : ℕ)

theorem coeff_universalMonic_lt {k : ℕ} (hk : k < d) :
    (universalMonic K d).coeff k = MvPolynomial.X (⟨k, hk⟩ : Fin d) := by
  classical
  rw [universalMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    Polynomial.finsetSum_coeff, zero_add, Finset.sum_eq_single (⟨k, hk⟩ : Fin d)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    intro hcon
    exact hb (Fin.ext hcon.symm)
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

theorem natDegree_universalMonic [Nontrivial K] (hd : 0 < d) :
    (universalMonic K d).natDegree = d := by
  rw [universalMonic]
  refine Polynomial.natDegree_add_eq_left_of_natDegree_lt ?_ |>.trans
    (Polynomial.natDegree_X_pow d)
  rw [Polynomial.natDegree_X_pow]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
  refine lt_of_le_of_lt (Finset.fold_max_le (b := d - 1) ?_) (by omega)
  refine ⟨by omega, fun i _ => ?_⟩
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.le_sub_one_of_lt i.2

theorem monic_universalMonic [Nontrivial K] (hd : 0 < d) : (universalMonic K d).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_universalMonic hd, universalMonic]
  classical
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl, Polynomial.finsetSum_coeff]
  have hzero : ∀ b : Fin d,
      (Polynomial.C (MvPolynomial.X b) * Polynomial.X ^ (b : ℕ) :
        Polynomial (MvPolynomial (Fin d) K)).coeff d = 0 := by
    intro b
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    intro hcon
    exact absurd (hcon ▸ b.2) (by omega)
  rw [Finset.sum_congr rfl (fun b _ => hzero b), Finset.sum_const_zero, add_zero]

end GaloisForLFunctions.HTGeometry
