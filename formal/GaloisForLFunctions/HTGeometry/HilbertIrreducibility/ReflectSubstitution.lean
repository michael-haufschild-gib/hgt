/-
# The substitution `X ↦ s₀ + T⁻¹` on a bivariate polynomial

Step 3 of Coleman--Zwald replaces the parameter `s` by `s₀ + 1/t` and clears the resulting negative
powers of `t`.  Composing `Polynomial.taylor s₀` with `Polynomial.reflect D` does exactly that:
`(reflect D (taylor s₀ c)).eval t = t ^ D * c.eval (t⁻¹ + s₀)`.

Because the base point `s₀` is taken in the *base ring* (in the application: an integer), the
substituted polynomial stays over the same ring, and no denominators are introduced.  Scaling by the
`(D * M)`-th power of `t` turns a monic relation for `w` at `s₀ + t⁻¹` into a monic relation for
`t ^ D * w` at `t`.
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GermIntegral

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- The `T`-polynomial obtained from `c` by the substitution `X ↦ s₀ + T⁻¹`, cleared by `T ^ D`. -/
noncomputable def shiftReflect (s₀ : R) (D : ℕ) (c : Polynomial R) : Polynomial R :=
  Polynomial.reflect D (Polynomial.taylor s₀ c)

omit [Algebra R ℂ] in
theorem natDegree_taylor_le (s₀ : R) (c : Polynomial R) :
    (Polynomial.taylor s₀ c).natDegree = c.natDegree :=
  Polynomial.natDegree_taylor c s₀

/-- **The substitution identity.** -/
theorem eval_shiftReflect (s₀ : R) (D : ℕ) (c : Polynomial R) (hc : c.natDegree ≤ D) {t : ℂ}
    (ht : t ≠ 0) :
    Polynomial.aeval t (shiftReflect s₀ D c) = t ^ D * Polynomial.aeval (t⁻¹ + algebraMap R ℂ s₀) c := by
  classical
  haveI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have hdeg : (Polynomial.taylor s₀ c).natDegree ≤ D := by
    rw [natDegree_taylor_le]; exact hc
  have hkey := Polynomial.eval₂_reflect_mul_pow (algebraMap R ℂ) (t⁻¹) D
    (Polynomial.taylor s₀ c) hdeg
  have hinvinv : (⅟(t⁻¹) : ℂ) = t :=
    invOf_eq_right_inv (by field_simp)
  rw [hinvinv] at hkey
  have htaylor : Polynomial.eval₂ (algebraMap R ℂ) (t⁻¹) (Polynomial.taylor s₀ c)
      = Polynomial.eval₂ (algebraMap R ℂ) (t⁻¹ + algebraMap R ℂ s₀) c := by
    rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
    simp
  rw [htaylor] at hkey
  have hpow : (t⁻¹ : ℂ) ^ D ≠ 0 := pow_ne_zero D (inv_ne_zero ht)
  have hfinal : Polynomial.eval₂ (algebraMap R ℂ) t (shiftReflect s₀ D c)
      = t ^ D * Polynomial.eval₂ (algebraMap R ℂ) (t⁻¹ + algebraMap R ℂ s₀) c := by
    rw [shiftReflect, ← hkey]
    have hone : (t : ℂ) ^ D * (t⁻¹) ^ D = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
    calc Polynomial.eval₂ (algebraMap R ℂ) t (Polynomial.reflect D (Polynomial.taylor s₀ c))
        = Polynomial.eval₂ (algebraMap R ℂ) t (Polynomial.reflect D (Polynomial.taylor s₀ c))
            * ((t : ℂ) ^ D * (t⁻¹) ^ D) := by rw [hone, mul_one]
      _ = t ^ D * (Polynomial.eval₂ (algebraMap R ℂ) t
            (Polynomial.reflect D (Polynomial.taylor s₀ c)) * (t⁻¹) ^ D) := by ring
  simpa [Polynomial.aeval_def] using hfinal

/-- The substituted polynomial: monic of the same degree, in the new variable `T`. -/
noncomputable def shiftedPoly (s₀ : R) (D M : ℕ) (P : Polynomial (Polynomial R)) :
    Polynomial (Polynomial R) :=
  Polynomial.X ^ M + ∑ j ∈ Finset.range M,
    Polynomial.C (shiftReflect s₀ D (P.coeff j) * Polynomial.X ^ (D * (M - 1 - j)))
      * Polynomial.X ^ j

omit [Algebra R ℂ] in
theorem natDegree_shiftedPoly_aux (s₀ : R) (D M : ℕ) (P : Polynomial (Polynomial R)) :
    (∑ j ∈ Finset.range M, Polynomial.C (shiftReflect s₀ D (P.coeff j)
      * Polynomial.X ^ (D * (M - 1 - j))) * Polynomial.X ^ j).degree < (M : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe M)).mpr fun j hj => ?_
  have hjM : j < M := Finset.mem_range.mp hj
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have h1 : (Polynomial.C (shiftReflect s₀ D (P.coeff j)
      * Polynomial.X ^ (D * (M - 1 - j)))).degree ≤ 0 := Polynomial.degree_C_le
  have h2 : ((Polynomial.X : Polynomial (Polynomial R)) ^ j).degree ≤ (j : WithBot ℕ) :=
    Polynomial.degree_X_pow_le j
  calc (Polynomial.C (shiftReflect s₀ D (P.coeff j) * Polynomial.X ^ (D * (M - 1 - j)))).degree
        + ((Polynomial.X : Polynomial (Polynomial R)) ^ j).degree
      ≤ 0 + (j : WithBot ℕ) := add_le_add h1 h2
    _ = (j : WithBot ℕ) := zero_add _
    _ < (M : WithBot ℕ) := by exact_mod_cast hjM

omit [Algebra R ℂ] in
theorem monic_shiftedPoly (s₀ : R) (D M : ℕ) (P : Polynomial (Polynomial R)) :
    (shiftedPoly s₀ D M P).Monic :=
  Polynomial.monic_X_pow_add (natDegree_shiftedPoly_aux s₀ D M P)

omit [Algebra R ℂ] in
theorem natDegree_shiftedPoly [Nontrivial R] (s₀ : R) (D M : ℕ)
    (P : Polynomial (Polynomial R)) : (shiftedPoly s₀ D M P).natDegree = M := by
  have h := natDegree_shiftedPoly_aux s₀ D M P
  rw [shiftedPoly]
  refine Polynomial.natDegree_eq_of_degree_eq_some ?_
  rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])]
  exact Polynomial.degree_X_pow M

/-- **The substituted relation.**  A relation for `w` at `s₀ + t⁻¹` becomes one for `t ^ D * w`
at `t`. -/
theorem bivEval_shiftedPoly (s₀ : R) (D M : ℕ) {P : Polynomial (Polynomial R)}
    (hD : ∀ j, (P.coeff j).natDegree ≤ D) (hM : P.natDegree = M) (hPmonic : P.Monic)
    {t w : ℂ} (ht : t ≠ 0) :
    bivEval (shiftedPoly s₀ D M P) t (t ^ D * w)
      = t ^ (D * M) * bivEval P (t⁻¹ + algebraMap R ℂ s₀) w := by
  classical
  set s : ℂ := t⁻¹ + algebraMap R ℂ s₀ with hs
  have hcoef : ∀ j, Polynomial.aeval t (shiftReflect s₀ D (P.coeff j))
      = t ^ D * Polynomial.aeval s (P.coeff j) := fun j =>
    eval_shiftReflect s₀ D (P.coeff j) (hD j) ht
  have hPM : Polynomial.aeval s (P.coeff M) = 1 := by
    rw [← hM, hPmonic.coeff_natDegree]
    simp
  have hRHS : bivEval P s w = ∑ j ∈ Finset.range (M + 1), Polynomial.aeval s (P.coeff j) * w ^ j := by
    rw [bivEval]
    exact Polynomial.eval₂_eq_sum_range' _ (by omega) _
  rw [shiftedPoly, bivEval, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, Polynomial.aeval_X_pow]
  rw [hRHS, Finset.sum_range_succ, mul_add, Finset.mul_sum, hPM]
  have hterm : ∀ j ∈ Finset.range M,
      Polynomial.aeval t (shiftReflect s₀ D (P.coeff j)) * t ^ (D * (M - 1 - j))
        * (t ^ D * w) ^ j
      = t ^ (D * M) * (Polynomial.aeval s (P.coeff j) * w ^ j) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    rw [hcoef j, mul_pow, ← pow_mul]
    have hexp : D + D * (M - 1 - j) + D * j = D * M := by
      have : 1 + (M - 1 - j) + j = M := by omega
      calc D + D * (M - 1 - j) + D * j = D * (1 + (M - 1 - j) + j) := by ring
        _ = D * M := by rw [this]
    calc t ^ D * Polynomial.aeval s (P.coeff j) * t ^ (D * (M - 1 - j)) * (t ^ (D * j) * w ^ j)
        = t ^ (D + D * (M - 1 - j) + D * j) * (Polynomial.aeval s (P.coeff j) * w ^ j) := by
          rw [pow_add, pow_add]; ring
      _ = t ^ (D * M) * (Polynomial.aeval s (P.coeff j) * w ^ j) := by rw [hexp]
  rw [Finset.sum_congr rfl hterm]
  have hlast : (t ^ D * w) ^ M = t ^ (D * M) * (1 * w ^ M) := by
    rw [mul_pow, ← pow_mul, one_mul]
  rw [hlast]
  ring

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
