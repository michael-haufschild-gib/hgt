import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# A square root outside the base forces an even degree

An element whose square lies in the base but which does not itself lie there generates a quadratic
subextension, so the degree of any extension containing it is even.

In particular a cyclic extension of odd degree contains no such square root, which is what settles
the odd case of the Kummer step with no discriminant computation at all.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- An element whose square is a scalar is integral. -/
theorem isIntegral_of_sq_mem_bot {δ : L} {c : F} (hsq : δ * δ = algebraMap F L c) :
    IsIntegral F δ := by
  refine ⟨Polynomial.X ^ (2 : ℕ) - Polynomial.C c, ?_, ?_⟩
  · refine (Polynomial.monic_X_pow 2).sub_of_left ?_
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      pow_two, hsq, sub_self]

/-- **A square root outside the base generates a quadratic subextension.** -/
theorem finrank_adjoin_eq_two {δ : L} {c : F} (hsq : δ * δ = algebraMap F L c)
    (hδ : δ ∉ (⊥ : IntermediateField F L)) :
    Module.finrank F F⟮δ⟯ = 2 := by
  have hint : IsIntegral F δ := isIntegral_of_sq_mem_bot hsq
  have hrank : Module.finrank F F⟮δ⟯ = (minpoly F δ).natDegree :=
    IntermediateField.adjoin.finrank hint
  have hdvd : minpoly F δ ∣ Polynomial.X ^ (2 : ℕ) - Polynomial.C c := by
    refine minpoly.dvd F δ ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, pow_two, hsq, sub_self]
  have hne : (Polynomial.X ^ (2 : ℕ) - Polynomial.C c : Polynomial F) ≠ 0 := by
    intro hcon
    have hdeg := congrArg Polynomial.natDegree hcon
    rw [Polynomial.natDegree_zero] at hdeg
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow] at hdeg
    exact absurd hdeg (by norm_num)
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hne
    rwa [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow] at h
  have hpos : 0 < (minpoly F δ).natDegree := minpoly.natDegree_pos hint
  have hne1 : (minpoly F δ).natDegree ≠ 1 := by
    intro hcon
    refine hδ ?_
    have hbot : F⟮δ⟯ = ⊥ := by
      refine IntermediateField.finrank_eq_one_iff.mp ?_
      rw [hrank, hcon]
    rw [← hbot]
    exact IntermediateField.mem_adjoin_simple_self F δ
  rw [hrank]
  omega

/-- **An extension containing a square root outside the base has even degree.** -/
theorem two_dvd_finrank_of_sq_mem_bot [FiniteDimensional F L] {δ : L} {c : F}
    (hsq : δ * δ = algebraMap F L c) (hδ : δ ∉ (⊥ : IntermediateField F L)) :
    2 ∣ Module.finrank F L := by
  have htower : Module.finrank F F⟮δ⟯ * Module.finrank F⟮δ⟯ L = Module.finrank F L :=
    Module.finrank_mul_finrank F F⟮δ⟯ L
  refine ⟨Module.finrank F⟮δ⟯ L, ?_⟩
  rw [← htower, finrank_adjoin_eq_two hsq hδ]

end GaloisForLFunctions.HTGeometry
