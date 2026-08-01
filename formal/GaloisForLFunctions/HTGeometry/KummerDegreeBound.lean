import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The degree of a radical extension

An element whose `n`-th power lies in the base field is a root of a monic polynomial of degree `n`,
so the extension it generates has degree at most `n`.  Together with a lower bound from a group of
automorphisms this pins the degree of a Kummer extension exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem isIntegral_of_pow_mem {α : L} {c : F} {n : ℕ} (hn : 0 < n)
    (hα : α ^ n = algebraMap F L c) : IsIntegral F α :=
  ⟨Polynomial.X ^ n - Polynomial.C c, Polynomial.monic_X_pow_sub_C c (by omega), by
    rw [← Polynomial.aeval_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα,
      sub_self]⟩

/-- **A radical extension has degree at most the exponent.** -/
theorem finrank_adjoin_le_of_pow_mem {α : L} {c : F} {n : ℕ} (hn : 0 < n)
    (hα : α ^ n = algebraMap F L c) : Module.finrank F F⟮α⟯ ≤ n := by
  have hint : IsIntegral F α := isIntegral_of_pow_mem hn hα
  have hmonic : (Polynomial.X ^ n - Polynomial.C c : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C c (by omega)
  have hroot : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C c : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα, sub_self]
  have hle := minpoly.min F α hmonic hroot
  rw [Polynomial.degree_X_pow_sub_C hn c] at hle
  rw [IntermediateField.adjoin.finrank hint]
  exact Polynomial.natDegree_le_iff_degree_le.2 hle

end GaloisForLFunctions.HTGeometry
