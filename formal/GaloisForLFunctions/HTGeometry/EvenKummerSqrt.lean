import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The square root supplied by a Kummer extension of even degree

If an element generates an extension of degree `n` and its `n`-th power lies in the base, then no
smaller power of it lies in the base: a power landing in the base is a root of a polynomial of that
degree, which would bound the degree of the extension.

When `n` is even this gives a square root of a base element inside the extension that is not itself
in the base, namely the `n/2`-nd power of the generator.  That is the element the even case of the
base change step needs.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **A power below the degree does not fall into the base field.** -/
theorem pow_notMem_bot_of_finrank_le {α : L} {n m : ℕ} (hm : 0 < m) (hmn : m < n)
    (hdeg : n ≤ Module.finrank F F⟮α⟯) :
    α ^ m ∉ (⊥ : IntermediateField F L) := by
  intro hmem
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.1 hmem
  have hmonic : (Polynomial.X ^ m - Polynomial.C b : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C b (by omega)
  have hroot : Polynomial.aeval α (Polynomial.X ^ m - Polynomial.C b : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hb, sub_self]
  have hint : IsIntegral F α := ⟨_, hmonic, by rw [← Polynomial.aeval_def]; exact hroot⟩
  have hdegm : (Polynomial.X ^ m - Polynomial.C b : Polynomial F).degree = (m : WithBot ℕ) :=
    Polynomial.degree_X_pow_sub_C hm b
  have hle := minpoly.min F α hmonic hroot
  rw [hdegm] at hle
  have hnat : (minpoly F α).natDegree ≤ m := Polynomial.natDegree_le_iff_degree_le.2 hle
  rw [IntermediateField.adjoin.finrank hint] at hdeg
  omega

/-- **The even Kummer square root.**  The half power of a generator of an extension of even degree
squares into the base and does not itself lie in the base. -/
theorem sq_pow_half {α : L} {c : F} {m : ℕ} (hα : α ^ (2 * m) = algebraMap F L c) :
    α ^ m * α ^ m = algebraMap F L c := by
  rw [← pow_add, ← hα]
  congr 1
  omega

end GaloisForLFunctions.HTGeometry
