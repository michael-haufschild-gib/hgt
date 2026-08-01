import GaloisForLFunctions.HTGeometry.KummerDegreeBound

/-!
# The degree of a radical extension with irreducible defining polynomial

If the radical polynomial is irreducible then it is the minimal polynomial of any of its roots, so
the extension a root generates has exactly its degree.

This turns irreducibility into the degree hypothesis of the base change step.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **A root of an irreducible radical polynomial generates an extension of its degree.** -/
theorem finrank_adjoin_of_irreducible {c : F} {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F))
    {α : L} (hα : α ^ n = algebraMap F L c) :
    Module.finrank F F⟮α⟯ = n := by
  have hmonic : (Polynomial.X ^ n - Polynomial.C c : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C c (by omega)
  have hroot : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C c : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα, sub_self]
  have hmin : minpoly F α = (Polynomial.X ^ n - Polynomial.C c : Polynomial F) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  have hint : IsIntegral F α := isIntegral_of_pow_mem hn hα
  rw [IntermediateField.adjoin.finrank hint, hmin, Polynomial.natDegree_X_pow_sub_C]

/-- **The degree hypothesis of the base change step, from irreducibility.** -/
theorem le_finrank_adjoin_of_irreducible {c : F} {n : ℕ} (hn : 0 < n)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F)) :
    ∀ α : L, α ^ n = algebraMap F L c → n ≤ Module.finrank F F⟮α⟯ :=
  fun _ hα => le_of_eq (finrank_adjoin_of_irreducible hn hirr hα).symm

end GaloisForLFunctions.HTGeometry
