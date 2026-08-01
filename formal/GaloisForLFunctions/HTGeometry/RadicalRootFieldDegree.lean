import GaloisForLFunctions.HTGeometry.RadicalBaseChangeCapstone
import Mathlib.FieldTheory.KummerExtension

/-!
# The degree of the root field of a radical polynomial

Over a field containing the roots of unity, the splitting field of an irreducible radical polynomial
has degree its exponent.  Inside a splitting field of a product, the root field of the radical factor
is such a splitting field.

So the parity of that degree is the parity of the exponent, which is what the odd case of the base
change step consumes.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The root field of an irreducible radical polynomial has degree the exponent.** -/
theorem finrank_rootField_X_pow_sub_C {p : Polynomial F} {c : F} {n : ℕ} (hp : p ≠ 0) (hn : 0 < n)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ n - Polynomial.C c))]
    (hζ : (primitiveRoots n F).Nonempty)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F)) :
    Module.finrank F (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)) = n := by
  have hq : (Polynomial.X ^ n - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  haveI := isSplittingField_rootField_right (L := L) hp hq
  exact finrank_of_isSplittingField_X_pow_sub_C hζ hirr
    (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c))

/-- **The odd hypothesis of the base change step, from the parity of the exponent.** -/
theorem not_two_dvd_finrank_rootField {p : Polynomial F} {c : F} {n : ℕ} (hp : p ≠ 0) (hn : 0 < n)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ n - Polynomial.C c))]
    (hζ : (primitiveRoots n F).Nonempty)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F))
    (hodd : ¬ 2 ∣ n) :
    ¬ 2 ∣ Module.finrank F (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)) := by
  rw [finrank_rootField_X_pow_sub_C hp hn hζ hirr]
  exact hodd

end GaloisForLFunctions.HTGeometry
