import GaloisForLFunctions.HTGeometry.PaperNativeReesQuotient
import GaloisForLFunctions.HTGeometry.PaperHankelIdealOrders

/-!
# A nonnilpotent normal direction for every Hankel rank

Apply the source Rees coefficient kernel to the native Hankel ideal. The
principal determinant gives an actual element of the associated graded
ring. Every power remains nonzero: this is a persistent normal direction,
not merely a nonzero class in the first conormal quotient.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

noncomputable section

variable (K : Type*) [Field K]

/-- The principal determinant times the native Rees variable. -/
def paperHankelNativeNormalGenerator (r : ℕ) (extra : ℕ := 0) :
    reesAlgebra (finiteHankelSecantIdeal K (2 * r + 1 + extra) r) :=
  ReesGrading.mono _ 1 (paperHankelPrincipalMinor K r extra)
    (by simpa only [pow_one] using paperHankelPrincipalMinor_mem K r extra)

/-- The determinant's degree-one class in the actual associated graded ring. -/
def paperHankelNormalDirection (r : ℕ) (extra : ℕ := 0) :
    PaperIdealAssociatedGraded (finiteHankelSecantIdeal K (2 * r + 1 + extra) r) :=
  paperNativeReesSpecialization _ (paperHankelNativeNormalGenerator K r extra)

/-- Powers of the normal direction are the classes of the corresponding determinant powers. -/
theorem paperHankelNormalDirection_pow (r n : ℕ) (extra : ℕ := 0) :
    paperHankelNormalDirection K r extra ^ n =
      paperNativeReesSpecialization _
        (ReesGrading.mono _ n (paperHankelPrincipalMinor K r extra ^ n)
          (paperHankelPrincipalMinor_pow_mem K r n extra)) := by
  rw [paperHankelNormalDirection, ← map_pow]
  congr 1
  apply Subtype.ext
  change Polynomial.monomial 1 (paperHankelPrincipalMinor K r extra) ^ n =
    Polynomial.monomial n (paperHankelPrincipalMinor K r extra ^ n)
  rw [Polynomial.monomial_pow, one_mul]

/-- Every power survives, by the paper's exact coefficient-kernel theorem. -/
theorem paperHankelNormalDirection_pow_ne_zero (r n : ℕ) (extra : ℕ := 0) :
    paperHankelNormalDirection K r extra ^ n ≠ 0 := by
  rw [paperHankelNormalDirection_pow K r n extra]
  intro h
  exact paperHankelPrincipalMinor_pow_not_mem_succ K r n extra
    ((paperNativeReesSpecialization_mono_eq_zero_iff _ n
      ⟨_, paperHankelPrincipalMinor_pow_mem K r n extra⟩).mp h)

/-- In particular, the conormal direction itself is nonzero. -/
theorem paperHankelNormalDirection_ne_zero (r : ℕ) (extra : ℕ := 0) :
    paperHankelNormalDirection K r extra ≠ 0 := by
  simpa only [pow_one] using paperHankelNormalDirection_pow_ne_zero K r 1 extra

/-- The canonical normal direction is never nilpotent, over any field and at any rank. -/
theorem paperHankelNormalDirection_not_isNilpotent (r : ℕ) (extra : ℕ := 0) :
    ¬ IsNilpotent (paperHankelNormalDirection K r extra) := by
  rintro ⟨n, hn⟩
  exact paperHankelNormalDirection_pow_ne_zero K r n extra hn

end

end GaloisForLFunctions.HTGeometry
