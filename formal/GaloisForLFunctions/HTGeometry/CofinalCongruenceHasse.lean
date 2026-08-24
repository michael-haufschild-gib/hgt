import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineLattice

/-!
# Cofinal congruence Hasse principle for integers

Every finite collection of congruence observers has infinite fibres, but the cofinal family of all
moduli at least two separates integers.  This file packages the positive cofinal statement as a
Hasse family and extracts a concrete local modulus witness for every unequal pair.
-/

namespace GaloisForLFunctions.HTGeometry

/-- All congruence quotients of modulus at least two form a Hasse family for integers. -/
def integerCofinalCongruenceHasseFamily :
    HasseFamily ℤ {m : ℕ // 2 ≤ m} where
  Local m := ZMod m.1
  profile n m := n
  profile_injective := by
    intro n n' h
    exact cofinal_separating fun m hm => congrFun h ⟨m, hm⟩

/-- Integers agree globally exactly when they agree in every congruence quotient of modulus at
least two. -/
theorem integerCofinalCongruence_congr_hasse_iff (n n' : ℤ) :
    (∀ m : {m : ℕ // 2 ≤ m}, (n : ZMod m.1) = (n' : ZMod m.1)) ↔ n = n' :=
  integerCofinalCongruenceHasseFamily.pointwise_eq_iff n n'

/-- Every unequal pair of integers is distinguished by one finite congruence place. -/
theorem integerCofinalCongruence_ne_iff_exists_local_ne (n n' : ℤ) :
    n ≠ n' ↔ ∃ m : {m : ℕ // 2 ≤ m}, (n : ZMod m.1) ≠ (n' : ZMod m.1) :=
  integerCofinalCongruenceHasseFamily.ne_iff_exists_local_ne n n'

end GaloisForLFunctions.HTGeometry
