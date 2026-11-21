import Mathlib

/-!
# Ring isomorphisms of `ℚ`-algebras

A ring isomorphism between `ℚ`-algebras is automatically `ℚ`-linear.
-/

namespace RingEquiv

variable {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]

/-- Reinterpret a ring isomorphism of `ℚ`-algebras as a `ℚ`-algebra isomorphism. -/
def toRatAlgEquiv (f : R ≃+* S) : R ≃ₐ[ℚ] S :=
  { f with commutes' := (f : R →+* S).map_rat_algebraMap }

@[simp]
theorem toRatAlgEquiv_apply (f : R ≃+* S) (x : R) : f.toRatAlgEquiv x = f x := rfl

end RingEquiv
