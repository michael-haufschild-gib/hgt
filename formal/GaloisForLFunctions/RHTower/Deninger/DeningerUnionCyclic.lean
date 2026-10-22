import GaloisForLFunctions.RHTower.Deninger.DeningerBauTrivial
import GaloisForLFunctions.RHTower.Deninger.DeningerHomologyUnion

/-!
# An increasing union of infinite cyclic subgroups

A group which is an increasing union of infinite cyclic subgroups has no homology in degrees at
least two: each stage is acyclic there, and a cycle lives in a stage.  The rationals are such a
union, and so is the rationalization of an infinite cyclic group.

* `deningerIsZero_of_iUnion_cyclic` : the vanishing.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **An increasing union of infinite cyclic subgroups has no homology in degrees at least two.** -/
theorem deningerIsZero_of_iUnion_cyclic (k G : Type u) [CommRing k] [Group G]
    (S : ℕ → Subgroup G) (hmono : Monotone S) (hunion : ∀ g : G, ∃ m, g ∈ S m)
    (hcyc : ∀ m, Nonempty ((S m) ≃* Multiplicative ℤ)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k G k) (n + 2)) := by
  classical
  refine deningerIsZero_of_iUnion k G S hmono hunion (n + 1) (fun m => ?_)
  obtain ⟨e⟩ := hcyc m
  exact deningerZ_isZero k e n

end RHTower
