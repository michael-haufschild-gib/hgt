import GaloisForLFunctions.RHTower.Deninger.DeningerRetractVanishing
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagRationalProjective

/-!
# A criterion for the vanishing of the homology of the rationalization

The rationalization of a free group is a retract of any group with unique roots surjecting onto it,
so its homology vanishes in any degree in which that group's does.  This reduces the vanishing for
the rationalization to the exhibition of a single acyclic group with unique roots mapping onto it.

* `deningerBauFree_isZero_of_surjection` : the criterion.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A criterion for the vanishing of the homology of the rationalization of a free group.** -/
theorem deningerBauFree_isZero_of_surjection (k : Type u) [CommRing k] {ι : Type u}
    {E : Type u} [Group E] (hE : DeningerUniquelyDivisible E)
    (π : E →* DeningerBau (FreeGroup ι)) (hπ : Function.Surjective π) (n : ℕ)
    (hzero : IsZero (groupHomology (Rep.trivial k E k) n)) :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup ι)) k) n) := by
  obtain ⟨s, hs⟩ := deningerBauFree_projective hE π hπ
  exact deningerIsZero_of_retract k π s hs n hzero

end RHTower
