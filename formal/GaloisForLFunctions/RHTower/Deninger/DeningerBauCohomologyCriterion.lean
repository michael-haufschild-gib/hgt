import GaloisForLFunctions.RHTower.Deninger.DeningerRetractCohomology
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagRationalProjective

/-!
# A cohomological criterion for the packet

The rationalization of a free group is a retract of any group with unique roots surjecting onto it,
so its cohomology vanishes in any degree in which that group's does.  For an empty index set the
rationalization is trivial and the cohomology vanishes outright.

* `deningerBauFree_isZero_cohomology_of_surjection` : the criterion.
* `deningerBauFree_isZero_cohomology_of_isEmpty` : the empty index set.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A cohomological criterion for the vanishing of the packet's cohomology.** -/
theorem deningerBauFree_isZero_cohomology_of_surjection (k : Type u) [CommRing k] {ι : Type u}
    {E : Type u} [Group E] (hE : DeningerUniquelyDivisible E)
    (π : E →* DeningerBau (FreeGroup ι)) (hπ : Function.Surjective π) (n : ℕ)
    (hzero : IsZero (groupCohomology (Rep.trivial k E k) n)) :
    IsZero (groupCohomology (Rep.trivial k (DeningerBau (FreeGroup ι)) k) n) := by
  obtain ⟨s, hs⟩ := deningerBauFree_projective hE π hπ
  exact deningerIsZero_of_retract_cohomology k π s hs n hzero

/-- **The packet's cohomology vanishes in positive degrees for an empty index set.** -/
theorem deningerBauFree_isZero_cohomology_of_isEmpty (k : Type u) [CommRing k] {ι : Type u}
    [IsEmpty ι] (n : ℕ) :
    IsZero (groupCohomology (Rep.trivial k (DeningerBau (FreeGroup ι)) k) (n + 1)) := by
  haveI : Subsingleton (FreeGroup ι) := by
    constructor
    intro x y
    have h : (MonoidHom.id (FreeGroup ι)) = (1 : FreeGroup ι →* FreeGroup ι) :=
      FreeGroup.ext_hom _ _ (fun i => (IsEmpty.false i).elim)
    have hx := congrArg (fun f : FreeGroup ι →* FreeGroup ι => f x) h
    have hy := congrArg (fun f : FreeGroup ι →* FreeGroup ι => f y) h
    simp only [MonoidHom.id_apply, MonoidHom.one_apply] at hx hy
    rw [hx, hy]
  haveI : Subsingleton (DeningerBau (FreeGroup ι)) := deningerBau_subsingleton
  exact isZero_groupCohomology_succ_of_subsingleton _ n

end RHTower
