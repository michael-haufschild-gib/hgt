import GaloisForLFunctions.RHTower.Deninger.DeningerBauCyclic
import GaloisForLFunctions.RHTower.Deninger.DeningerBauTrivial

/-!
# The packet on an index set with at most one element

A free group on at most one generator is cyclic, so the packet's homology vanishes in degrees at
least two.  This settles clause (4) in all degrees for such index sets.

* `deningerBauFree_isZero_of_subsingleton` : the vanishing.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **The packet's homology vanishes in degrees at least two for an index set with at most one
element.** -/
theorem deningerBauFree_isZero_of_subsingleton (k : Type u) [CommRing k] {ι : Type u}
    [Subsingleton ι] (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (DeningerBau (FreeGroup ι)) k) (n + 2)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact deningerBauFree_isZero_of_isEmpty k (n + 1)
  · refine deningerBau_isZero_of_cyclic k (FreeGroup.of i₀) (fun a => ?_) n
    have htop : Subgroup.zpowers (FreeGroup.of i₀) = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← FreeGroup.closure_range_of ι]
      refine Subgroup.closure_le _ |>.2 ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨1, ?_⟩
      show (FreeGroup.of i₀) ^ (1 : ℤ) = FreeGroup.of i
      rw [zpow_one, Subsingleton.elim i₀ i]
    rw [htop]
    trivial

end RHTower
