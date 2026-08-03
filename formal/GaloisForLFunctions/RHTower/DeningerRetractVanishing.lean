import GaloisForLFunctions.RHTower.DeningerIndSubsingleton

/-!
# Vanishing passes to a retract

A group which is a retract of another has its homology a retract of the other's, so vanishing passes
to it.  Combined with the projectivity of the rationalization of a free group against surjections
from groups with unique roots, this reduces the vanishing for the rationalization to the vanishing
for any such group surjecting onto it.

* `deningerIsZero_of_retract` : vanishing passes to a retract.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Vanishing passes to a retract.** -/
theorem deningerIsZero_of_retract (k : Type u) [CommRing k] {G E : Type u} [Group G] [Group E]
    (π : E →* G) (s : G →* E) (hs : π.comp s = MonoidHom.id G) (n : ℕ)
    (hE : IsZero (groupHomology (Rep.trivial k E k) n)) :
    IsZero (groupHomology (Rep.trivial k G k) n) := by
  set φ : Rep.trivial k G k ⟶ Rep.res s (Rep.trivial k E k) := 𝟙 (Rep.trivial k G k) with hφ
  set ψ : Rep.trivial k E k ⟶ Rep.res π (Rep.trivial k G k) := 𝟙 (Rep.trivial k E k) with hψ
  have hcomp : groupHomology.map s φ n ≫ groupHomology.map π ψ n = 𝟙 _ := by
    rw [← groupHomology.map_comp s π φ ψ n, hs, hφ, hψ]
    have hres : Rep.resMap s (𝟙 (Rep.trivial k E k)) =
        𝟙 (Rep.res s (Rep.trivial k E k)) := rfl
    rw [hres, Category.comp_id]
    exact groupHomology.map_id
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← hcomp, hE.eq_zero_of_tgt (groupHomology.map s φ n), zero_comp]

end RHTower
