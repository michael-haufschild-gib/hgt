import GaloisForLFunctions.RHTower.Deninger.DeningerFreeProductRoots

/-!
# Vanishing passes to a retract

A group which is a retract of another has its homology a retract of the other's, so vanishing passes
to it.  The comparison of coefficients is made by the identity of the ground ring rather than by the
identity morphism of the trivial representation, which would ask for a definitional identification
of a restricted representation with a trivial one.

* `deningerTrivialRes` : the comparison of coefficients.
* `deningerIsZero_of_retract` : vanishing passes to a retract.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [CommRing k] {G E : Type u} [Group G] [Group E]

/-- The comparison of trivial coefficients along a group homomorphism. -/
noncomputable def deningerTrivialRes (s : G →* E) :
    Rep.trivial k G k ⟶ Rep.res s (Rep.trivial k E k) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- **Vanishing passes to a retract.** -/
theorem deningerIsZero_of_retract (π : E →* G) (s : G →* E)
    (hs : π.comp s = MonoidHom.id G) (n : ℕ)
    (hE : IsZero (groupHomology (Rep.trivial k E k) n)) :
    IsZero (groupHomology (Rep.trivial k G k) n) := by
  have hcomp : groupHomology.map s (deningerTrivialRes k s) n ≫
      groupHomology.map π (deningerTrivialRes k π) n = 𝟙 _ := by
    have h1 := groupHomology.map_comp s π (deningerTrivialRes k s) (deningerTrivialRes k π) n
    have h2 : groupHomology.map (π.comp s)
        (deningerTrivialRes k s ≫ (Rep.resFunctor s).map (deningerTrivialRes k π)) n =
        groupHomology.map (MonoidHom.id G) (deningerTrivialRes k (MonoidHom.id G)) n :=
      groupHomology.map_congr hs rfl n
    rw [← h1, h2]
    have h3 : groupHomology.map (MonoidHom.id G) (deningerTrivialRes k (MonoidHom.id G)) n =
        groupHomology.map (MonoidHom.id G) (𝟙 (Rep.trivial k G k)) n :=
      groupHomology.map_congr rfl rfl n
    rw [h3, groupHomology.map_id]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← hcomp, hE.eq_zero_of_tgt (groupHomology.map s (deningerTrivialRes k s) n), zero_comp]

end RHTower
