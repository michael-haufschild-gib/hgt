import GaloisForLFunctions.RHTower.DeningerTreeHomology
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Vanishing of the homology of an amalgam

If the homology of the vertex module vanishes in degree `i` and that of the edge module vanishes in
degree `i - 1`, then the homology of the amalgam vanishes in degree `i`.  For a two factor amalgam
this reads: in degrees at least three, the homology of the amalgam vanishes as soon as it vanishes
for the two factors and the base group.

No knowledge of the maps in the long exact sequence is needed, only of the two neighbouring terms.

* `deningerIsZero_of_exact` : an exact short complex with zero ends has zero middle.
* `deningerAmalgam_isZero` : vanishing for the amalgam.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

theorem deningerIsZero_of_exact {C : Type*} [Category C] [Abelian C] {S : ShortComplex C}
    (hS : S.Exact) (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ := by
  have hf : S.f = 0 := h₁.eq_zero_of_src _
  haveI := hS.mono_g hf
  have hg : S.g = 0 := h₃.eq_zero_of_tgt _
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← cancel_mono S.g, hg, zero_comp, comp_zero]

theorem deningerIsZero_biprod {C : Type*} [Category C] [Abelian C] {A B : C}
    (hA : IsZero A) (hB : IsZero B) : IsZero (A ⊞ B) := by
  refine (IsZero.iff_id_eq_zero _).2 (biprod.hom_ext _ _ ?_ ?_)
  · rw [hA.eq_zero_of_tgt (𝟙 (A ⊞ B) ≫ biprod.fst), hA.eq_zero_of_tgt (0 ≫ biprod.fst)]
  · rw [hB.eq_zero_of_tgt (𝟙 (A ⊞ B) ≫ biprod.snd), hB.eq_zero_of_tgt (0 ≫ biprod.snd)]

variable {k G : Type u} [CommRing k] [Group G]

/-- **The middle term of the long exact sequence in group homology.**  If the homology of `X₂`
vanishes in degree `i` and that of `X₁` vanishes in degree `i - 1`, then the homology of `X₃`
vanishes in degree `i`. -/
theorem deningerGroupHomology_isZero_X₃ {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : j + 1 = i)
    (h₂ : IsZero (groupHomology X.X₂ i)) (h₁ : IsZero (groupHomology X.X₁ j)) :
    IsZero (groupHomology X.X₃ i) :=
  deningerIsZero_of_exact (groupHomology.mapShortComplex₃_exact hX hij) h₂ h₁

section Amalgam

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k] [DecidableEq (PushoutI φ)]

/-- **Vanishing for a two factor amalgam.**  If the homology of the base group and of the two
factors vanishes in degree `i`, and that of the base group also vanishes in degree `i - 1`, then the
homology of the amalgam vanishes in degree `i`. -/
theorem deningerAmalgam_isZero (hφ : ∀ i, Function.Injective (φ i)) (i j : ℕ) (hij : j + 1 = i)
    (hC : IsZero (groupHomology (Rep.trivial k ((PushoutI.base φ).range) k) i))
    (h0 : IsZero
      (groupHomology (Rep.trivial k ((PushoutI.of (φ := φ) (ULift.up true)).range) k) i))
    (h1 : IsZero
      (groupHomology (Rep.trivial k ((PushoutI.of (φ := φ) (ULift.up false)).range) k) i))
    (hCj : IsZero (groupHomology (Rep.trivial k ((PushoutI.base φ).range) k) j)) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) i) := by
  have hV : IsZero (groupHomology (deningerTreeVertexRep φ k) i) :=
    IsZero.of_iso (deningerIsZero_biprod hC (deningerIsZero_biprod h0 h1))
      (deningerTreeVertexHomologyIso k i)
  have hE : IsZero (groupHomology (deningerTreeEdgeRep φ k) j) :=
    IsZero.of_iso (deningerIsZero_biprod hCj hCj) (deningerTreeEdgeHomologyIso k j)
  exact deningerGroupHomology_isZero_X₃ (deningerTreeShortComplex_shortExact k hφ) i j hij hV hE

end Amalgam

end RHTower
