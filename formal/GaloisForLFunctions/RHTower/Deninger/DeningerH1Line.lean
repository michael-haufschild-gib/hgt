import GaloisForLFunctions.RHTower.Deninger.DeningerRegularH0

/-!
# A line, and surjections between lines

The first homology of an infinite cyclic group with trivial coefficients is a line: the two term
resolution identifies it with the zeroth homology of the regular representation, which is the ground
ring.  A surjection between lines over a field is injective, so a comparison map between the first
homologies of two infinite cyclic groups needs only to be surjective to be an isomorphism.

* `deningerZ_H1_isoK` : the first homology of an infinite cyclic group is a line.
* `deningerMono_of_epi_of_line` : a surjection between lines is injective.
* `deningerTransfer_comp_proj` : the transfer followed by the projection is the index.
-/

namespace RHTower

open CategoryTheory Rep

universe u

variable {Z : Type u} [Group Z] (e : Z ≃* Multiplicative ℤ) (k : Type u) [CommRing k]
  [DecidableEq Z]

/-- **The first homology of an infinite cyclic group is a line.** -/
noncomputable def deningerZ_H1_isoK :
    groupHomology (Rep.trivial k Z k) 1 ≅ ModuleCat.of k k :=
  deningerZ_H1Iso e k ≪≫ deningerRegularH0Iso k

/-- **A surjection between lines is injective.** -/
theorem deningerMono_of_epi_of_line {k : Type u} [Field k] {M N : ModuleCat.{u} k}
    (eM : M ≅ ModuleCat.of k k) (eN : N ≅ ModuleCat.of k k) (f : M ⟶ N) [Epi f] : Mono f := by
  have hcomp : f = eM.hom ≫ (eM.inv ≫ f ≫ eN.hom) ≫ eN.inv := by simp
  haveI : Mono (eM.inv ≫ f ≫ eN.hom) := by
    rw [ModuleCat.mono_iff_injective]
    refine LinearMap.injective_iff_surjective.2 ?_
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  rw [hcomp]
  infer_instance

section Transfer

variable {G : Type u} [Group G] {H B : Subgroup G} (hHB : H ≤ B)
  [Fintype (↥B ⧸ H.subgroupOf B)] (k : Type u) [CommRing k]

/-- **The transfer followed by the projection is the index.** -/
theorem deningerTransfer_comp_proj :
    deningerCosetTransfer (H := H) k ≫ deningerCosetProj k hHB =
      (Fintype.card (↥B ⧸ H.subgroupOf B)) • 𝟙 (Rep.ofMulAction k G (G ⧸ B)) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_))
  show (deningerCosetProj k hHB).hom ((deningerCosetTransfer (H := H) k).hom
    (MonoidAlgebra.single x (1 : k))) = _
  rw [deningerCosetTransfer, deningerPermHom_single, one_smul, deningerCosetProj_transfer]
  rfl

end Transfer

end RHTower
