import GaloisForLFunctions.RHTower.Deninger.DeningerH1Line

/-!
# The projection is split, and injective on first homology

Over a field in which the index is invertible, the transfer divided by the index splits the coset
projection, so the projection stays surjective after any functor.  When both subgroups are infinite
cyclic the first homologies are lines, and a surjection between lines is injective.

* `deningerCosetProj_isSplitEpi` : the projection is a split epimorphism.
* `deningerMono_map_proj` : it is injective on first homology.
-/

namespace RHTower

open CategoryTheory Rep

universe u

variable {G : Type u} [Group G] {H B : Subgroup G} (hHB : H ≤ B)
  [Fintype (↥B ⧸ H.subgroupOf B)] (k : Type u) [Field k]

/-- **The projection is a split epimorphism.** -/
theorem deningerCosetProj_isSplitEpi
    (hcard : (Fintype.card (↥B ⧸ H.subgroupOf B) : k) ≠ 0) :
    IsSplitEpi (deningerCosetProj k hHB) :=
  ⟨⟨(Fintype.card (↥B ⧸ H.subgroupOf B) : k)⁻¹ • deningerCosetTransfer (H := H) k, by
    rw [Linear.smul_comp, deningerTransfer_comp_proj,
      ← Nat.cast_smul_eq_nsmul k (Fintype.card (↥B ⧸ H.subgroupOf B))
        (𝟙 (Rep.ofMulAction k G (G ⧸ B))), smul_smul, inv_mul_cancel₀ hcard, one_smul]⟩⟩

theorem deningerEpi_map_proj (hcard : (Fintype.card (↥B ⧸ H.subgroupOf B) : k) ≠ 0) (n : ℕ) :
    Epi ((groupHomology.functor k G n).map (deningerCosetProj k hHB)) := by
  obtain ⟨⟨sec, hsec⟩⟩ := deningerCosetProj_isSplitEpi hHB k hcard
  haveI : IsSplitEpi ((groupHomology.functor k G n).map (deningerCosetProj k hHB)) :=
    ⟨⟨(groupHomology.functor k G n).map sec, by
      rw [← Functor.map_comp, hsec, CategoryTheory.Functor.map_id]⟩⟩
  infer_instance

section Cyclic

variable [DecidableEq G] [DecidableEq H] [DecidableEq B]

/-- **The projection is injective on first homology.** -/
theorem deningerMono_map_proj (hcard : (Fintype.card (↥B ⧸ H.subgroupOf B) : k) ≠ 0)
    (eH : H ≃* Multiplicative ℤ) (eB : B ≃* Multiplicative ℤ) :
    Mono ((groupHomology.functor k G 1).map (deningerCosetProj k hHB)) := by
  exact @deningerMono_of_epi_of_line k _ _ _
    (deningerPermutationShapiro H 1 ≪≫ deningerZ_H1_isoK eH k)
    (deningerPermutationShapiro B 1 ≪≫ deningerZ_H1_isoK eB k) _
    (deningerEpi_map_proj hHB k hcard 1)

end Cyclic

end RHTower
