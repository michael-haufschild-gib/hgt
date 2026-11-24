import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.ResidueCompression

/-! # Independent winding differences within residue classes -/

open Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

/-- Each residue class supplies one root. Every other index supplies a distinct
leaf whose winding difference from its root is divisible by the modulus. -/
theorem exists_residue_forest {I : Type*} [Fintype I] (z : I → ℤ) (d r : ℕ)
    (hr : (residues z d).card+1+r ≤ Fintype.card I) :
    ∃ leaf root : Fin r → I, Function.Injective leaf ∧
      (∀ i j, root i ≠ leaf j) ∧ ∀ i, (d:ℤ) ∣ z (leaf i)-z (root i) := by
  classical
  let f := fun i => z i % (d:ℤ)
  let S := univ.image f
  have pre (y : S) : ∃ i, f i=y.val := by
    obtain ⟨i,_,hi⟩ := mem_image.mp y.property
    exact ⟨i,hi⟩
  choose pick hp using pre
  let R : Finset I := univ.image pick
  have hR : R.card ≤ S.card := card_image_le.trans_eq (by simp)
  have hS : S.card ≤ (residues z d).card+1 := by
    change S.card ≤ (S.erase 0).card+1
    by_cases h : 0 ∈ S
    · exact (card_erase_add_one h).symm.le
    · rw [erase_eq_of_notMem h]; omega
  have hcard : Fintype.card (Fin r) ≤ Fintype.card ↥(Rᶜ) := by
    rw [Fintype.card_fin,Fintype.card_coe,card_compl]
    omega
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hcard
  let leaf (i : Fin r) := (j i).val
  let y (i : Fin r) : S := ⟨f (leaf i),mem_image.mpr ⟨leaf i,mem_univ _,rfl⟩⟩
  refine ⟨leaf,fun i => pick (y i),Subtype.val_injective.comp j.injective,?_,?_⟩
  · intro i k he
    change pick (y i)=leaf k at he
    have hm : pick (y i) ∈ R := mem_image.mpr ⟨y i,mem_univ _,rfl⟩
    rw [he] at hm
    exact (mem_compl.mp (j k).property) hm
  · intro i
    exact Int.modEq_iff_dvd.mp (hp (y i) : f (pick (y i))=f (leaf i))

#print axioms exists_residue_forest
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
