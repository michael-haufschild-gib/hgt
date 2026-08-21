import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **Coset deficit estimate.**  If every point of `E` lying in the coset `v • H` already lies in
`Y`, then passing from the subgroup `H₁ ≤ H` to `H` gains at least `#H - #(Y * H₁)` points. -/
theorem coset_deficit {H H₁ E Y : Finset G} {v : G}
    (hH : IsSubgroupFinset H) (hH₁ : IsSubgroupFinset H₁) (hsub : H₁ ⊆ H)
    (hv : v ∈ E) (hY : Y ⊆ v • H)
    (hcover : ∀ x ∈ E, x ∈ v • H → x ∈ Y) :
    H.card + (E * H₁).card ≤ (E * H).card + (Y * H₁).card := by
  have hYH₁ : Y * H₁ ⊆ v • H := by
    calc Y * H₁ ⊆ (v • H) * H := mul_subset_mul hY hsub
      _ = v • (H * H) := smul_mul_assoc v H H
      _ = v • H := by rw [hH.mul_self]
  have hvHsub : v • H ⊆ E * H := by
    intro z hz
    rw [mem_smul_finset] at hz
    obtain ⟨h, hh, rfl⟩ := hz
    exact mul_mem_mul hv hh
  have hE₁sub : E * H₁ ⊆ E * H := mul_subset_mul_left hsub
  have hkey : (v • H) \ (Y * H₁) ⊆ (E * H) \ (E * H₁) := by
    intro z hz
    rw [mem_sdiff] at hz ⊢
    refine ⟨hvHsub hz.1, ?_⟩
    intro hcon
    apply hz.2
    rw [mem_mul] at hcon
    obtain ⟨x, hx, h₁, hh₁, rfl⟩ := hcon
    have hxv : x ∈ v • H := by
      have hmem : x * h₁ * h₁⁻¹ ∈ (v • H) * H := mul_mem_mul hz.1 (hsub (hH₁.inv_mem hh₁))
      rw [smul_mul_assoc, hH.mul_self] at hmem
      simpa using hmem
    exact mul_mem_mul (hcover x hx hxv) hh₁
  have c1 := Finset.card_le_card hkey
  have c2 := Finset.card_sdiff_add_card_eq_card hYH₁
  have c3 := Finset.card_sdiff_add_card_eq_card hE₁sub
  have c4 : (v • H).card = H.card := Finset.card_smul_finset _ _
  omega

end GaloisForLFunctions.HTGeometry.AddComb
