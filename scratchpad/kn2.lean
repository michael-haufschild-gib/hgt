import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- A coset of the stabiliser meeting a set is contained in it. -/
theorem smul_mulStab_subset_of_mem {s : Finset G} {x z : G} (hz : z ∈ s)
    (hx : x ∈ z • mulStab s) : x • mulStab s ⊆ s := by
  have h := (isSubgroupFinset_mulStab s).smul_eq_smul_of_mem hx
  rw [h]
  exact smul_mulStab_subset hz

/-- If `D` is a nonempty proper subset of a coset `w • S(C)` disjoint from `C`, then the
stabiliser of `C ∪ D` is the stabiliser of `D`, and this is a proper subgroup of `S(C)`. -/
theorem mulStab_union_coset {C D : Finset G} {w : G}
    (hD : D.Nonempty)
    (hDsub : D ⊆ w • mulStab C) (hDne : D ≠ w • mulStab C)
    (hdisj : Disjoint C (w • mulStab C)) :
    mulStab (C ∪ D) = mulStab D ∧ mulStab D ⊆ mulStab C ∧ mulStab D ≠ mulStab C := by
  classical
  set H := mulStab C with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab C
  have hcardH : (w • H).card = H.card := Finset.card_smul_finset _ _
  have hDlt : D.card < H.card := by
    rw [← hcardH]
    exact Finset.card_lt_card ⟨hDsub, fun h => hDne (Subset.antisymm hDsub h)⟩
  have hDpos : 0 < D.card := Finset.card_pos.2 hD
  -- `mulStab D ⊆ H`
  have hstabD : mulStab D ⊆ H := by
    intro j hj
    rw [mem_mulStab] at hj
    obtain ⟨d, hd⟩ := hD
    have hjd : j * d ∈ D := by
      rw [← hj]
      exact mem_smul_finset.2 ⟨d, hd, rfl⟩
    obtain ⟨h₁, hh₁, hh₁e⟩ := mem_smul_finset.1 (hDsub hd)
    obtain ⟨h₂, hh₂, hh₂e⟩ := mem_smul_finset.1 (hDsub hjd)
    have hjeq : j = h₂ * h₁⁻¹ := by
      have e1 : w * h₁ = d := hh₁e
      have e2 : w * h₂ = j * d := hh₂e
      rw [← e1] at e2
      have e3 : w * h₂ = w * (j * h₁) := by
        rw [e2, ← mul_assoc, ← mul_assoc, mul_comm j w]
      have e4 : h₂ = j * h₁ := mul_left_cancel e3
      rw [e4, mul_inv_cancel_right]
    rw [hjeq]
    exact hHgrp.mul_mem hh₂ (hHgrp.inv_mem hh₁)
  -- the intersection of `C ∪ D` with the coset is exactly `D`
  have hinter : (C ∪ D) ∩ (w • H) = D := by
    ext z
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hz | hz, hzc⟩
      · exact absurd hzc (Finset.disjoint_left.1 hdisj hz)
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, hDsub hz⟩
  -- `mulStab (C ∪ D) ⊆ H`
  have hstabU : mulStab (C ∪ D) ⊆ H := by
    intro j hj
    rw [mem_mulStab] at hj
    by_contra hjH
    have hne : (j * w) • H ≠ w • H := by
      intro hcon
      apply hjH
      have : j • (w • H) = w • H := by rw [← mul_smul]; exact hcon
      have h2 : w • (j • H) = w • H := by rw [smul_comm]; exact this
      have h3 : j • H = H := by
        have := congrArg (fun t : Finset G => w⁻¹ • t) h2
        simpa only [inv_smul_smul] using this
      exact hHgrp.mem_of_smul_eq h3
    have hkey : (C ∪ D) ∩ ((j * w) • H) = j • D := by
      have hsi : j • ((C ∪ D) ∩ (w • H)) = (j • (C ∪ D)) ∩ (j • (w • H)) :=
        Finset.smul_finset_inter
      rw [hinter, hj, ← mul_smul] at hsi
      exact hsi.symm
    have hcard1 : ((C ∪ D) ∩ ((j * w) • H)).card = D.card := by
      rw [hkey, Finset.card_smul_finset]
    -- but the intersection is `C ∩ (j*w) • H`, which is empty or the whole coset
    have hDdisj : Disjoint D ((j * w) • H) :=
      Finset.disjoint_of_subset_left hDsub (hHgrp.smul_coset_disjoint (Ne.symm hne))
    have hCU : (C ∪ D) ∩ ((j * w) • H) = C ∩ ((j * w) • H) := by
      ext z
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hz | hz, hzc⟩
        · exact ⟨hz, hzc⟩
        · exact absurd hzc (Finset.disjoint_left.1 hDdisj hz)
      · rintro ⟨hz, hzc⟩
        exact ⟨Or.inl hz, hzc⟩
    rcases Finset.eq_empty_or_nonempty (C ∩ ((j * w) • H)) with hemp | ⟨z, hz⟩
    · rw [hCU, hemp] at hcard1
      simp at hcard1
      omega
    · rw [mem_inter] at hz
      have hz1 : z • H ⊆ C := smul_mulStab_subset hz.1
      have hz2 : z • H = (j * w) • H := hHgrp.smul_eq_smul_of_mem hz.2
      have hsub : (j * w) • H ⊆ C := by rw [← hz2]; exact hz1
      have : C ∩ ((j * w) • H) = (j * w) • H := by
        exact Finset.inter_eq_right.2 hsub
      rw [hCU, this, Finset.card_smul_finset] at hcard1
      omega
  refine ⟨?_, hstabD, ?_⟩
  · -- `mulStab (C ∪ D) = mulStab D`
    apply Subset.antisymm
    · intro j hj
      have hjH : j ∈ H := hstabU hj
      rw [mem_mulStab] at hj ⊢
      have hjC : j • C = C := mem_mulStab.1 hjH
      have hCD : D = (C ∪ D) \ C := by
        ext z
        simp only [mem_sdiff, mem_union]
        constructor
        · intro hz
          exact ⟨Or.inr hz, fun hc => (Finset.disjoint_left.1 hdisj hc) (hDsub hz)⟩
        · rintro ⟨hz | hz, hnc⟩
          · exact absurd hz hnc
          · exact hz
      rw [hCD, Finset.smul_finset_sdiff, hj, hjC]
    · intro j hj
      have hjH : j ∈ H := hstabD hj
      rw [mem_mulStab] at hj ⊢
      have hjC : j • C = C := mem_mulStab.1 hjH
      rw [Finset.smul_finset_union, hjC, hj]
  · -- `mulStab D ≠ H`
    intro hcon
    apply hDne
    obtain ⟨d, hd⟩ := hD
    have h1 : d • mulStab D ⊆ D := smul_mulStab_subset hd
    rw [hcon] at h1
    have h2 : d • H = w • H := hHgrp.smul_eq_smul_of_mem (hDsub hd)
    rw [h2] at h1
    exact Subset.antisymm hDsub h1

end GaloisForLFunctions.HTGeometry.AddComb
