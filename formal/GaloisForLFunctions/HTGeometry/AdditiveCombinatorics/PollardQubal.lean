import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepThreePoly

/-!
# Periodicity of the full-translation set, and the condition (qubal)

`mulStab_dysonFull_eq`: the set `T = dysonFull A B` of translations carrying `B` inside `A` has
the same stabiliser as `T · B`.  One inclusion is `mulStab_subset_mulStab_mul`; the other holds
because `z · B ⊆ T · B` for `z ∈ T`, and `T · B` is `H`-stable.

`mem_dysonFull_of_card_ge` is the mechanism by which maximality of the Dyson witness is used: a
translate meeting `A` in at least `t` points must lie inside `A`, once the maximal small part has
fewer than `t` points.

`qubal` combines the two: if `B` is not contained in a single `H`-coset, every `H`-coset slice of
`B` has fewer than `t` points.  With `card_dysonFull_add_card_le` this gives Grynkiewicz's bound
`#T + #B + 1 ≤ #A + t`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- A stabiliser of a factor stabilises the product. -/
theorem mulStab_subset_mulStab_mul (X Y : Finset G) : mulStab X ⊆ mulStab (X * Y) := by
  intro g hg
  rw [mem_mulStab] at hg ⊢
  rw [← smul_mul_assoc, hg]

/-- **Maximality forces full translations.**  If the maximal Dyson small part has fewer than `t`
elements and some translate meets `A` in at least `t` points, then that translate lies inside
`A`. -/
theorem mem_dysonFull_of_card_ge {A B : Finset G} {x₀ y : G} {t : ℕ}
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hsmall : (dysonSmall A B x₀).card + 1 ≤ t)
    (hy : t ≤ (dysonSmall A B y).card) :
    y ∈ dysonFull A B := by
  classical
  by_contra hcon
  rw [mem_dysonFull] at hcon
  have hne : (dysonSmall A B y).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hsub : dysonSmall A B y ⊆ y • B := Finset.inter_subset_left
  have hcard : (y • B).card = B.card := Finset.card_smul_finset _ _
  have hlt : (dysonSmall A B y).card < B.card := by
    rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
    · omega
    · exfalso
      apply hcon
      have heq : dysonSmall A B y = y • B :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
      rw [← heq]
      exact Finset.inter_subset_right
  have := hmax y hne hlt
  omega

/-- **The set of full translations is periodic.**  The stabiliser of `dysonFull A B` coincides
with the stabiliser of `dysonFull A B · B`. -/
theorem mulStab_dysonFull_eq (A B : Finset G) :
    mulStab (dysonFull A B) = mulStab (dysonFull A B * B) := by
  classical
  set T := dysonFull A B with hTdef
  refine Subset.antisymm (mulStab_subset_mulStab_mul T B) (fun h hh => ?_)
  rw [mem_mulStab] at hh ⊢
  have hsub : h • T ⊆ T := by
    intro z hz
    rw [Finset.mem_smul_finset] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hTdef, mem_dysonFull] at hw ⊢
    intro u hu
    rw [Finset.mem_smul_finset] at hu
    obtain ⟨b, hb, rfl⟩ := hu
    have hmem : w • b ∈ T * B := mul_mem_mul (by rw [hTdef, mem_dysonFull]; exact hw) hb
    have hshift : (h • w) • b = h • (w • b) := by
      simp only [smul_eq_mul]
      rw [mul_assoc]
    rw [hshift]
    have : h • (w • b) ∈ h • (T * B) := Finset.smul_mem_smul_finset hmem
    rw [hh] at this
    exact dysonFull_mul_subset A B this
  have hcard : (h • T).card = T.card := Finset.card_smul_finset _ _
  exact Finset.eq_of_subset_of_card_le hsub (by omega)


/-- **Grynkiewicz's condition (qubal).**  If the maximal Dyson small part has fewer than `t`
elements and `B` is not contained in a single coset of `H = S(T · B)`, then every `H`-coset slice
of `B` has fewer than `t` points. -/
theorem qubal {A B : Finset G} {x₀ : G} {t : ℕ}
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hsmall : (dysonSmall A B x₀).card + 1 ≤ t)
    (hspread : ∀ c : G, ¬ (B ⊆ c • mulStab (dysonFull A B * B))) :
    ∀ b ∈ B, ((b • mulStab (dysonFull A B * B)) ∩ B).card + 1 ≤ t := by
  classical
  intro b₀ hb₀
  by_contra hcon
  push Not at hcon
  set T := dysonFull A B with hTdef
  set H := mulStab (T * B) with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (T * B)
  have hstabT : mulStab T = H := by rw [hTdef, hHdef, mulStab_dysonFull_eq A B]
  -- pick `b₁` outside the coset of `b₀`
  obtain ⟨b₁, hb₁B, hb₁⟩ : ∃ b₁ ∈ B, b₁ ∉ b₀ • H := by
    by_contra hall
    push Not at hall
    exact hspread b₀ (fun z hz => hall z hz)
  -- every translate of `T` by `b₁ b₀⁻¹` stays in `T`
  have hshift : ∀ z ∈ T, b₁ * b₀⁻¹ * z ∈ T := by
    intro z hz
    set y : G := b₁ * b₀⁻¹ * z with hydef
    have hsubA : y • ((b₀ • H) ∩ B) ⊆ dysonSmall A B y := by
      intro u hu
      rw [Finset.mem_smul_finset] at hu
      obtain ⟨b, hb, rfl⟩ := hu
      rw [Finset.mem_inter] at hb
      obtain ⟨hbH, hbB⟩ := hb
      obtain ⟨h, hh, hbh⟩ := Finset.mem_smul_finset.1 hbH
      rw [dysonSmall, Finset.mem_inter]
      refine ⟨Finset.smul_mem_smul_finset hbB, ?_⟩
      have hzb : z * b₁ ∈ T * B := mul_mem_mul hz hb₁B
      have hmem : (z * b₁) * h ∈ (T * B) * H := mul_mem_mul hzb hh
      rw [mul_mulStab] at hmem
      have hval : y • b = (z * b₁) * h := by
        simp only [hydef, smul_eq_mul] at hbh ⊢
        rw [← hbh]
        simp [mul_comm, mul_left_comm, mul_assoc]
      rw [hval]
      exact dysonFull_mul_subset A B hmem
    have hcardge : t ≤ (dysonSmall A B y).card := by
      have h1 : (y • ((b₀ • H) ∩ B)).card = ((b₀ • H) ∩ B).card :=
        Finset.card_smul_finset _ _
      have h2 := Finset.card_le_card hsubA
      omega
    exact mem_dysonFull_of_card_ge hmax hsmall hcardge
  -- hence `b₁ b₀⁻¹` stabilises `T`
  have hstabmem : b₁ * b₀⁻¹ ∈ mulStab T := by
    rw [mem_mulStab]
    have hsub : (b₁ * b₀⁻¹) • T ⊆ T := by
      intro z hz
      rw [Finset.mem_smul_finset] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hshift w hw
    have hcard : ((b₁ * b₀⁻¹) • T).card = T.card := Finset.card_smul_finset _ _
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [hstabT] at hstabmem
  apply hb₁
  rw [Finset.mem_smul_finset]
  refine ⟨b₀⁻¹ * b₁, ?_, by simp [smul_eq_mul, mul_inv_cancel_left]⟩
  have : b₀⁻¹ * b₁ = b₁ * b₀⁻¹ := mul_comm _ _
  rw [this]
  exact hstabmem

end GaloisForLFunctions.HTGeometry.AddComb
