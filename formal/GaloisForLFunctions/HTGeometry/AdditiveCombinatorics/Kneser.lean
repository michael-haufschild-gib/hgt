import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Kneser's addition theorem

Kneser's theorem states that for nonempty finite subsets `A`, `B` of a commutative group, with
`H = S(A * B)` the stabiliser of the product set,

```
#(A * H) + #(B * H) ≤ #(A * B) + #H .
```

Mathlib contains the Cauchy--Davenport theorem
(`Mathlib/Combinatorics/Additive/CauchyDavenport.lean`) but not Kneser's theorem, and this corpus
did not contain it either.  This file supplies it for finite commutative groups, which is the
setting needed for the additive-combinatorial input of Matomäki--Teräväinen, *Linnik's problem for
multiplicative functions* (arXiv:2605.27833), where the ambient group is `ℤ_q^×`.

The proof is the short one of Matt DeVos, *A short proof of Kneser's addition theorem for abelian
groups* (arXiv:1303.3539): induction on `#(A * B) + #A`, first reducing to a trivial stabiliser by
passing to the quotient `G ⧸ S(A * B)`, and then running an intersection/union argument over
"convergent" subsets of `A * B`.

## Main results

* `mulStab_union_coset` — the stabiliser of `C ∪ D`, where `D` is a nonempty proper subset of a
  coset of `S(C)` disjoint from `C`, equals `S(D)`, a proper subgroup of `S(C)`.
* `kneser_core` — DeVos's main argument.
* `card_mul_le_card_mul_mulStab` — **Kneser's addition theorem**.
* `card_add_card_le_card_mul_add_card_mulStab` — its weak form `#A + #B ≤ #(A * B) + #S(A * B)`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

universe u

/-- Kneser's inequality for all pairs `(A, B)` with `#(A * B) + #A ≤ n`. -/
def KneserAt (n : ℕ) : Prop :=
  ∀ {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (A B : Finset G),
    A.Nonempty → B.Nonempty → (A * B).card + A.card ≤ n →
    (A * mulStab (A * B)).card + (B * mulStab (A * B)).card
      ≤ (A * B).card + (mulStab (A * B)).card

variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

/-- A set stabilised by `mulStab` is the full preimage of its image in the quotient. -/
theorem mem_iff_mk_mem_image (s : Finset G) [DecidableEq (G ⧸ stabSubgroup s)] (x : G) :
    x ∈ s ↔ (QuotientGroup.mk x : G ⧸ stabSubgroup s)
      ∈ s.image (fun g : G => (QuotientGroup.mk g : G ⧸ stabSubgroup s)) := by
  constructor
  · intro hx; exact mem_image_of_mem _ hx
  · intro hx
    rw [mem_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hmem : y⁻¹ * x ∈ stabSubgroup s := by
      rw [← QuotientGroup.eq (s := stabSubgroup s)]
      exact hxy
    have : y * (y⁻¹ * x) ∈ s * mulStab s :=
      mul_mem_mul hy (by rw [mem_mulStab]; exact hmem)
    rw [mul_mulStab, mul_inv_cancel_left] at this
    exact this


/-- **Quotient reduction.**  When the stabiliser of `A * B` is nontrivial, Kneser's inequality
for `(A, B)` follows from the inequality for the images of `A` and `B` in `G ⧸ S(A * B)`. -/
theorem kneser_quotient (n : ℕ) (IH : ∀ m, m < n → KneserAt.{u} m)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hn : (A * B).card + A.card ≤ n) (hK : 1 < (mulStab (A * B)).card) :
    (A * mulStab (A * B)).card + (B * mulStab (A * B)).card
      ≤ (A * B).card + (mulStab (A * B)).card := by
  classical
  have hKN : ∀ g : G, g ∈ mulStab (A * B) ↔ g ∈ stabSubgroup (A * B) := by
    intro g; simp
  haveI : Finite (G ⧸ stabSubgroup (A * B)) :=
    Finite.of_surjective (QuotientGroup.mk : G → G ⧸ stabSubgroup (A * B))
      QuotientGroup.mk_surjective
  letI : Fintype (G ⧸ stabSubgroup (A * B)) := Fintype.ofFinite _
  letI : DecidableEq (G ⧸ stabSubgroup (A * B)) := Classical.decEq _
  set A' : Finset (G ⧸ stabSubgroup (A * B)) :=
    A.image (fun g : G => (QuotientGroup.mk g : G ⧸ stabSubgroup (A * B))) with hA'def
  set B' : Finset (G ⧸ stabSubgroup (A * B)) :=
    B.image (fun g : G => (QuotientGroup.mk g : G ⧸ stabSubgroup (A * B))) with hB'def
  have himg : (A * B).image (fun g : G => (QuotientGroup.mk g : G ⧸ stabSubgroup (A * B)))
      = A' * B' := Finset.image_mul (QuotientGroup.mk' (stabSubgroup (A * B)))
  have hcA : (A * mulStab (A * B)).card = (mulStab (A * B)).card * A'.card :=
    card_mul_subgroupFinset_eq _ A _ hKN
  have hcB : (B * mulStab (A * B)).card = (mulStab (A * B)).card * B'.card :=
    card_mul_subgroupFinset_eq _ B _ hKN
  have hcAB : (A * B).card = (mulStab (A * B)).card * (A' * B').card := by
    have h := card_mul_subgroupFinset_eq (stabSubgroup (A * B)) (A * B) (mulStab (A * B)) hKN
    rwa [mul_mulStab, himg] at h
  have hA'ne : A'.Nonempty := hA.image _
  have hB'ne : B'.Nonempty := hB.image _
  have hprodne : (A' * B').Nonempty := hA'ne.mul hB'ne
  have hiff : ∀ z : G, z ∈ A * B ↔
      (QuotientGroup.mk z : G ⧸ stabSubgroup (A * B)) ∈ A' * B' := by
    intro z; rw [← himg]; exact mem_iff_mk_mem_image (A * B) z
  have hstabtriv : mulStab (A' * B') = {1} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨by simp, ?_⟩
    intro x hx
    rw [mem_mulStab] at hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hgstab : g • (A * B) = A * B := by
      ext y
      simp only [mem_smul_finset, smul_eq_mul]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hiff]
        have hz' := (hiff z).1 hz
        have hmk : (QuotientGroup.mk (g * z) : G ⧸ stabSubgroup (A * B))
            = (QuotientGroup.mk g : G ⧸ stabSubgroup (A * B))
              • (QuotientGroup.mk z : G ⧸ stabSubgroup (A * B)) := by
          rw [smul_eq_mul]; rfl
        rw [hmk, ← hx]
        exact mem_smul_finset.2 ⟨_, hz', rfl⟩
      · intro hy
        refine ⟨g⁻¹ * y, ?_, mul_inv_cancel_left g y⟩
        rw [hiff]
        have hy' := (hiff y).1 hy
        rw [← hx, mem_smul_finset] at hy'
        obtain ⟨w, hw, hwy⟩ := hy'
        have heq : (QuotientGroup.mk (g⁻¹ * y) : G ⧸ stabSubgroup (A * B)) = w := by
          have h1 : (QuotientGroup.mk (g⁻¹ * y) : G ⧸ stabSubgroup (A * B))
              = (QuotientGroup.mk g : G ⧸ stabSubgroup (A * B))⁻¹
                * (QuotientGroup.mk y : G ⧸ stabSubgroup (A * B)) := rfl
          rw [h1, ← hwy, smul_eq_mul, inv_mul_cancel_left]
        rw [heq]; exact hw
    have hgm : g ∈ stabSubgroup (A * B) := hgstab
    exact (QuotientGroup.eq_one_iff g).2 hgm
  have hlt : (A' * B').card + A'.card < n := by
    have h1 : 1 ≤ (A' * B').card := Finset.card_pos.2 hprodne
    have h2 : (A' * B').card < (A * B).card := by
      rw [hcAB]
      calc (A' * B').card = 1 * (A' * B').card := (one_mul _).symm
        _ < (mulStab (A * B)).card * (A' * B').card :=
            (Nat.mul_lt_mul_right (by omega : 0 < (A' * B').card)).2 hK
    have h3 : A'.card ≤ A.card := Finset.card_image_le
    omega
  have hIH := IH _ hlt A' B' hA'ne hB'ne le_rfl
  rw [hstabtriv] at hIH
  have hone : ({1} : Finset (G ⧸ stabSubgroup (A * B))) = 1 := rfl
  rw [hone, mul_one, mul_one, Finset.card_one] at hIH
  rw [hcA, hcB, hcAB]
  calc (mulStab (A * B)).card * A'.card + (mulStab (A * B)).card * B'.card
      = (mulStab (A * B)).card * (A'.card + B'.card) := by ring
    _ ≤ (mulStab (A * B)).card * ((A' * B').card + 1) := Nat.mul_le_mul_left _ hIH
    _ = (mulStab (A * B)).card * (A' * B').card + (mulStab (A * B)).card := by ring


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


omit [Fintype G] in
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



section Core

variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **DeVos's argument.**  When the stabiliser of `A * B` is trivial and `A ∩ B` is a nonempty
proper subset of `A`, the Cauchy--Davenport bound `#A + #B ≤ #(A * B) + 1` holds. -/
theorem kneser_core (n : ℕ) (IH : ∀ m, m < n → KneserAt.{u} m)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hn : (A * B).card + A.card ≤ n)
    (hK : mulStab (A * B) = {1})
    (hABne : (A ∩ B).Nonempty) (hABlt : (A ∩ B).card < A.card) :
    A.card + B.card ≤ (A * B).card + 1 := by
  classical
  have hABprod : (A * B).Nonempty := hA.mul hB
  have hUne : (A ∪ B).Nonempty := Finset.Nonempty.mono Finset.subset_union_left hA
  have hcardIU : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hone : ({1} : Finset G) = 1 := rfl
  -- The set of convergents.
  set 𝒞 : Finset (Finset G) := (A * B).powerset.filter
    (fun C => C.Nonempty ∧
      (A ∩ B).card + ((A ∪ B) * (mulStab C)).card ≤ C.card + (mulStab C).card) with h𝒞def
  have hmem𝒞 : ∀ C : Finset G, C ∈ 𝒞 ↔ (C ⊆ A * B ∧ C.Nonempty ∧
      (A ∩ B).card + ((A ∪ B) * (mulStab C)).card ≤ C.card + (mulStab C).card) := by
    intro C
    rw [h𝒞def, Finset.mem_filter, Finset.mem_powerset]
  -- `(A ∩ B) * (A ∪ B)` is a convergent.
  have hC₀sub : (A ∩ B) * (A ∪ B) ⊆ A * B := by
    intro x hx
    rw [mem_mul] at hx ⊢
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    rw [Finset.mem_inter] at hp
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact ⟨q, hq, p, hp.2, mul_comm q p⟩
    · exact ⟨p, hp.1, q, hq, rfl⟩
  have hC₀ : (A ∩ B) * (A ∪ B) ∈ 𝒞 := by
    rw [hmem𝒞]
    refine ⟨hC₀sub, hABne.mul hUne, ?_⟩
    have hmeas : ((A ∩ B) * (A ∪ B)).card + (A ∩ B).card < n := by
      have h1 : ((A ∩ B) * (A ∪ B)).card ≤ (A * B).card := Finset.card_le_card hC₀sub
      omega
    have hIHC := IH _ hmeas (A ∩ B) (A ∪ B) hABne hUne le_rfl
    have hsub2 : (A ∩ B).card ≤ ((A ∩ B) * mulStab ((A ∩ B) * (A ∪ B))).card :=
      Finset.card_le_card ((isSubgroupFinset_mulStab _).subset_mul _)
    omega
  obtain ⟨C, hC𝒞, hCmin⟩ := Finset.exists_min_image 𝒞 (fun C => (mulStab C).card) ⟨_, hC₀⟩
  rw [hmem𝒞] at hC𝒞
  obtain ⟨hCsub, hCne, hCconv⟩ := hC𝒞
  by_cases hH1 : (mulStab C).card = 1
  · -- The stabiliser of the convergent is trivial: we are done.
    have hHeq : (mulStab C) = {1} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hH1
      have h1 : (1 : G) ∈ (mulStab C) := by simp
      rw [hx, Finset.mem_singleton] at h1
      rw [hx, h1]
    rw [hHeq, hone, mul_one, Finset.card_one] at hCconv
    have hCle : C.card ≤ (A * B).card := Finset.card_le_card hCsub
    omega
  · exfalso
    have hHgrp : IsSubgroupFinset (mulStab C) := isSubgroupFinset_mulStab C
    have hHcard : 2 ≤ (mulStab C).card := by
      have := (isSubgroupFinset_mulStab C).card_pos'
      omega
    obtain ⟨h₀, hh₀H, hh₀ne⟩ : ∃ h ∈ (mulStab C), h ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (mulStab C) ⊆ {1} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      omega
    have hnotstab : h₀ • (A * B) ≠ A * B := by
      intro hcon
      have hm : h₀ ∈ mulStab (A * B) := mem_mulStab.2 hcon
      rw [hK, Finset.mem_singleton] at hm
      exact hh₀ne hm
    obtain ⟨c, hc, hcnot⟩ : ∃ c ∈ A * B, h₀ * c ∉ A * B := by
      by_contra hcon
      push Not at hcon
      apply hnotstab
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rw [mem_smul_finset] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact hcon y hy
      · rw [Finset.card_smul_finset]
    obtain ⟨a, ha, b, hb, hab⟩ := mem_mul.1 hc
    have hcosetnotsub : ¬ ((a * b) • (mulStab C) ⊆ A * B) := by
      intro hcon
      apply hcnot
      have hmm : a * b * h₀ ∈ (a * b) • (mulStab C) := mem_smul_finset.2 ⟨h₀, hh₀H, rfl⟩
      have heq : h₀ * c = a * b * h₀ := by rw [mul_comm h₀ c, ← hab]
      rw [heq]
      exact hcon hmm
    have hCdisj : Disjoint C ((a * b) • (mulStab C)) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      apply hcosetnotsub
      have h1 : z • (mulStab C) ⊆ C := smul_mulStab_subset hz
      have h2 : z • (mulStab C) = (a * b) • (mulStab C) := hHgrp.smul_eq_smul_of_mem hz'
      rw [← h2]
      exact fun x hx => hCsub (h1 hx)
    have hHleC : (mulStab C).card ≤ C.card := by
      obtain ⟨z, hz⟩ := hCne
      have h1 : z • (mulStab C) ⊆ C := smul_mulStab_subset hz
      have h2 := Finset.card_le_card h1
      rwa [Finset.card_smul_finset] at h2
    have hCle : C.card ≤ (A * B).card := Finset.card_le_card hCsub
    -- The uniform package of facts attached to a pair of coset pieces.
    have main : ∀ (X Y : Finset G) (u v : G), X ⊆ A → Y ⊆ B → X.Nonempty → Y.Nonempty →
        X ⊆ u • (mulStab C) → Y ⊆ v • (mulStab C) → u * v = a * b →
        mulStab (X * Y) ⊆ (mulStab C)
        ∧ X.card + Y.card + (mulStab (X * Y)).card ≤ (mulStab C).card
        ∧ ((A ∪ B) * (mulStab C)).card + (X * mulStab (X * Y)).card + (Y * mulStab (X * Y)).card
            < (mulStab C).card + ((A ∪ B) * mulStab (X * Y)).card
        ∧ X.card + Y.card ≤ (X * Y).card + (mulStab (X * Y)).card
        ∧ (X * Y).card + C.card ≤ (A * B).card := by
      intro X Y u v hXA hYB hXne hYne hXu hYv huv
      have hDne : (X * Y).Nonempty := hXne.mul hYne
      have hDsub : X * Y ⊆ (a * b) • (mulStab C) := by
        calc X * Y ⊆ (u • (mulStab C)) * (v • (mulStab C)) := mul_subset_mul hXu hYv
          _ = (u * v) • ((mulStab C) * (mulStab C)) := smul_mul_smul u (mulStab C) v (mulStab C)
          _ = (a * b) • (mulStab C) := by rw [hHgrp.mul_self, huv]
      have hDAB : X * Y ⊆ A * B := mul_subset_mul hXA hYB
      have hDne2 : X * Y ≠ (a * b) • (mulStab C) := by
        intro hcon
        exact hcosetnotsub (hcon ▸ hDAB)
      obtain ⟨hstabU, hstabsub, hstabne⟩ := mulStab_union_coset hDne hDsub hDne2 hCdisj
      have hHigrp : IsSubgroupFinset (mulStab (X * Y)) := isSubgroupFinset_mulStab (X * Y)
      have hHilt : (mulStab (X * Y)).card < (mulStab C).card :=
        Finset.card_lt_card ⟨hstabsub, fun h => hstabne (Subset.antisymm hstabsub h)⟩
      have hCDdisj : Disjoint C (X * Y) := Finset.disjoint_of_subset_right hDsub hCdisj
      have hP4 : (X * Y).card + C.card ≤ (A * B).card := by
        have hu : (C ∪ (X * Y)).card = C.card + (X * Y).card :=
          Finset.card_union_of_disjoint hCDdisj
        have hsub : C ∪ (X * Y) ⊆ A * B := Finset.union_subset hCsub hDAB
        have := Finset.card_le_card hsub
        omega
      have hDcardlt : (X * Y).card < (mulStab C).card := by
        have h1 : ((a * b) • (mulStab C)).card = (mulStab C).card := Finset.card_smul_finset _ _
        have h2 := Finset.card_lt_card
          (⟨hDsub, fun h => hDne2 (Subset.antisymm hDsub h)⟩ : X * Y ⊂ (a * b) • (mulStab C))
        omega
      have hmeas : (X * Y).card + X.card < n := by
        have h2 : X.card ≤ A.card := Finset.card_le_card hXA
        omega
      have hIHXY := IH _ hmeas X Y hXne hYne le_rfl
      have hXHi : X.card ≤ (X * mulStab (X * Y)).card :=
        Finset.card_le_card (hHigrp.subset_mul X)
      have hYHi : Y.card ≤ (Y * mulStab (X * Y)).card :=
        Finset.card_le_card (hHigrp.subset_mul Y)
      have hCD𝒞 : C ∪ (X * Y) ∉ 𝒞 := by
        intro hcon
        have hle := hCmin _ hcon
        rw [hstabU] at hle
        omega
      have hnotconv : (C ∪ (X * Y)).card + (mulStab (C ∪ (X * Y))).card
          < (A ∩ B).card + ((A ∪ B) * mulStab (C ∪ (X * Y))).card := by
        by_contra hcon
        push Not at hcon
        exact hCD𝒞 ((hmem𝒞 _).2
          ⟨Finset.union_subset hCsub hDAB, hCne.mono Finset.subset_union_left, hcon⟩)
      rw [hstabU, Finset.card_union_of_disjoint hCDdisj] at hnotconv
      have hP3 : ((A ∪ B) * (mulStab C)).card + (X * mulStab (X * Y)).card
          + (Y * mulStab (X * Y)).card < (mulStab C).card + ((A ∪ B) * mulStab (X * Y)).card := by
        omega
      have hP5 : X.card + Y.card + (mulStab (X * Y)).card ≤ (mulStab C).card := by
        have hmono : ((A ∪ B) * mulStab (X * Y)).card ≤ ((A ∪ B) * (mulStab C)).card :=
          Finset.card_le_card (mul_subset_mul_left hstabsub)
        have hlt : (X * mulStab (X * Y)).card + (Y * mulStab (X * Y)).card < (mulStab C).card := by omega
        have d1 : (mulStab (X * Y)).card ∣ (mulStab C).card :=
          hHgrp.card_dvd_card_of_subset hHigrp hstabsub
        have d2 : (mulStab (X * Y)).card ∣ (X * mulStab (X * Y)).card :=
          hHigrp.card_dvd_card_mul X
        have d3 : (mulStab (X * Y)).card ∣ (Y * mulStab (X * Y)).card :=
          hHigrp.card_dvd_card_mul Y
        have d4 : (mulStab (X * Y)).card ∣
            (mulStab C).card - ((X * mulStab (X * Y)).card + (Y * mulStab (X * Y)).card) :=
          Nat.dvd_sub d1 (Nat.dvd_add d2 d3)
        have d5 : (mulStab (X * Y)).card
            ≤ (mulStab C).card - ((X * mulStab (X * Y)).card + (Y * mulStab (X * Y)).card) :=
          Nat.le_of_dvd (by omega) d4
        omega
      exact ⟨hstabsub, hP5, hP3, by omega, hP4⟩
    -- The four coset pieces.
    have hA₁ne : (A ∩ (a • (mulStab C))).Nonempty := ⟨a, Finset.mem_inter.2 ⟨ha, hHgrp.mem_smul_self a⟩⟩
    have hB₁ne : (B ∩ (b • (mulStab C))).Nonempty := ⟨b, Finset.mem_inter.2 ⟨hb, hHgrp.mem_smul_self b⟩⟩
    obtain ⟨m1sub, m1P5, m1P3, m1P6, m1P4⟩ :=
      main (A ∩ (a • (mulStab C))) (B ∩ (b • (mulStab C))) a b Finset.inter_subset_left Finset.inter_subset_left
        hA₁ne hB₁ne Finset.inter_subset_right Finset.inter_subset_right rfl
    -- `B ∩ a • H` is nonempty.
    have hB₂ne : (B ∩ (a • (mulStab C))).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (B ∩ (a • (mulStab C))) with hemp | h
      · exfalso
        have hcover : ∀ x ∈ A ∪ B, x ∈ a • (mulStab C) → x ∈ A ∩ (a • (mulStab C)) := by
          intro x hx hxa
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact Finset.mem_inter.2 ⟨hx, hxa⟩
          · exact absurd (Finset.mem_inter.2 ⟨hx, hxa⟩ : x ∈ B ∩ (a • (mulStab C)))
              (by rw [hemp]; exact Finset.notMem_empty x)
        have hd := coset_deficit hHgrp (isSubgroupFinset_mulStab _) m1sub
          (Finset.mem_union_left _ ha) Finset.inter_subset_right hcover
        omega
      · exact h
    have hA₂ne : (A ∩ (b • (mulStab C))).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (A ∩ (b • (mulStab C))) with hemp | h
      · exfalso
        have hcover : ∀ x ∈ A ∪ B, x ∈ b • (mulStab C) → x ∈ B ∩ (b • (mulStab C)) := by
          intro x hx hxb
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact absurd (Finset.mem_inter.2 ⟨hx, hxb⟩ : x ∈ A ∩ (b • (mulStab C)))
              (by rw [hemp]; exact Finset.notMem_empty x)
          · exact Finset.mem_inter.2 ⟨hx, hxb⟩
        have hd := coset_deficit hHgrp (isSubgroupFinset_mulStab _) m1sub
          (Finset.mem_union_right _ hb) Finset.inter_subset_right hcover
        omega
      · exact h
    -- The two cosets are distinct.
    have hcosetne : a • (mulStab C) ≠ b • (mulStab C) := by
      intro heq
      have hcover : ∀ x ∈ A ∪ B, x ∈ a • (mulStab C) → x ∈ (A ∩ (a • (mulStab C))) ∪ (B ∩ (b • (mulStab C))) := by
        intro x hx hxa
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hx, hxa⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, heq ▸ hxa⟩)
      have hYsub : (A ∩ (a • (mulStab C))) ∪ (B ∩ (b • (mulStab C))) ⊆ a • (mulStab C) := by
        refine Finset.union_subset Finset.inter_subset_right ?_
        rw [heq]; exact Finset.inter_subset_right
      have hd := coset_deficit hHgrp (isSubgroupFinset_mulStab _) m1sub
        (Finset.mem_union_left _ ha) hYsub hcover
      have hsplit : (((A ∩ (a • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))
            * mulStab ((A ∩ (a • (mulStab C))) * (B ∩ (b • (mulStab C))))).card
          ≤ ((A ∩ (a • (mulStab C))) * mulStab ((A ∩ (a • (mulStab C))) * (B ∩ (b • (mulStab C))))).card
            + ((B ∩ (b • (mulStab C))) * mulStab ((A ∩ (a • (mulStab C))) * (B ∩ (b • (mulStab C))))).card := by
        rw [Finset.union_mul]
        exact Finset.card_union_le _ _
      omega
    obtain ⟨m2sub, m2P5, m2P3, m2P6, m2P4⟩ :=
      main (A ∩ (b • (mulStab C))) (B ∩ (a • (mulStab C))) b a Finset.inter_subset_left Finset.inter_subset_left
        hA₂ne hB₂ne Finset.inter_subset_right Finset.inter_subset_right (mul_comm b a)
    -- The two leftover pieces.
    have hcov1 : (mulStab C).card ≤ ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))).card
        + (A ∩ (a • (mulStab C))).card + (B ∩ (a • (mulStab C))).card := by
      have hsub : a • (mulStab C) ⊆ ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C)))))
          ∪ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C)))) := by
        intro x hx
        by_cases hc : x ∈ (A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C)))
        · exact Finset.mem_union_right _ hc
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hc⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C)))))
        ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))
      have h3 := Finset.card_union_le (A ∩ (a • (mulStab C))) (B ∩ (a • (mulStab C)))
      have h4 : (a • (mulStab C)).card = (mulStab C).card := Finset.card_smul_finset _ _
      omega
    have hcov2 : (mulStab C).card ≤ ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))).card
        + (A ∩ (b • (mulStab C))).card + (B ∩ (b • (mulStab C))).card := by
      have hsub : b • (mulStab C) ⊆ ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C)))))
          ∪ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C)))) := by
        intro x hx
        by_cases hc : x ∈ (A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C)))
        · exact Finset.mem_union_right _ hc
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hc⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C)))))
        ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))
      have h3 := Finset.card_union_le (A ∩ (b • (mulStab C))) (B ∩ (b • (mulStab C)))
      have h4 : (b • (mulStab C)).card = (mulStab C).card := Finset.card_smul_finset _ _
      omega
    have hSAB : Disjoint ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))) (A ∪ B) := by
      rw [Finset.disjoint_left]
      intro x hx hxAB
      rw [Finset.mem_sdiff] at hx
      apply hx.2
      rw [Finset.mem_union] at hxAB
      rcases hxAB with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h, hx.1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hx.1⟩)
    have hTAB : Disjoint ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))) (A ∪ B) := by
      rw [Finset.disjoint_left]
      intro x hx hxAB
      rw [Finset.mem_sdiff] at hx
      apply hx.2
      rw [Finset.mem_union] at hxAB
      rcases hxAB with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h, hx.1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hx.1⟩)
    have hSTdisj : Disjoint ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C)))))
        ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))) := by
      have hsd : Disjoint (a • (mulStab C)) (b • (mulStab C)) := hHgrp.smul_coset_disjoint hcosetne
      exact Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hsd)
    have hSTP : (A ∪ B).card + ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))).card
        + ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))).card
        ≤ ((A ∪ B) * (mulStab C)).card := by
      have hsubU : ((A ∪ B) ∪ ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))))
          ∪ ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))) ⊆ (A ∪ B) * (mulStab C) := by
        refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
        · exact hHgrp.subset_mul _
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hx.1
          exact mul_mem_mul (Finset.mem_union_left _ ha) hh
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hx.1
          exact mul_mem_mul (Finset.mem_union_right _ hb) hh
      have hd1 : Disjoint ((A ∪ B) ∪ ((a • (mulStab C)) \ ((A ∩ (a • (mulStab C))) ∪ (B ∩ (a • (mulStab C))))))
          ((b • (mulStab C)) \ ((A ∩ (b • (mulStab C))) ∪ (B ∩ (b • (mulStab C))))) :=
        Finset.disjoint_union_left.2 ⟨hTAB.symm, hSTdisj⟩
      have hc1 := Finset.card_union_of_disjoint hd1
      have hc2 := Finset.card_union_of_disjoint hSAB.symm
      have := Finset.card_le_card hsubU
      omega
    -- `A * B` is not a convergent.
    have hABnotconv : (A * B).card + 1 < (A ∩ B).card + (A ∪ B).card := by
      have hABn𝒞 : A * B ∉ 𝒞 := by
        intro hcon
        have hle := hCmin _ hcon
        rw [hK] at hle
        simp only [Finset.card_singleton] at hle
        omega
      by_contra hcon
      push Not at hcon
      apply hABn𝒞
      rw [hmem𝒞]
      refine ⟨Subset.rfl, hABprod, ?_⟩
      rw [hK, hone, mul_one, Finset.card_one]
      omega
    omega

end Core


section Assemble

variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The trivial-stabiliser case of Kneser's theorem: `#A + #B ≤ #(A * B) + 1`. -/
theorem kneser_trivial (n : ℕ) (IH : ∀ m, m < n → KneserAt.{u} m)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hn : (A * B).card + A.card ≤ n) (hK : mulStab (A * B) = {1}) :
    A.card + B.card ≤ (A * B).card + 1 := by
  classical
  rcases Nat.lt_or_ge A.card 2 with hA2 | hA2
  · -- `#A = 1`
    have hA1 : A.card = 1 := by
      have := Finset.card_pos.2 hA
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hA1
    subst hx
    rw [Finset.singleton_mul, Finset.card_smul_finset, Finset.card_singleton]
    omega
  · -- `#A ≥ 2`: translate `B` so that `A ∩ B` is a nonempty proper subset of `A`
    obtain ⟨a, ha, a', ha', hne⟩ : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' :=
      Finset.one_lt_card.1 (by omega)
    have hstabB : mulStab B ⊆ mulStab (A * B) := by
      intro g hg
      rw [mem_mulStab] at hg ⊢
      rw [← mul_smul_comm, hg]
    have hnotstab : (a' * a⁻¹) • B ≠ B := by
      intro hcon
      have h1 : a' * a⁻¹ ∈ mulStab B := mem_mulStab.2 hcon
      have h2 := hstabB h1
      rw [hK, Finset.mem_singleton] at h2
      exact hne (by
        have : a' = a := by
          have := mul_inv_eq_one.1 h2
          exact this
        exact this.symm)
    obtain ⟨b, hb, hbnot⟩ : ∃ b ∈ B, (a' * a⁻¹) * b ∉ B := by
      by_contra hcon
      push Not at hcon
      apply hnotstab
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rw [mem_smul_finset] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact hcon y hy
      · rw [Finset.card_smul_finset]
    have hBB : A * ((b⁻¹ * a) • B) = (b⁻¹ * a) • (A * B) := mul_smul_comm _ _ _
    have hB'ne : ((b⁻¹ * a) • B).Nonempty := hB.image _
    have hK' : mulStab (A * ((b⁻¹ * a) • B)) = {1} := by
      rw [hBB, mulStab_smul]; exact hK
    have hcard' : (A * ((b⁻¹ * a) • B)).card = (A * B).card := by
      rw [hBB, Finset.card_smul_finset]
    have hn' : (A * ((b⁻¹ * a) • B)).card + A.card ≤ n := by rw [hcard']; exact hn
    have hmemA : a ∈ A ∩ ((b⁻¹ * a) • B) := by
      refine Finset.mem_inter.2 ⟨ha, mem_smul_finset.2 ⟨b, hb, ?_⟩⟩
      simp only [smul_eq_mul]
      rw [mul_comm b⁻¹ a, mul_assoc, inv_mul_cancel, mul_one]
    have ha'not : a' ∉ (b⁻¹ * a) • B := by
      intro hcon
      obtain ⟨y, hy, hya⟩ := mem_smul_finset.1 hcon
      apply hbnot
      have hy2 : y = a' * a⁻¹ * b := by
        simp only [smul_eq_mul] at hya
        have h1 : b⁻¹ * a * y = a' := hya
        have h2 : y = (b⁻¹ * a)⁻¹ * a' := by
          rw [← h1, inv_mul_cancel_left]
        rw [h2, mul_inv_rev, inv_inv, mul_comm (a⁻¹ * b) a', ← mul_assoc]
      rw [← hy2]; exact hy
    have hlt : (A ∩ ((b⁻¹ * a) • B)).card < A.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hsub
      exact ha'not (Finset.mem_inter.1 (hsub ha')).2
    have := kneser_core n IH A ((b⁻¹ * a) • B) hA hB'ne hn' hK' ⟨a, hmemA⟩ hlt
    rwa [hcard', Finset.card_smul_finset] at this

/-- The inductive step for Kneser's theorem. -/
theorem kneserAt_step (n : ℕ) (IH : ∀ m, m < n → KneserAt.{u} m) : KneserAt.{u} n := by
  intro G _ _ _ A B hA hB hn
  by_cases hK : 1 < (mulStab (A * B)).card
  · exact kneser_quotient n IH A B hA hB hn hK
  · have hK1 : (mulStab (A * B)).card = 1 := by
      have := (isSubgroupFinset_mulStab (A * B)).card_pos'
      omega
    have hKeq : mulStab (A * B) = {1} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hK1
      have h1 : (1 : G) ∈ mulStab (A * B) := by simp
      rw [hx, Finset.mem_singleton] at h1
      rw [hx, h1]
    have hcore := kneser_trivial n IH A B hA hB hn hKeq
    have hone : ({1} : Finset G) = 1 := rfl
    rw [hKeq, hone, mul_one, mul_one, Finset.card_one]
    exact hcore

theorem kneserAt_all (n : ℕ) : KneserAt.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => exact kneserAt_step n ih

/-- **Kneser's addition theorem.**  For nonempty finite subsets `A, B` of a finite commutative
group, with `H = S(A * B)` the stabiliser of the product set,
`#(A * H) + #(B * H) ≤ #(A * B) + #H`. -/
theorem card_mul_le_card_mul_mulStab (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A * mulStab (A * B)).card + (B * mulStab (A * B)).card
      ≤ (A * B).card + (mulStab (A * B)).card :=
  kneserAt_all _ A B hA hB le_rfl

/-- The weak form of Kneser's theorem: `#A + #B ≤ #(A * B) + #S(A * B)`. -/
theorem card_add_card_le_card_mul_add_card_mulStab (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ (A * B).card + (mulStab (A * B)).card := by
  have h := card_mul_le_card_mul_mulStab A B hA hB
  have h1 : A.card ≤ (A * mulStab (A * B)).card :=
    Finset.card_le_card ((isSubgroupFinset_mulStab _).subset_mul A)
  have h2 : B.card ≤ (B * mulStab (A * B)).card :=
    Finset.card_le_card ((isSubgroupFinset_mulStab _).subset_mul B)
  omega

end Assemble

end GaloisForLFunctions.HTGeometry.AddComb
