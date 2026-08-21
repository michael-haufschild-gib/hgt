import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseFourTwoStructure
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCosetDecomposition

/-!
# CASE 4.2 of Grynkiewicz's proof: the extra block

Each of the three subcases of CASE 4.2 exhibits a set of products lying outside the core
`X · Y = (A ∪ B) · (A ∩ B)` and bounds the corresponding part of `∑_{i≤t} #(A ·_i B)` from below.
`repSum_ge_block` is that mechanism, and `case42_extra_block` is the instance where the extra
block comes from a coset meeting `A` but not `B`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **A disjoint block adds to `repSum`.**  If `C · D` avoids a `t`-representable set `S`, then
`∑_{i≤t} #(A ·_i B)` dominates `t·#S` plus `∑_{i≤t} #(C ·_i D)`. -/
theorem repSum_ge_block {A B C D S : Finset G} {t : ℕ}
    (hCA : C ⊆ A) (hDB : D ⊆ B)
    (hS : S ⊆ repSet A B t) (hdisj : Disjoint (C * D) S) :
    t * S.card + repSum C D t ≤ repSum A B t := by
  classical
  rw [repSum_eq_sum_min, repSum_eq_sum_min]
  have hsplit : ∑ c ∈ Finset.univ \ S, min (rep A B c) t + ∑ c ∈ S, min (rep A B c) t
      = ∑ c : G, min (rep A B c) t := Finset.sum_sdiff (Finset.subset_univ S)
  have hin : ∑ c ∈ S, min (rep A B c) t = t * S.card := by
    have hval : ∀ c ∈ S, min (rep A B c) t = t := by
      intro c hc
      exact min_eq_right (mem_repSet.1 (hS hc))
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_comm]
  have hzero : ∀ c ∈ S, min (rep C D c) t = 0 := by
    intro c hc
    have : rep C D c = 0 := by
      by_contra hcon
      exact (Finset.disjoint_right.1 hdisj) hc
        ((rep_pos_iff_mem_mul C D c).1 (Nat.pos_of_ne_zero hcon))
    simp [this]
  have hCD : ∑ c : G, min (rep C D c) t = ∑ c ∈ Finset.univ \ S, min (rep C D c) t := by
    have hsp : ∑ c ∈ Finset.univ \ S, min (rep C D c) t + ∑ c ∈ S, min (rep C D c) t
        = ∑ c : G, min (rep C D c) t := Finset.sum_sdiff (Finset.subset_univ S)
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsp
    omega
  have hout : ∑ c ∈ Finset.univ \ S, min (rep C D c) t
      ≤ ∑ c ∈ Finset.univ \ S, min (rep A B c) t := by
    refine Finset.sum_le_sum (fun c _ => ?_)
    exact min_le_min (rep_mono hCA hDB c) le_rfl
  omega

omit [Fintype G] in
/-- A coset meeting `A` but not `B` contributes its complement to the holes of `A ∪ B`. -/
theorem case42_holes_ge_one {A B H : Finset G} (hH : IsSubgroupFinset H)
    {α : G} (hα : α ∈ A) (hαB : ∀ z ∈ B, z ∉ α • H) :
    H.card ≤ (A ∩ (α • H)).card + (((A ∪ B) * H) \ (A ∪ B)).card := by
  classical
  have hsub : (α • H) \ (A ∪ B) ⊆ ((A ∪ B) * H) \ (A ∪ B) := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨hH.smul_subset_mul (hH.subset_mul (A ∪ B) (Finset.mem_union_left _ hα)) hz.1, hz.2⟩
  have hcard := Finset.card_le_card hsub
  have hA : ((α • H) ∩ (A ∪ B)).card + ((α • H) \ (A ∪ B)).card = H.card := by
    rw [Finset.card_inter_add_card_sdiff, Finset.card_smul_finset]
  have hAeq : (α • H) ∩ (A ∪ B) = A ∩ (α • H) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hz, hzA | hzB⟩
      · exact ⟨hzA, hz⟩
      · exact absurd hz (hαB z hzB)
    · rintro ⟨hzA, hz⟩
      exact ⟨hz, Or.inl hzA⟩
  rw [hAeq] at hA
  omega

/-- **CASE 4.2, the extra-block estimate.**  A coset meeting `A` but not `B` whose products with
some `D ⊆ B` of size at least `t` avoid the core forces `∑_{i≤t} #(A ·_i B) ≥ t#A + t#B`. -/
theorem case42_extra_block {A B : Finset G} {t : ℕ}
    (hper : (A ∩ B) * mulStab ((A ∪ B) * (A ∩ B)) = A ∩ B)
    (hsub : (A ∪ B) * (A ∩ B) ⊆ repSet A B t)
    (hAne : A.Nonempty) (hYne : (A ∩ B).Nonempty)
    {α : G} (hα : α ∈ A) (hαB : ∀ z ∈ B, z ∉ α • mulStab ((A ∪ B) * (A ∩ B)))
    {D : Finset G} (hDB : D ⊆ B) (hDt : t ≤ D.card)
    (hout : Disjoint ((A ∩ (α • mulStab ((A ∪ B) * (A ∩ B)))) * D) ((A ∪ B) * (A ∩ B))) :
    t * A.card + t * B.card ≤ repSum A B t := by
  classical
  set H := mulStab ((A ∪ B) * (A ∩ B)) with hHdef
  have hH : IsSubgroupFinset H := isSubgroupFinset_mulStab _
  have hblock := repSum_ge_block (A := A) (B := B) (C := A ∩ (α • H)) (D := D)
    (S := (A ∪ B) * (A ∩ B)) Finset.inter_subset_left hDB hsub hout
  have htriv := mul_card_le_repSum (A ∩ (α • H)) D t hDt
  have hKn := card_mul_le_card_mul_mulStab (A ∪ B) (A ∩ B)
    (hAne.mono Finset.subset_union_left) hYne
  rw [← hHdef] at hKn
  have hhX : (((A ∪ B) * H) \ (A ∪ B)).card + (A ∪ B).card = ((A ∪ B) * H).card :=
    Finset.card_sdiff_add_card_eq_card (hH.subset_mul (A ∪ B))
  have hhY : ((A ∩ B) * H).card = (A ∩ B).card := by rw [hper]
  have hcards : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hholes := case42_holes_ge_one hH hα hαB
  have hsum : A.card + B.card ≤ ((A ∪ B) * (A ∩ B)).card + (A ∩ (α • H)).card := by omega
  have hmul : t * (A.card + B.card)
      ≤ t * (((A ∪ B) * (A ∩ B)).card + (A ∩ (α • H)).card) := Nat.mul_le_mul_left t hsum
  have he1 : t * (A.card + B.card) = t * A.card + t * B.card := by ring
  have he2 : t * (((A ∪ B) * (A ∩ B)).card + (A ∩ (α • H)).card)
      = t * ((A ∪ B) * (A ∩ B)).card + t * (A ∩ (α • H)).card := by ring
  omega

end GaloisForLFunctions.HTGeometry.AddComb
