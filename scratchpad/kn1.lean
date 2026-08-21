import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset

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

end GaloisForLFunctions.HTGeometry.AddComb

namespace GaloisForLFunctions.HTGeometry.AddComb
variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

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

end GaloisForLFunctions.HTGeometry.AddComb
