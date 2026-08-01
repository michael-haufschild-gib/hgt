import GaloisForLFunctions.RHTower.DeningerBoxRefinement
import GaloisForLFunctions.RHTower.DeningerTransversePartition
import Mathlib.Topology.PartitionOfUnity

/-!
# Fineness of the packet: transverse partitions of unity subordinate to any cover

On a product whose first factor is compact profinite and whose second factor is compact Hausdorff,
every open cover admits a subordinate partition of unity which is locally constant along the first
factor.

The three steps are the ones the card performs by hand: refine the cover by clopen boxes, refine
the clopen sides to a clopen partition, and over each piece of the partition take a partition of
unity on the second factor subordinate to the sides that survive there.  The assembled functions
are the products.

* `deningerPacketFine` : the subordinate transverse partition of unity.
-/

namespace RHTower

open Set TopologicalSpace

universe u v w

section PacketFine

variable {B : Type u} {S : Type v} {κ : Type w} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TotallyDisconnectedSpace B] [TopologicalSpace S] [CompactSpace S] [T2Space S]

/-- **The packet is fine.**  Every open cover of a compact profinite factor times a compact
Hausdorff factor admits a subordinate partition of unity whose members are continuous and locally
constant along the profinite factor. -/
theorem deningerPacketFine (U : κ → Set (B × S)) (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ p : B × S, ∃ j, p ∈ U j) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (ρ : ι → B × S → ℝ) (g : ι → κ),
      (∀ i, Continuous (ρ i))
        ∧ (∀ (i : ι) (t : S), IsLocallyConstant fun b : B => ρ i (b, t))
        ∧ (∀ p : B × S, ∑ i, ρ i p = 1)
        ∧ ∀ (i : ι) (p : B × S), ρ i p ≠ 0 → p ∈ U (g i) := by
  classical
  obtain ⟨T, C, W, f, hCclopen, hWopen, hbox, hTcov⟩ := deningerBoxRefinement hU hcov
  -- the boxes of the finite refinement, as a finite index type
  set ι₀ : Type (max u v) := {q : B × S // q ∈ T} with hι₀
  haveI : Fintype ι₀ := FinsetCoe.fintype T
  set Cs : ι₀ → Set B := fun q => C q.val with hCs
  have hCsClopen : ∀ q : ι₀, IsClopen (Cs q) := fun q => hCclopen q.val
  -- the clopen partition refining the sides of the boxes
  set A : Finset ι₀ → Set B := fun P => deningerAtom Cs P with hA
  have hAclopen : ∀ P, IsClopen (A P) := fun P => deningerAtom_isClopen hCsClopen P
  have hApart : ∀ b : B, ∃! P : Finset ι₀, b ∈ A P := deningerAtom_existsUnique Cs
  -- the transverse sides that survive over a given piece
  set V : Finset ι₀ → ι₀ → Set S := fun P q => if q ∈ P then W q.val else ∅ with hV
  have hVopen : ∀ P q, IsOpen (V P q) := by
    intro P q
    by_cases h : q ∈ P
    · rw [hV]
      simp only [if_pos h]
      exact hWopen q.val
    · rw [hV]
      simp only [if_neg h]
      exact isOpen_empty
  -- over a nonempty piece the surviving sides cover the second factor
  have hVcover : ∀ (P : Finset ι₀) (b : B), b ∈ A P → (univ : Set S) ⊆ ⋃ q, V P q := by
    intro P b hb t _
    obtain ⟨q, hqT, hq⟩ := hTcov (b, t)
    have hqP : (⟨q, hqT⟩ : ι₀) ∈ P := (hb ⟨q, hqT⟩).mpr hq.1
    refine mem_iUnion.mpr ⟨⟨q, hqT⟩, ?_⟩
    rw [hV]
    simp only [if_pos hqP]
    exact hq.2
  -- a partition of unity on the second factor over each piece
  have hpou : ∀ P : Finset ι₀, ∃ ψ : ι₀ → S → ℝ,
      (∀ q, Continuous (ψ q)) ∧ (∀ q t, ψ q t ≠ 0 → t ∈ V P q)
        ∧ ∀ b ∈ A P, ∀ t : S, ∑ q, ψ q t = 1 := by
    intro P
    by_cases hne : (A P).Nonempty
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate (s := (univ : Set S))
        isClosed_univ (V P) (hVopen P) (hVcover P b hb)
      refine ⟨fun q => φ q, fun q => (φ q).continuous, fun q t ht => ?_, fun _ _ t => ?_⟩
      · exact hφ q (subset_tsupport _ ht)
      · rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one (mem_univ t)
    · refine ⟨fun _ _ => 0, fun _ => continuous_const, fun q t ht => absurd rfl ht, ?_⟩
      intro b hb
      exact absurd ⟨b, hb⟩ hne
  choose ψ hψcont hψsupp hψsum using hpou
  refine ⟨ι₀, inferInstance, fun q p => deningerTransverseSum A ψ q p, fun q => f q.val,
    fun q => ?_, fun q t => ?_, fun p => ?_, fun q p hne => ?_⟩
  · exact deningerTransverseSum_continuous hAclopen (fun P j => hψcont P j) q
  · exact deningerTransverseSum_locallyConstant hAclopen hApart q t
  · exact deningerTransverseSum_sum hApart (fun P b hb t => hψsum P b hb t) p
  · refine deningerTransverseSum_subordinate (I := V) (U := fun j : ι₀ => U (f j.val))
      (fun P j t ht => hψsupp P j t ht) ?_ hne
    intro P j
    rintro ⟨b, t⟩ ⟨hbP, htV⟩
    by_cases hjP : j ∈ P
    · have hbC : b ∈ Cs j := deningerAtom_subset hjP hbP
      have htW : t ∈ W j.val := by
        rw [hV] at htV
        simpa only [if_pos hjP] using htV
      exact hbox j.val ⟨hbC, htW⟩
    · rw [hV] at htV
      simp only [if_neg hjP] at htV
      exact absurd htV (notMem_empty t)

end PacketFine

end RHTower
