import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayers
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedScheduleCount

/-!
# Explicit active block chains in Matomäki--Teräväinen main layers

Empty padded blocks contribute the zero arithmetic function and are removed before counting.
Every surviving depth-`d` main piece is indexed by one strictly descending active block chain, and
the total chain count is at most the `d`-th power of the number of active blocks.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Indices of genuinely nonempty blocks in an arbitrary finite iteration schedule. -/
def mtActiveBlockIndices {t : ℕ} (block : Fin t → Finset ℕ) : Finset (Fin t) :=
  Finset.univ.filter fun i => (block i).Nonempty

/-- Active indices lying strictly below the current recursion cutoff. -/
def mtActiveBlockPrefix {t : ℕ} (block : Fin t → Finset ℕ)
    (j : Fin (t + 1)) : Finset (Fin t) :=
  (mtBlockPrefix j).filter fun i => (block i).Nonempty

/-- Strictly descending active block-index chains of one fixed length. -/
def mtActiveBlockChains {t : ℕ} (block : Fin t → Finset ℕ) :
    ℕ → Fin (t + 1) → Finset (List (Fin t))
  | 0, _ => {[]}
  | depth + 1, j =>
      (mtActiveBlockPrefix block j).biUnion fun i =>
        (mtActiveBlockChains block depth i.castSucc).image fun chain => i :: chain

/-- One signed convolution piece attached to a descending block chain. -/
def mtSignedBlockChainAF {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ) :
    List (Fin t) → ArithmeticFunction ℂ
  | [] => T
  | i :: chain => -(mtPrimeBlockAF (block i) * mtSignedBlockChainAF T block chain)

@[simp] theorem mtPrimeBlockAF_empty : mtPrimeBlockAF ∅ = (0 : ArithmeticFunction ℂ) := by
  ext n
  simp [mtPrimeBlockAF]

/-- Removing empty blocks does not change one recursive main-layer sum. -/
theorem sum_mtActiveBlockPrefix_eq {t : ℕ}
    (block : Fin t → Finset ℕ) (j : Fin (t + 1))
    (F : Fin t → ArithmeticFunction ℂ) :
    ∑ i ∈ mtActiveBlockPrefix block j, mtPrimeBlockAF (block i) * F i =
      ∑ i ∈ mtBlockPrefix j, mtPrimeBlockAF (block i) * F i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hiPrefix hiActive
  have hnot : ¬(block i).Nonempty := by
    simpa [mtActiveBlockPrefix, hiPrefix] using hiActive
  have hempty : block i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  simp [hempty]

/-- The recursive signed layer is exactly the sum over its active descending chains. -/
theorem mtSignedMainLayerAF_eq_sum_activeChains {t : ℕ}
    (T : ArithmeticFunction ℂ) (block : Fin t → Finset ℕ)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtSignedMainLayerAF T block depth j =
      ∑ chain ∈ mtActiveBlockChains block depth j,
        mtSignedBlockChainAF T block chain := by
  induction depth generalizing j with
  | zero => simp [mtSignedMainLayerAF, mtActiveBlockChains, mtSignedBlockChainAF]
  | succ depth ih =>
      rw [mtSignedMainLayerAF, ← sum_mtActiveBlockPrefix_eq]
      rw [mtActiveBlockChains]
      have hpair :
          (↑(mtActiveBlockPrefix block j) : Set (Fin t)).PairwiseDisjoint fun i =>
            (mtActiveBlockChains block depth i.castSucc).image fun chain => i :: chain := by
        intro i hi k hk hik
        change Disjoint
          ((mtActiveBlockChains block depth i.castSucc).image fun chain => i :: chain)
          ((mtActiveBlockChains block depth k.castSucc).image fun chain => k :: chain)
        rw [Finset.disjoint_left]
        intro chain hchainI hchainK
        obtain ⟨tailI, htailI, rfl⟩ := Finset.mem_image.mp hchainI
        obtain ⟨tailK, htailK, heq⟩ := Finset.mem_image.mp hchainK
        exact hik (List.cons.inj heq.symm).1
      rw [Finset.sum_biUnion hpair, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_image (by
        intro a ha b hb hab
        exact (List.cons.inj hab).2)]
      rw [ih i.castSucc, Finset.mul_sum, ← Finset.sum_neg_distrib]
      rfl

/-- Every prefix-active index belongs to the global active family. -/
theorem mtActiveBlockPrefix_subset_activeBlockIndices {t : ℕ}
    (block : Fin t → Finset ℕ) (j : Fin (t + 1)) :
    mtActiveBlockPrefix block j ⊆ mtActiveBlockIndices block := by
  intro i hi
  simp only [mtActiveBlockPrefix, mtActiveBlockIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

/-- Number of depth-`d` active descending chains never exceeds the full active `d`-tuple count. -/
theorem card_mtActiveBlockChains_le_pow {t : ℕ}
    (block : Fin t → Finset ℕ) (depth : ℕ) (j : Fin (t + 1)) :
    (mtActiveBlockChains block depth j).card ≤ (mtActiveBlockIndices block).card ^ depth := by
  induction depth generalizing j with
  | zero => simp [mtActiveBlockChains]
  | succ depth ih =>
      calc
        (mtActiveBlockChains block (depth + 1) j).card ≤
            ∑ i ∈ mtActiveBlockPrefix block j,
              ((mtActiveBlockChains block depth i.castSucc).image
                fun chain => i :: chain).card := by
          rw [mtActiveBlockChains]
          exact Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ mtActiveBlockPrefix block j,
              (mtActiveBlockIndices block).card ^ depth := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.card_image_le.trans (ih i.castSucc)
        _ = (mtActiveBlockPrefix block j).card *
              (mtActiveBlockIndices block).card ^ depth := by
          simp [Finset.sum_const]
        _ ≤ (mtActiveBlockIndices block).card *
              (mtActiveBlockIndices block).card ^ depth := by
          exact Nat.mul_le_mul_right _
            (Finset.card_le_card (mtActiveBlockPrefix_subset_activeBlockIndices block j))
        _ = (mtActiveBlockIndices block).card ^ (depth + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _

/-- Generic active-block count specializes definitionally to the paper-aligned schedule. -/
theorem mtActiveBlockIndices_paperAligned {t z₀ z₁ : ℕ} (δ : ℝ) :
    mtActiveBlockIndices
      (mtAdjacentPrimeBlock (t := t) (mtPaperAlignedEndpoint z₀ z₁ δ)) =
      mtPaperAlignedActiveBlockIndices t z₀ z₁ δ := by
  rfl

/-- Every repaired paper-aligned main layer has the exact source-scale chain count. -/
theorem card_mtActiveBlockChains_paperAligned_le
    {t z₀ z₁ depth : ℕ} {δ : ℝ}
    (hz₀ : 2 ≤ z₀) (hz : z₀ ≤ z₁) (hδ : 0 < δ)
    (hprogress : 2 ≤ δ * ((z₀ - 1 : ℕ) : ℝ))
    (j : Fin (t + 1)) :
    (mtActiveBlockChains
        (mtAdjacentPrimeBlock (t := t) (mtPaperAlignedEndpoint z₀ z₁ δ)) depth j).card ≤
      (adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 2) ^ depth := by
  calc
    _ ≤ (mtActiveBlockIndices
        (mtAdjacentPrimeBlock (t := t) (mtPaperAlignedEndpoint z₀ z₁ δ))).card ^ depth :=
      card_mtActiveBlockChains_le_pow _ depth j
    _ = (mtPaperAlignedActiveBlockIndices t z₀ z₁ δ).card ^ depth := by
      rw [mtActiveBlockIndices_paperAligned]
    _ ≤ (adicIndex (δ / 2) ((z₀ - 1 : ℕ) : ℝ) ((z₁ - 1 : ℕ) : ℝ) + 2) ^ depth :=
      (Nat.pow_le_pow_left
        (card_mtPaperAlignedActiveBlockIndices_le_adicIndex_add_two
          (t := t) hz₀ hz hδ hprogress)) depth

end

end RHTower.Sieve
