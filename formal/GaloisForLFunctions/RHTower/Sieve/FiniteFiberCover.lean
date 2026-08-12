import GaloisForLFunctions.RHTower.Sieve.FiniteFiberPartition
import Mathlib.Algebra.Order.Chebyshev

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem finiteFiberCountWith_le_cover
    {α β ι : Type*} [Fintype α] [Fintype ι] [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p]
    (cover : ι → α → Prop) [∀ i, DecidablePred (cover i)]
    (hcover : ∀ a, p a → ∃ i, cover i a) (b : β) :
    finiteFiberCountWith f p b ≤
      ∑ i : ι, finiteFiberCountWith f (fun a => p a ∧ cover i a) b := by
  classical
  let source := Finset.univ.filter fun a : α => p a ∧ f a = b
  let target : ι → Finset α := fun i =>
    Finset.univ.filter fun a => (p a ∧ cover i a) ∧ f a = b
  have hsubset : source ⊆ Finset.univ.biUnion target := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    obtain ⟨i, hi⟩ := hcover a ha'.1
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨⟨ha'.1, hi⟩, ha'.2⟩⟩⟩
  calc
    finiteFiberCountWith f p b = source.card := rfl
    _ ≤ (Finset.univ.biUnion target).card := Finset.card_le_card hsubset
    _ ≤ ∑ i ∈ Finset.univ, (target i).card := Finset.card_biUnion_le
    _ = ∑ i : ι, finiteFiberCountWith f (fun a => p a ∧ cover i a) b := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

theorem finiteFiberEnergyWith_le_cover
    {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq β]
    (f : α → β) (p : α → Prop) [DecidablePred p]
    (cover : ι → α → Prop) [∀ i, DecidablePred (cover i)]
    (hcover : ∀ a, p a → ∃ i, cover i a) :
    finiteFiberEnergyWith f p ≤
      Fintype.card ι *
        ∑ i : ι, finiteFiberEnergyWith f (fun a => p a ∧ cover i a) := by
  classical
  unfold finiteFiberEnergyWith
  calc
    (∑ b : β, finiteFiberCountWith f p b ^ 2) ≤
        ∑ b : β, (∑ i : ι,
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b) ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      exact Nat.pow_le_pow_left
        (finiteFiberCountWith_le_cover f p cover hcover b) 2
    _ ≤ ∑ b : β, Fintype.card ι *
        ∑ i : ι, finiteFiberCountWith f (fun a => p a ∧ cover i a) b ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i : ι =>
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b))
    _ = Fintype.card ι *
        ∑ i : ι, ∑ b : β,
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]

end

end RHTower.Sieve

