import GaloisForLFunctions.RHTower.Sieve.FiniteFiberPartition
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fibre counts and additive energy under a finite cover

For a map `f : α → β` on a finite set and a predicate `p`, the restricted fibre count of `b` is
`#{a : p a ∧ f a = b}` and the restricted energy is `∑_b (fibre count)²`. If the `p`-points are
covered by finitely many pieces `cover i`, each fibre count is at most the sum of the piece counts,
and by Cauchy–Schwarz the energy is at most `#ι` times the sum of the piece energies.

## Main results

- `finiteFiberCountWith_le_cover`: `count_p(b) ≤ ∑_i count_{p ∧ cover i}(b)`.
- `finiteFiberEnergyWith_le_cover`: `energy_p ≤ #ι · ∑_i energy_{p ∧ cover i}`.

## Hypotheses

Both results are unconditional finite combinatorics; they take as input the covering hypothesis
that every `a` with `p a` satisfies `cover i a` for some `i`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- If every `p`-point lies in some piece `cover i`, the `p`-restricted fibre count of `b` is at most
the sum over pieces of the fibre counts restricted to `p ∧ cover i`. -/
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

/-- If every `p`-point lies in some piece `cover i`, the `p`-restricted fibre energy is at most
`#ι` times the sum of the piece energies, by Cauchy–Schwarz on each fibre. -/
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
    (∑ b : β, finiteFiberCountWith f p b ^ (2 : ℕ)) ≤
        ∑ b : β, (∑ i : ι,
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro b _
      exact Nat.pow_le_pow_left
        (finiteFiberCountWith_le_cover f p cover hcover b) 2
    _ ≤ ∑ b : β, Fintype.card ι *
        ∑ i : ι, finiteFiberCountWith f (fun a => p a ∧ cover i a) b ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro b _
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i : ι =>
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b))
    _ = Fintype.card ι *
        ∑ i : ι, ∑ b : β,
          finiteFiberCountWith f (fun a => p a ∧ cover i a) b ^ (2 : ℕ) := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]

end

end RHTower.Sieve

