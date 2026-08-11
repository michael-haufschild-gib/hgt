import GaloisForLFunctions.RHTower.Sieve.HeathBrownSmoothAggregatePerron
import GaloisForLFunctions.RHTower.Sieve.MaynardGroupSelection

/-!
# Large-box selection from the exact signed Heath--Brown aggregate

The smooth Perron identity produces one nested finite signed sum.  This file proves the exact
finite pigeonhole needed to return from that cancellation-preserving aggregate to one literal
factorized box.  All losses are explicit cardinal factors; no maximum or asymptotic notation is
left hidden.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- A finite sum with large norm contains a summand which is large after paying exactly the
cardinality of the index set. -/
theorem exists_mem_card_mul_norm_ge
    {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → E) {V : ℝ}
    (hlarge : V ≤ ‖∑ i ∈ s, f i‖) :
    ∃ i ∈ s, V ≤ (s.card : ℝ) * ‖f i‖ := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) hs
  refine ⟨i, hi, hlarge.trans ?_⟩
  calc
    ‖∑ j ∈ s, f j‖ ≤ ∑ j ∈ s, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, ‖f i‖ := Finset.sum_le_sum fun j hj => hmax j hj
    _ = (s.card : ℝ) * ‖f i‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Every dyadic tuple set is inhabited: the all-zero tuple is admissible. -/
theorem dyadicChoiceSet_nonempty (r M : ℕ) : (dyadicChoiceSet r M).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp [dyadicChoiceSet]

/-- Exact number of dyadic tuples. -/
@[simp] theorem card_dyadicChoiceSet (r M : ℕ) :
    (dyadicChoiceSet r M).card = (Nat.log 2 M + 1) ^ r := by
  simp [dyadicChoiceSet]

/-- Name for the complete pointwise signed dyadic aggregate appearing in smooth Perron. -/
def heathBrownDyadicAggregate (L X k : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range k,
    ∑ q ∈ Finset.range (Nat.log 2 X + 1),
      ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
        ∑ a ∈ dyadicChoiceSet (k - m) L,
          heathBrownDyadicTermProduct L X k m a b q s

/-- **Exact four-level aggregate-to-box selection.**  A large value of the cancellation-preserving
aggregate forces one literal signed box to be large after the precise product of the four indexing
cardinalities. -/
theorem exists_large_heathBrownDyadicTermProduct
    (L X k : ℕ) (hk : 0 < k) (s : ℂ) {V : ℝ}
    (hlarge : V ≤ ‖heathBrownDyadicAggregate L X k s‖) :
    ∃ m ∈ Finset.range k,
      ∃ q ∈ Finset.range (Nat.log 2 X + 1),
        ∃ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∃ a ∈ dyadicChoiceSet (k - m) L,
            V ≤ ((Finset.range k).card : ℝ) *
              (((Finset.range (Nat.log 2 X + 1)).card : ℝ) *
                (((dyadicChoiceSet (k - m - 1) X).card : ℝ) *
                  (((dyadicChoiceSet (k - m) L).card : ℝ) *
                    ‖heathBrownDyadicTermProduct L X k m a b q s‖))) := by
  classical
  let Fm : ℕ → ℂ := fun m =>
    ∑ q ∈ Finset.range (Nat.log 2 X + 1),
      ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
        ∑ a ∈ dyadicChoiceSet (k - m) L,
          heathBrownDyadicTermProduct L X k m a b q s
  have hmset : (Finset.range k).Nonempty := ⟨0, Finset.mem_range.mpr hk⟩
  have haggregate : heathBrownDyadicAggregate L X k s = ∑ m ∈ Finset.range k, Fm m := rfl
  obtain ⟨m, hm, hmlarge⟩ := exists_mem_card_mul_norm_ge
    (Finset.range k) hmset Fm (hlarge.trans_eq (congrArg norm haggregate))
  let Fq : ℕ → ℂ := fun q =>
    ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
      ∑ a ∈ dyadicChoiceSet (k - m) L,
        heathBrownDyadicTermProduct L X k m a b q s
  have hqset : (Finset.range (Nat.log 2 X + 1)).Nonempty := by simp
  have hFm : Fm m = ∑ q ∈ Finset.range (Nat.log 2 X + 1), Fq q := rfl
  obtain ⟨q, hq, hqlarge⟩ := exists_mem_card_mul_norm_ge
    (Finset.range (Nat.log 2 X + 1)) hqset Fq
    (show ‖Fm m‖ ≤ ‖∑ q ∈ Finset.range (Nat.log 2 X + 1), Fq q‖ by rw [hFm])
  let Fb : (Fin (k - m - 1) → ℕ) → ℂ := fun b =>
    ∑ a ∈ dyadicChoiceSet (k - m) L,
      heathBrownDyadicTermProduct L X k m a b q s
  have hbset := dyadicChoiceSet_nonempty (k - m - 1) X
  have hFq : Fq q = ∑ b ∈ dyadicChoiceSet (k - m - 1) X, Fb b := rfl
  obtain ⟨b, hb, hblarge⟩ := exists_mem_card_mul_norm_ge
    (dyadicChoiceSet (k - m - 1) X) hbset Fb
    (show ‖Fq q‖ ≤ ‖∑ b ∈ dyadicChoiceSet (k - m - 1) X, Fb b‖ by rw [hFq])
  let Fa : (Fin (k - m) → ℕ) → ℂ := fun a =>
    heathBrownDyadicTermProduct L X k m a b q s
  have haset := dyadicChoiceSet_nonempty (k - m) L
  have hFb : Fb b = ∑ a ∈ dyadicChoiceSet (k - m) L, Fa a := rfl
  obtain ⟨a, ha, halarge⟩ := exists_mem_card_mul_norm_ge
    (dyadicChoiceSet (k - m) L) haset Fa
    (show ‖Fb b‖ ≤ ‖∑ a ∈ dyadicChoiceSet (k - m) L, Fa a‖ by rw [hFb])
  refine ⟨m, hm, q, hq, b, hb, a, ha, ?_⟩
  calc
    V ≤ ((Finset.range k).card : ℝ) * ‖Fm m‖ := hmlarge
    _ ≤ ((Finset.range k).card : ℝ) *
        (((Finset.range (Nat.log 2 X + 1)).card : ℝ) * ‖Fq q‖) :=
      mul_le_mul_of_nonneg_left hqlarge (by positivity)
    _ ≤ ((Finset.range k).card : ℝ) *
        (((Finset.range (Nat.log 2 X + 1)).card : ℝ) *
          (((dyadicChoiceSet (k - m - 1) X).card : ℝ) * ‖Fb b‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hblarge (by positivity)) (by positivity)
    _ ≤ ((Finset.range k).card : ℝ) *
        (((Finset.range (Nat.log 2 X + 1)).card : ℝ) *
          (((dyadicChoiceSet (k - m - 1) X).card : ℝ) *
            (((dyadicChoiceSet (k - m) L).card : ℝ) * ‖Fa a‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left halarge (by positivity)) (by positivity)) (by positivity)

/-- The four exact cardinality losses collapse to one fixed-degree polylogarithmic factor. -/
theorem exists_large_heathBrownDyadicTermProduct_polylog
    (L X k : ℕ) (hk : 0 < k) (s : ℂ) {V : ℝ}
    (hlarge : V ≤ ‖heathBrownDyadicAggregate L X k s‖) :
    ∃ m ∈ Finset.range k,
      ∃ q ∈ Finset.range (Nat.log 2 X + 1),
        ∃ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∃ a ∈ dyadicChoiceSet (k - m) L,
            V ≤ (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
              (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m)) *
                ‖heathBrownDyadicTermProduct L X k m a b q s‖ := by
  obtain ⟨m, hm, q, hq, b, hb, a, ha, hbound⟩ :=
    exists_large_heathBrownDyadicTermProduct L X k hk s hlarge
  refine ⟨m, hm, q, hq, b, hb, a, ha, ?_⟩
  have hm_lt : m < k := Finset.mem_range.mp hm
  have hsub : k - m = (k - m - 1) + 1 := by omega
  simp only [Finset.card_range, card_dyadicChoiceSet] at hbound
  push_cast at hbound
  have hpowX : (1 + (Nat.log 2 X : ℝ)) ^ (k - m) =
      (1 + (Nat.log 2 X : ℝ)) ^ (k - m - 1) * (1 + (Nat.log 2 X : ℝ)) := by
    calc
      (1 + (Nat.log 2 X : ℝ)) ^ (k - m) =
          (1 + (Nat.log 2 X : ℝ)) ^ ((k - m - 1) + 1) := congrArg _ hsub
      _ = (1 + (Nat.log 2 X : ℝ)) ^ (k - m - 1) *
          (1 + (Nat.log 2 X : ℝ)) := pow_succ _ _
  have hpowX' : ((Nat.log 2 X : ℝ) + 1) ^ (k - m) =
      ((Nat.log 2 X : ℝ) + 1) ^ (k - m - 1) * ((Nat.log 2 X : ℝ) + 1) := by
    simpa [add_comm] using hpowX
  apply hbound.trans_eq
  push_cast
  rw [hpowX']
  ring

end RHTower.Sieve
