import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalEdgeMass

/-! Each canonical edge runs from its positive-parity endpoint to its negative-parity endpoint. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilBinomialParity_eq_one_or_neg_one (r : ℕ) (j : Fin (r + 2)) :
    finiteWeilBinomialParity r j = 1 ∨ finiteWeilBinomialParity r j = -1 :=
  neg_one_pow_eq_or ℝ ((r + 1) - (j : ℕ))

def finiteWeilCanonicalEdgeSource (r : ℕ) (i : Fin (r + 1)) : Fin (r + 2) :=
  if finiteWeilBinomialParity r i.castSucc = 1 then i.castSucc else i.succ

def finiteWeilCanonicalEdgeTarget (r : ℕ) (i : Fin (r + 1)) : Fin (r + 2) :=
  if finiteWeilBinomialParity r i.castSucc = 1 then i.succ else i.castSucc

theorem finiteWeilCanonicalEdgeSource_parity (r : ℕ) (i : Fin (r + 1)) :
    finiteWeilBinomialParity r (finiteWeilCanonicalEdgeSource r i) = 1 := by
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with h | h
  · simp [finiteWeilCanonicalEdgeSource, h]
  · norm_num [finiteWeilCanonicalEdgeSource, h, finiteWeilBinomialParity_adjacent]

theorem finiteWeilCanonicalEdgeTarget_parity (r : ℕ) (i : Fin (r + 1)) :
    finiteWeilBinomialParity r (finiteWeilCanonicalEdgeTarget r i) = -1 := by
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with h | h
  · simp [finiteWeilCanonicalEdgeTarget, h, finiteWeilBinomialParity_adjacent]
  · norm_num [finiteWeilCanonicalEdgeTarget, h]

theorem finiteWeilCanonicalEdge_difference (r : ℕ) (i : Fin (r + 1))
    (f : Fin (r + 2) → ℝ) :
    f (finiteWeilCanonicalEdgeSource r i) - f (finiteWeilCanonicalEdgeTarget r i) =
      finiteWeilBinomialParity r i.castSucc * (f i.castSucc - f i.succ) := by
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with h | h
  · simp [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, h]
  · norm_num [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, h]

theorem finiteWeilCanonicalEdge_adjacent (r : ℕ) (i : Fin (r + 1)) :
    (finiteWeilCanonicalEdgeSource r i : ℕ) + 1 =
        (finiteWeilCanonicalEdgeTarget r i : ℕ) ∨
      (finiteWeilCanonicalEdgeTarget r i : ℕ) + 1 =
        (finiteWeilCanonicalEdgeSource r i : ℕ) := by
  by_cases h : finiteWeilBinomialParity r i.castSucc = 1
  · simp [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, h]
  · simp [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, h]

theorem finiteWeilCanonicalEdge_ne (r : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalEdgeSource r i ≠ finiteWeilCanonicalEdgeTarget r i := by
  intro he
  have hs := finiteWeilCanonicalEdgeSource_parity r i
  rw [he, finiteWeilCanonicalEdgeTarget_parity] at hs
  norm_num at hs

theorem finiteWeilCanonicalEdge_pairing (r k : ℕ) (f : Fin (r + 2) → ℝ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i *
      (f (finiteWeilCanonicalEdgeSource r i) - f (finiteWeilCanonicalEdgeTarget r i))) =
      ∑ j, (finiteWeilCanonicalPositiveProfile r k j -
        finiteWeilCanonicalNegativeProfile r k j) * f j := by
  have hzero : (∑ j, (finiteWeilCanonicalPositiveProfile r k j -
      finiteWeilCanonicalNegativeProfile r k j)) = 0 := by
    rw [Finset.sum_sub_distrib, (finiteWeilCanonicalProfiles_spec r k).2.1,
      (finiteWeilCanonicalProfiles_spec r k).2.2.1]
    norm_num
  rw [finiteWeil_prefix_pairing_zero _ f hzero]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = finiteWeilCanonicalPrefixDifference r k i * (f i.castSucc - f i.succ)
  rw [finiteWeilCanonicalEdge_difference, finiteWeilCanonicalPrefixDifference_signed_mass]
  ring

end RHTower
