import GaloisForLFunctions.RHTower.Sieve.MaynardLowTotalObstruction

/-!
# Eligible-box recut of the Heath--Brown aggregate

The all-short grouping threshold may only be imposed after removing boxes whose total logarithmic
length is too small.  This module defines that exact finite recut and proves pointwise selection
inside the eligible aggregate.  Low-total cancellation is left intact as one complementary signed
aggregate; it is not bounded box-by-box.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

private theorem sum_subtype_mem_eq_sum
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (u : Finset α) (f : α → M) :
    (∑ x : {x // x ∈ u}, f x) = ∑ x ∈ u, f x := by
  simpa only [Finset.univ_eq_attach] using Finset.sum_attach u f

/-- Literal signed term indexed by a dependent box choice. -/
def heathBrownBoxTerm (L X k : ℕ) (c : HeathBrownBoxChoice L X k) (s : ℂ) : ℂ :=
  heathBrownDyadicTermProduct L X k c.m c.a c.b c.q s

/-- Total logarithmic lower-edge exponent of one box. -/
def heathBrownBoxTotalExponent
    (L X k : ℕ) (T0 : ℝ) (c : HeathBrownBoxChoice L X k) : ℝ :=
  ∑ i : HeathBrownBoxFactorIndex k c.m,
    dyadicLogExponent T0 (heathBrownBoxFactorExponent c.a c.b c.q i)

/-- Boxes long enough to admit a robust greedy group at threshold `t`. -/
def IsHeathBrownBoxEligible
    (L X k : ℕ) (T0 t : ℝ) (c : HeathBrownBoxChoice L X k) : Prop :=
  t ≤ heathBrownBoxTotalExponent L X k T0 c

/-- Complete aggregate reindexed by the dependent finite box type. -/
def heathBrownFlatDyadicAggregate (L X k : ℕ) (s : ℂ) : ℂ :=
  ∑ c : HeathBrownBoxChoice L X k, heathBrownBoxTerm L X k c s

/-- Dependent-box reindexing is exactly the original four-level aggregate. -/
theorem heathBrownFlatDyadicAggregate_eq
    (L X k : ℕ) (s : ℂ) :
    heathBrownFlatDyadicAggregate L X k s = heathBrownDyadicAggregate L X k s := by
  classical
  unfold heathBrownFlatDyadicAggregate heathBrownDyadicAggregate
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, heathBrownBoxTerm,
    HeathBrownBoxChoice.m, HeathBrownBoxChoice.q,
    HeathBrownBoxChoice.a, HeathBrownBoxChoice.b]
  calc
    (∑ m : Fin k, ∑ q : Fin (Nat.log 2 X + 1),
      ∑ b : {b // b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X},
        ∑ a : {a // a ∈ dyadicChoiceSet (k - (m : ℕ)) L},
          heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s) =
        ∑ m : Fin k, ∑ q : Fin (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - (m : ℕ)) L,
              heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s := by
      apply Fintype.sum_congr
      intro m
      apply Fintype.sum_congr
      intro q
      calc
        (∑ b : {b // b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X},
          ∑ a : {a // a ∈ dyadicChoiceSet (k - (m : ℕ)) L},
            heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s) =
            ∑ b : {b // b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X},
              ∑ a ∈ dyadicChoiceSet (k - (m : ℕ)) L,
                heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s := by
          apply Fintype.sum_congr
          intro b
          exact sum_subtype_mem_eq_sum
            (dyadicChoiceSet (k - (m : ℕ)) L)
            (fun a => heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s)
        _ = ∑ b ∈ dyadicChoiceSet (k - (m : ℕ) - 1) X,
              ∑ a ∈ dyadicChoiceSet (k - (m : ℕ)) L,
                heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s :=
          sum_subtype_mem_eq_sum
            (dyadicChoiceSet (k - (m : ℕ) - 1) X)
            (fun b => ∑ a ∈ dyadicChoiceSet (k - (m : ℕ)) L,
              heathBrownDyadicTermProduct L X k (m : ℕ) a b (q : ℕ) s)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
        ∑ q : Fin (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - m) L,
              heathBrownDyadicTermProduct L X k m a b q s) k]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Fin.sum_univ_eq_sum_range (fun q : ℕ =>
        ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∑ a ∈ dyadicChoiceSet (k - m) L,
            heathBrownDyadicTermProduct L X k m a b q s) (Nat.log 2 X + 1)]

/-- Signed aggregate restricted to boxes with enough total logarithmic length. -/
def heathBrownEligibleDyadicAggregate
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ c : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t c then heathBrownBoxTerm L X k c s else 0

/-- Complementary low-total signed aggregate. -/
def heathBrownLowTotalDyadicAggregate
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ c : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t c then 0 else heathBrownBoxTerm L X k c s

/-- Exact eligible/low-total decomposition, preserving cancellation in both pieces. -/
theorem heathBrownFlatDyadicAggregate_eq_eligible_add_lowTotal
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    heathBrownFlatDyadicAggregate L X k s =
      heathBrownEligibleDyadicAggregate L X k T0 t s +
        heathBrownLowTotalDyadicAggregate L X k T0 t s := by
  classical
  simp only [heathBrownFlatDyadicAggregate, heathBrownEligibleDyadicAggregate,
    heathBrownLowTotalDyadicAggregate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases h : IsHeathBrownBoxEligible L X k T0 t c <;> simp [h]

/-- A bound for the complementary low-total aggregate transfers any excess large value to the
eligible aggregate. -/
theorem norm_heathBrownEligibleDyadicAggregate_ge_of_lowTotal
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) {V E : ℝ}
    (hlarge : V + E ≤ ‖heathBrownDyadicAggregate L X k s‖)
    (hlow : ‖heathBrownLowTotalDyadicAggregate L X k T0 t s‖ ≤ E) :
    V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖ := by
  have hsplit : heathBrownDyadicAggregate L X k s =
      heathBrownEligibleDyadicAggregate L X k T0 t s +
        heathBrownLowTotalDyadicAggregate L X k T0 t s := by
    rw [← heathBrownFlatDyadicAggregate_eq L X k s]
    exact heathBrownFlatDyadicAggregate_eq_eligible_add_lowTotal L X k T0 t s
  have htri : ‖heathBrownDyadicAggregate L X k s‖ ≤
      ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖ +
        ‖heathBrownLowTotalDyadicAggregate L X k T0 t s‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  linarith

/-- The dependent box type is inhabited for every nonempty Heath--Brown packet. -/
theorem nonempty_heathBrownBoxChoice
    (L X k : ℕ) (hk : 0 < k) : Nonempty (HeathBrownBoxChoice L X k) := by
  obtain ⟨label⟩ := nonempty_heathBrownSelectionLabel L X k hk
  exact ⟨label.1⟩

/-- **Eligible aggregate selection.**  A positive large value selects an actually eligible box;
the zero-index obstruction can no longer be returned by pigeonholing. -/
theorem exists_large_eligible_heathBrownBox
    (L X k : ℕ) (hk : 0 < k) (T0 t : ℝ) (s : ℂ) {V : ℝ}
    (hV : 0 < V)
    (hlarge : V ≤ ‖heathBrownEligibleDyadicAggregate L X k T0 t s‖) :
    ∃ c : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t c ∧
        V ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ‖heathBrownBoxTerm L X k c s‖ := by
  classical
  letI : Nonempty (HeathBrownBoxChoice L X k) :=
    nonempty_heathBrownBoxChoice L X k hk
  let f : HeathBrownBoxChoice L X k → ℂ := fun c =>
    if IsHeathBrownBoxEligible L X k T0 t c then heathBrownBoxTerm L X k c s else 0
  have hsum : heathBrownEligibleDyadicAggregate L X k T0 t s =
      ∑ c ∈ (Finset.univ : Finset (HeathBrownBoxChoice L X k)), f c := by
    simp [heathBrownEligibleDyadicAggregate, f]
  obtain ⟨c, _hc, hc⟩ := exists_mem_card_mul_norm_ge
    (Finset.univ : Finset (HeathBrownBoxChoice L X k)) Finset.univ_nonempty f
      (hlarge.trans_eq (congrArg norm hsum))
  have helig : IsHeathBrownBoxEligible L X k T0 t c := by
    by_contra hnot
    simp [f, hnot] at hc
    linarith
  refine ⟨c, helig, ?_⟩
  simpa [f, helig] using hc

end RHTower.Sieve
