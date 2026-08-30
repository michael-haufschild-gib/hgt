import GaloisForLFunctions.HTGeometry.SourceLawJetPromotion

/-!
# Singular law blow-up and exceptional-port reconstruction

An ordinary prolonged product law reconstructs a withheld response from a nonzero zeroth
multiplier port.  Singular completion can erase that port and several successors.  This module
proves that the first nonzero multiplier jet supplies a canonical exceptional chart: every lower
target coefficient vanishes, every withheld coefficient is reconstructed recursively, and the
complete product formation remains injective for every nonzero multiplier history.

The result is algebraic.  It does not assert boundedness of the inverse exceptional chart, a
cofinal bound on first active order, or an RH-facing source landing.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {F : Type*} [Field F]

/-- The order-`k` exceptional chart of a Hasse product. -/
def exceptionalHasseJetMul (q m : ℕ → F) (k n : ℕ) : F :=
  ∑ j ∈ Finset.range (n + 1), q j * m (k + n - j)

/-- If the multiplier vanishes below order `k`, the ordinary Hasse product is already its
order-`k` exceptional chart. -/
theorem hasseJetMul_eq_exceptional_of_vanishBelow
    {q m : ℕ → F} {k n : ℕ}
    (hm : ∀ r < k, m r = 0) :
    hasseJetMul q m (k + n) = exceptionalHasseJetMul q m k n := by
  rw [hasseJetMul, exceptionalHasseJetMul]
  rw [show k + n + 1 = (n + 1) + k by omega, Finset.sum_range_add]
  have htail :
      ∑ j ∈ Finset.range k,
          q (n + 1 + j) * m (k + n - (n + 1 + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hm]
    · simp
    · have hjk := Finset.mem_range.mp hj
      omega
  rw [htail, add_zero]

/-- Every target coefficient below the first nonzero multiplier jet vanishes: blow-down reaches
the simultaneous base locus. -/
theorem prolongedProductLaw_target_vanishBelow
    {c : F} {q m h : ℕ → F} {k r : ℕ}
    (hlaw : IsProlongedProductLaw c q m h)
    (hm : ∀ s < k, m s = 0) (hr : r < k) :
    c * h r = 0 := by
  rw [← hlaw r, hasseJetMul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hm]
  · simp
  · have hjr := Finset.mem_range.mp hj
    omega

/-- **Singular all-order reconstruction.**  The first nonzero multiplier jet, at arbitrary order
`k`, replaces the vanished zeroth port and recovers every withheld coefficient. -/
theorem prolongedProductLaw_singular_reconstruct
    {c : F} {q m h : ℕ → F} {k : ℕ}
    (hlaw : IsProlongedProductLaw c q m h)
    (hm : ∀ r < k, m r = 0) (hmk : m k ≠ 0) (n : ℕ) :
    q n =
      (c * h (k + n) -
        ∑ j ∈ Finset.range n, q j * m (k + n - j)) / m k := by
  have hn := hlaw (k + n)
  rw [hasseJetMul_eq_exceptional_of_vanishBelow hm,
    exceptionalHasseJetMul, Finset.sum_range_succ] at hn
  have hidx : k + n - n = k := by omega
  simp only [hidx] at hn
  apply (eq_div_iff hmk).2
  linear_combination hn

/-- Exceptional leading direction: the order-`k` target coefficient divided by the first
nonzero admission coefficient is exactly the zeroth withheld response. -/
theorem prolongedProductLaw_exceptionalDirection
    {c : F} {q m h : ℕ → F} {k : ℕ}
    (hlaw : IsProlongedProductLaw c q m h)
    (hm : ∀ r < k, m r = 0) (hmk : m k ≠ 0) :
    q 0 = c * h k / m k := by
  simpa using prolongedProductLaw_singular_reconstruct hlaw hm hmk 0

/-- The complete withheld response remains unique even when the ordinary leading port vanishes,
provided some finite exceptional jet is the first nonzero port. -/
theorem prolongedProductLaw_singular_unique
    {c : F} {q q' m h : ℕ → F} {k : ℕ}
    (hlaw : IsProlongedProductLaw c q m h)
    (hlaw' : IsProlongedProductLaw c q' m h)
    (hm : ∀ r < k, m r = 0) (hmk : m k ≠ 0) :
    q = q' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [prolongedProductLaw_singular_reconstruct hlaw hm hmk n,
        prolongedProductLaw_singular_reconstruct hlaw' hm hmk n]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]

/-- **Global singular formation theorem.**  Multiplication by any nonzero Hasse jet is injective
on complete response histories.  No zeroth-port inverse and no uniform lower bound are needed: the
first nonzero exceptional layer supplies the reconstructing chart. -/
theorem hasseJetMul_left_injective_of_exists_ne_zero
    {m : ℕ → F} (hm : ∃ k, m k ≠ 0) :
    Function.Injective (fun q : ℕ → F => hasseJetMul q m) := by
  classical
  intro q q' hqq'
  let k := Nat.find hm
  have hmk : m k ≠ 0 := Nat.find_spec hm
  have hbelow : ∀ r < k, m r = 0 := by
    intro r hr
    by_contra hmr
    exact (not_lt_of_ge (Nat.find_min' hm hmr)) hr
  apply prolongedProductLaw_singular_unique
      (c := (1 : F)) (m := m) (h := hasseJetMul q m)
      (k := k) (q := q) (q' := q')
  · intro n
    simp
  · intro n
    simpa using (congrFun hqq' n).symm
  · exact hbelow
  · exact hmk

/-- **Cofinal active-order dichotomy.**  Every moving exceptional order either returns to one
fixed finite chart cofinally often, or escapes every finite jet depth.  There is no third failure
mode between finite-chart reconstruction and infinite-order escape. -/
theorem fixed_chart_frequently_or_activeOrder_tendsto_atTop (κ : ℕ → ℕ) :
    (∃ k, ∃ᶠ n in Filter.atTop, κ n = k) ∨
      Filter.Tendsto κ Filter.atTop Filter.atTop := by
  by_cases hescape : Filter.Tendsto κ Filter.atTop Filter.atTop
  · exact Or.inr hescape
  · left
    have hnot := hescape
    rw [Filter.tendsto_atTop_atTop] at hnot
    push Not at hnot
    obtain ⟨b, hb⟩ := hnot
    have hfreq : ∃ᶠ n in Filter.atTop, κ n < b := by
      rw [Filter.Frequently]
      intro hevent
      rw [Filter.eventually_atTop] at hevent
      obtain ⟨N, hN⟩ := hevent
      obtain ⟨n, hnN, hnb⟩ := hb N
      exact hN n hnN hnb
    have hfreqExists :
        ∃ᶠ n in Filter.atTop, ∃ k ∈ Finset.range b, κ n = k :=
      hfreq.mono fun n hn => ⟨κ n, Finset.mem_range.mpr hn, rfl⟩
    obtain ⟨k, hk, hkfreq⟩ :=
      (Finset.frequently_exists (Finset.range b)).mp hfreqExists
    exact ⟨k, hkfreq⟩

/-- A Hasse history first activates at order `k`. -/
def FirstActiveHasseOrderAt (m : ℕ → F) (k : ℕ) : Prop :=
  (∀ r < k, m r = 0) ∧ m k ≠ 0

/-- Two vanishing histories have vanishing product below the sum of their active orders. -/
theorem hasseJetMul_vanishBelow_add
    {m n : ℕ → F} {k l r : ℕ}
    (hm : ∀ i < k, m i = 0) (hn : ∀ j < l, n j = 0)
    (hr : r < k + l) :
    hasseJetMul m n r = 0 := by
  rw [hasseJetMul]
  apply Finset.sum_eq_zero
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hjk : j < k
  · rw [hm j hjk]
    simp
  · rw [hn]
    · simp
    · omega

/-- The leading fused exceptional port is the product of the two leading ports. -/
theorem hasseJetMul_leading_add
    {m n : ℕ → F} {k l : ℕ}
    (hm : ∀ i < k, m i = 0) (hn : ∀ j < l, n j = 0) :
    hasseJetMul m n (k + l) = m k * n l := by
  rw [show k + l = l + k by omega,
    hasseJetMul_eq_exceptional_of_vanishBelow hn,
    exceptionalHasseJetMul, Finset.sum_range_succ]
  have hsum :
      ∑ j ∈ Finset.range k, m j * n (l + k - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hm j (Finset.mem_range.mp hj)]
    simp
  rw [hsum, zero_add]
  congr 2
  omega

/-- **Additive exceptional-depth conservation.**  Fusion adds first active orders and multiplies
their leading exceptional ports. -/
theorem FirstActiveHasseOrderAt.mul
    {m n : ℕ → F} {k l : ℕ}
    (hm : FirstActiveHasseOrderAt m k)
    (hn : FirstActiveHasseOrderAt n l) :
    FirstActiveHasseOrderAt (hasseJetMul m n) (k + l) := by
  constructor
  · intro r hr
    exact hasseJetMul_vanishBelow_add hm.1 hn.1 hr
  · rw [hasseJetMul_leading_add hm.1 hn.1]
    exact mul_ne_zero hm.2 hn.2

/-- Unit admission concentrated on one exceptional layer. -/
def exceptionalUnitJet (k : ℕ) : ℕ → F := fun r => if r = k then 1 else 0

/-- Closed normal-form model: multiplication by an order-`k` exceptional unit is exactly the
`k`-step shift, so the entire response history survives a blow-down with `k` vanished layers. -/
theorem hasseJetMul_exceptionalUnitJet (q : ℕ → F) (k n : ℕ) :
    hasseJetMul q (exceptionalUnitJet k) (k + n) = q n := by
  have hlaw :
      IsProlongedProductLaw (1 : F) q (exceptionalUnitJet k)
        (hasseJetMul q (exceptionalUnitJet k)) := by
    intro r
    simp
  have hbelow : ∀ r < k, exceptionalUnitJet (F := F) k r = 0 := by
    intro r hr
    simp [exceptionalUnitJet, ne_of_lt hr]
  have hmk : exceptionalUnitJet (F := F) k k ≠ 0 := by
    simp [exceptionalUnitJet]
  have hrec :=
    prolongedProductLaw_singular_reconstruct hlaw hbelow hmk n
  have hsum :
      ∑ j ∈ Finset.range n,
          q j * exceptionalUnitJet (F := F) k (k + n - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn := Finset.mem_range.mp hj
    simp [exceptionalUnitJet]
    omega
  rw [hsum] at hrec
  simpa [exceptionalUnitJet] using hrec.symm

end

end HTGeometry
