import GaloisForLFunctions.RHTower.WindowBudget

namespace RHTower.Sieve

namespace StadlmannBoundedGaps

open Finset

noncomputable section

/-- Enlargement parameter used in the final numerical support. -/
def supportEpsilon : ℝ := 3 / 400

/-- Small bookkeeping parameter used in the equidistribution criterion. -/
def criterionEpsilon : ℝ := 1 / 10000000000

/-- Large-coordinate cutoff in the final numerical support. -/
def delta : ℝ := 7 / 250

/-- Upper endpoint of the one-shell support. -/
def supportEndpoint : ℝ := 253 / 1000

/-- Width above the Bombieri--Vinogradov quarter-simplex. -/
def omega : ℝ := supportEndpoint - 1 / 4

/-- Harman parameters in the final proof. -/
def xiOne : ℝ := 19 / 50

def xiTwo : ℝ := 2 / 5

def xiThree : ℝ := 2 / 5

/-- Budget for the sum of `m` large coordinates. -/
def largeCoordinateBudget (m : ℕ) : ℝ :=
  if m ≤ 2 then 3 / 20 else 17 / 100

theorem largeCoordinateBudget_delta_lt :
    ∀ m, delta < largeCoordinateBudget m := by
  intro m
  by_cases hm : m ≤ 2 <;> simp [largeCoordinateBudget, hm, delta] <;> norm_num

theorem largeCoordinateBudget_monotone : Monotone largeCoordinateBudget := by
  intro m n hmn
  by_cases hm : m ≤ 2
  · by_cases hn : n ≤ 2
    · simp [largeCoordinateBudget, hm, hn]
    · simp [largeCoordinateBudget, hm, hn]
      norm_num
  · have hn : ¬n ≤ 2 := fun hn => hm (hmn.trans hn)
    simp [largeCoordinateBudget, hm, hn]

theorem largeCoordinateBudget_step :
    ∀ m, largeCoordinateBudget (m + 1) ≤ largeCoordinateBudget m + delta := by
  intro m
  by_cases hnext : m + 1 ≤ 2
  · have hm : m ≤ 2 := by omega
    simp [largeCoordinateBudget, hnext, hm, delta]
    norm_num
  · by_cases hm : m ≤ 2
    · simp [largeCoordinateBudget, hnext, hm, delta]
      norm_num
    · simp [largeCoordinateBudget, hnext, hm, delta]
      norm_num

theorem largeCoordinateBudget_pair_le :
    ∀ m n, largeCoordinateBudget m + largeCoordinateBudget n ≤ 17 / 50 := by
  intro m n
  by_cases hm : m ≤ 2 <;> by_cases hn : n ≤ 2 <;>
    simp [largeCoordinateBudget, hm, hn] <;> norm_num

theorem largeCoordinateBudget_pair_le_of_small
    {m n : ℕ} (h : m ≤ 2 ∨ n ≤ 2) :
    largeCoordinateBudget m + largeCoordinateBudget n ≤ 8 / 25 := by
  rcases h with hm | hn
  · by_cases hn : n ≤ 2 <;> simp [largeCoordinateBudget, hm, hn] <;> norm_num
  · by_cases hm : m ≤ 2 <;> simp [largeCoordinateBudget, hm, hn] <;> norm_num

theorem largeCoordinateBudget_pair_le_of_both_small
    {m n : ℕ} (hm : m ≤ 2) (hn : n ≤ 2) :
    largeCoordinateBudget m + largeCoordinateBudget n ≤ 3 / 10 := by
  simp [largeCoordinateBudget, hm, hn]
  norm_num

/-- Definition 1's numerical side conditions for the final support. -/
theorem simplexSupportParameterCertificate :
    0 < supportEpsilon ∧
      0 < delta ∧
      -supportEpsilon < supportEndpoint ∧
      supportEndpoint < 1 / 2 - supportEpsilon ∧
      (∀ m, delta < largeCoordinateBudget m) ∧
      Monotone largeCoordinateBudget ∧
      (∀ m, largeCoordinateBudget (m + 1) ≤ largeCoordinateBudget m + delta) := by
  refine ⟨by norm_num [supportEpsilon], by norm_num [delta],
    by norm_num [supportEpsilon, supportEndpoint],
    by norm_num [supportEpsilon, supportEndpoint],
    largeCoordinateBudget_delta_lt, largeCoordinateBudget_monotone,
    largeCoordinateBudget_step⟩

/-- Proposition 2's five Harman-sieve inequalities at the final parameters. -/
theorem harmanParameterCertificate :
    2 * xiOne + 3 * xiTwo < 2 ∧
      xiTwo ≤ xiThree ∧
      xiOne + 9 * xiTwo < 4 ∧
      1 < 2 * xiOne + xiTwo ∧
      17 * xiTwo < 7 := by
  norm_num [xiOne, xiTwo, xiThree]

/-- Proposition 3(I): both entries of the minimum retain the required `delta` margin. -/
theorem typeIParameterCertificate :
    delta <
        min (xiOne - 4 * supportEndpoint + 2 / 3)
          (9 / 7 - 34 / 7 * supportEndpoint) - 2 * criterionEpsilon := by
  norm_num [delta, xiOne, supportEndpoint, criterionEpsilon, min_def]

/-- Proposition 3(II): numerical Type-II conditions at the final parameters. -/
theorem typeIIParameterCertificate :
    0 ≤ 19 / 2 - 36 * supportEndpoint - 13 * delta + 100 * criterionEpsilon ∧
      delta ≤
        min (xiTwo / 10 - 32 * supportEndpoint / 10 + 8 / 10)
          (xiTwo / 4 + 11 / 16 - 3 * supportEndpoint) - 2 * criterionEpsilon := by
  norm_num [delta, xiTwo, supportEndpoint, criterionEpsilon, min_def]

/-- Proposition 3(III): numerical Type-III condition at the final parameters. -/
theorem typeIIIParameterCertificate :
    delta < 11 / 8 - 7 / 2 * supportEndpoint - 9 / 8 * xiThree -
      2 * criterionEpsilon := by
  norm_num [delta, xiThree, supportEndpoint, criterionEpsilon]

/-- The four all-in-first-bin capacities used for conditions A, B, C, and E. -/
theorem allInFirstBinCapacityCertificate :
    17 / 50 < xiOne - 2 * criterionEpsilon ∧
      17 / 50 < 2 / 5 + 24 * omega / 5 + 7 * delta / 5 - 2 * criterionEpsilon ∧
      17 / 50 < 1 / 3 + 24 * omega / 3 + 7 * delta / 3 -
        4 * criterionEpsilon ∧
      17 / 50 < 1 - 6 * omega - 3 * xiThree / 2 - 2 * criterionEpsilon := by
  norm_num [xiOne, xiThree, criterionEpsilon, omega, supportEndpoint, delta]

/-- Empty complementary bins meet the remaining A, B, C, and E capacities. -/
theorem emptyComplementaryBinCertificate :
    0 ≤ 1 / 6 - 4 * omega - 2 * criterionEpsilon ∧
      0 ≤ 1 / 14 - 24 * omega / 7 - 2 * criterionEpsilon ∧
      0 ≤ 1 / 10 - 34 * omega / 5 - 7 * delta / 5 -
        4 * criterionEpsilon ∧
      0 ≤ 1 / 35 + 22 * omega / 35 + 21 * delta / 35 -
        4 * criterionEpsilon ∧
      0 ≤ 5 * omega / 2 + 3 * xiThree / 8 - 2 * criterionEpsilon := by
  norm_num [xiThree, criterionEpsilon, omega, supportEndpoint, delta]

/-- A concrete member of the paper's `Xi(B_m,B_n,m,n,delta)` set. -/
structure XiTuple (m n : ℕ) where
  left : Fin m → ℝ
  right : Fin n → ℝ
  left_lower : ∀ i, delta ≤ left i
  right_lower : ∀ i, delta ≤ right i
  left_upper : ∀ i, left i ≤ 1
  right_upper : ∀ i, right i ≤ 1
  left_sum_le : (∑ i, left i) ≤ largeCoordinateBudget m
  right_sum_le : (∑ i, right i) ≤ largeCoordinateBudget n

abbrev XiIndex (m n : ℕ) := Fin m ⊕ Fin n

def XiTuple.weight {m n : ℕ} (x : XiTuple m n) : XiIndex m n → ℝ :=
  Sum.elim x.left x.right

theorem XiTuple.sum_weight {m n : ℕ} (x : XiTuple m n) :
    (∑ i, x.weight i) = (∑ i, x.left i) + ∑ i, x.right i := by
  exact Fintype.sum_sum_type x.weight

theorem XiTuple.total_weight_le_budget {m n : ℕ} (x : XiTuple m n) :
    (∑ i, x.weight i) ≤ largeCoordinateBudget m + largeCoordinateBudget n := by
  rw [x.sum_weight]
  exact add_le_add x.left_sum_le x.right_sum_le

def IsTwoPartition {α : Type*} [Fintype α] [DecidableEq α]
    (I₁ I₂ : Finset α) : Prop :=
  I₁ ∪ I₂ = Finset.univ ∧ Disjoint I₁ I₂

def IsThreePartition {α : Type*} [Fintype α] [DecidableEq α]
    (I₁ I₂ I₃ : Finset α) : Prop :=
  I₁ ∪ I₂ ∪ I₃ = Finset.univ ∧
    Disjoint I₁ I₂ ∧ Disjoint I₁ I₃ ∧ Disjoint I₂ I₃

def TypeIPartitionCondition {m n : ℕ} (x : XiTuple m n) : Prop :=
  ∃ I₁ I₂ : Finset (XiIndex m n),
    IsTwoPartition I₁ I₂ ∧
      (∑ i ∈ I₁, x.weight i) ≤ xiOne - 2 * criterionEpsilon ∧
      (∑ i ∈ I₂, x.weight i) ≤
        1 / 6 - 4 * omega - 2 * criterionEpsilon

def TypeIIaPartitionCondition {m n : ℕ} (x : XiTuple m n) : Prop :=
  ∃ I₁ I₂ : Finset (XiIndex m n),
    IsTwoPartition I₁ I₂ ∧
      (∑ i ∈ I₁, x.weight i) ≤
        2 / 5 + 24 * omega / 5 + 7 * delta / 5 - 2 * criterionEpsilon ∧
      (∑ i ∈ I₂, x.weight i) ≤
        1 / 14 - 24 * omega / 7 - 2 * criterionEpsilon

def TypeIIbPartitionCondition {m n : ℕ} (x : XiTuple m n) : Prop :=
  ∃ I₁ I₂ I₃ : Finset (XiIndex m n),
    IsThreePartition I₁ I₂ I₃ ∧
      (∑ i ∈ I₁, x.weight i) ≤
        1 / 3 + 24 * omega / 3 + 7 * delta / 3 - 4 * criterionEpsilon ∧
      (∑ i ∈ I₂, x.weight i) ≤
        1 / 10 - 34 * omega / 5 - 7 * delta / 5 - 4 * criterionEpsilon ∧
      (∑ i ∈ I₃, x.weight i) ≤
        1 / 35 + 22 * omega / 35 + 21 * delta / 35 - 4 * criterionEpsilon

def TypeIIIPartitionCondition {m n : ℕ} (x : XiTuple m n) : Prop :=
  ∃ I₁ I₂ : Finset (XiIndex m n),
    IsTwoPartition I₁ I₂ ∧
      (∑ i ∈ I₁, x.weight i) ≤
        1 - 6 * omega - 3 * xiThree / 2 - 2 * criterionEpsilon ∧
      (∑ i ∈ I₂, x.weight i) ≤
        5 * omega / 2 + 3 * xiThree / 8 - 2 * criterionEpsilon

/-- Proposition 3(A): the full coordinate set fits in the first bin. -/
theorem XiTuple.typeIPartitionCondition {m n : ℕ} (x : XiTuple m n) :
    TypeIPartitionCondition x := by
  classical
  rcases allInFirstBinCapacityCertificate with ⟨hfirst, -, -, -⟩
  rcases emptyComplementaryBinCertificate with ⟨hsecond, -, -, -, -⟩
  refine ⟨Finset.univ, ∅, by simp [IsTwoPartition], ?_, ?_⟩
  · simpa using (x.total_weight_le_budget.trans
      (largeCoordinateBudget_pair_le m n)).trans hfirst.le
  · simpa using hsecond

/-- Proposition 3(B): the full coordinate set fits in the first bin. -/
theorem XiTuple.typeIIaPartitionCondition {m n : ℕ} (x : XiTuple m n) :
    TypeIIaPartitionCondition x := by
  classical
  rcases allInFirstBinCapacityCertificate with ⟨-, hfirst, -, -⟩
  rcases emptyComplementaryBinCertificate with ⟨-, hsecond, -, -, -⟩
  refine ⟨Finset.univ, ∅, by simp [IsTwoPartition], ?_, ?_⟩
  · simpa using (x.total_weight_le_budget.trans
      (largeCoordinateBudget_pair_le m n)).trans hfirst.le
  · simpa using hsecond

/-- Proposition 3(C): the full coordinate set fits in the first bin. -/
theorem XiTuple.typeIIbPartitionCondition {m n : ℕ} (x : XiTuple m n) :
    TypeIIbPartitionCondition x := by
  classical
  rcases allInFirstBinCapacityCertificate with ⟨-, -, hfirst, -⟩
  rcases emptyComplementaryBinCertificate with ⟨-, -, hsecond, hthird, -⟩
  refine ⟨Finset.univ, ∅, ∅, by simp [IsThreePartition], ?_, ?_, ?_⟩
  · simpa using (x.total_weight_le_budget.trans
      (largeCoordinateBudget_pair_le m n)).trans hfirst.le
  · simpa using hsecond
  · simpa using hthird

/-- Proposition 3(E): the full coordinate set fits in the first bin. -/
theorem XiTuple.typeIIIPartitionCondition {m n : ℕ} (x : XiTuple m n) :
    TypeIIIPartitionCondition x := by
  classical
  rcases allInFirstBinCapacityCertificate with ⟨-, -, -, hfirst⟩
  rcases emptyComplementaryBinCertificate with ⟨-, -, -, -, hsecond⟩
  refine ⟨Finset.univ, ∅, by simp [IsTwoPartition], ?_, ?_⟩
  · simpa using (x.total_weight_le_budget.trans
      (largeCoordinateBudget_pair_le m n)).trans hfirst.le
  · simpa using hsecond

private theorem XiTuple.exists_left_le {m n : ℕ} (x : XiTuple m n) (hm : 3 ≤ m) :
    ∃ i, x.left i ≤ 17 / 300 := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  have hmReal : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hbudget : largeCoordinateBudget m = 17 / 100 := by
    simp [largeCoordinateBudget, show ¬m ≤ 2 by omega]
  have hsum : (∑ i, x.left i) ≤ ∑ _i : Fin m, (17 / 300 : ℝ) := by
    calc
      (∑ i, x.left i) ≤ largeCoordinateBudget m := x.left_sum_le
      _ = 17 / 100 := hbudget
      _ ≤ (m : ℝ) * (17 / 300) := by nlinarith
      _ = ∑ _i : Fin m, (17 / 300 : ℝ) := by simp
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨i, hi⟩

private theorem XiTuple.exists_right_le {m n : ℕ} (x : XiTuple m n) (hn : 3 ≤ n) :
    ∃ i, x.right i ≤ 17 / 300 := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hbudget : largeCoordinateBudget n = 17 / 100 := by
    simp [largeCoordinateBudget, show ¬n ≤ 2 by omega]
  have hsum : (∑ i, x.right i) ≤ ∑ _i : Fin n, (17 / 300 : ℝ) := by
    calc
      (∑ i, x.right i) ≤ largeCoordinateBudget n := x.right_sum_le
      _ = 17 / 100 := hbudget
      _ ≤ (n : ℝ) * (17 / 300) := by nlinarith
      _ = ∑ _i : Fin n, (17 / 300 : ℝ) := by simp
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨i, hi⟩

/-- Strong two-bin certificate behind the final proof's Type-IIc partition.
The first bin has mass at most `0.312`, leaving a uniform margin below `0.32`. -/
theorem XiTuple.exists_typeIIc_twoBinSplit :
    ∀ {m n : ℕ} (x : XiTuple m n),
      ∃ I₂ : Finset (XiIndex m n),
        (∑ i ∈ I₂, x.weight i) ≤ 7 / 100 ∧
        (∑ i ∈ (Finset.univ \ I₂), x.weight i) ≤ 39 / 125 := by
  intro m n x
  classical
  have htotal : (∑ i, x.weight i) ≤ 17 / 50 :=
    x.total_weight_le_budget.trans (largeCoordinateBudget_pair_le m n)
  by_cases hm : m ≤ 2
  · by_cases hn : n ≤ 2
    · refine ⟨∅, by norm_num, ?_⟩
      apply x.total_weight_le_budget.trans
      exact (largeCoordinateBudget_pair_le_of_both_small hm hn).trans (by norm_num)
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨i, hi⟩ := x.exists_right_le hn3
      let idx : XiIndex m n := Sum.inr i
      refine ⟨{idx}, ?_, ?_⟩
      · simp [idx, XiTuple.weight]
        linarith
      · have hlower : delta ≤ x.weight idx := x.right_lower i
        have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (XiIndex m n))
          x.weight (Finset.mem_univ idx)
        have hcomp : (∑ j ∈ (Finset.univ : Finset (XiIndex m n)).erase idx,
            x.weight j) ≤ 39 / 125 := by
          calc
            _ = (∑ j, x.weight j) - x.weight idx := by linarith only [hdecomp]
            _ ≤ 17 / 50 - delta := sub_le_sub htotal hlower
            _ = 39 / 125 := by norm_num [delta]
        simpa [idx] using hcomp
  · have hm3 : 3 ≤ m := by omega
    obtain ⟨i, hi⟩ := x.exists_left_le hm3
    let idx : XiIndex m n := Sum.inl i
    refine ⟨{idx}, ?_, ?_⟩
    · simp [idx, XiTuple.weight]
      linarith
    · have hlower : delta ≤ x.weight idx := x.left_lower i
      have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (XiIndex m n))
        x.weight (Finset.mem_univ idx)
      have hcomp : (∑ j ∈ (Finset.univ : Finset (XiIndex m n)).erase idx,
          x.weight j) ≤ 39 / 125 := by
        calc
          _ = (∑ j, x.weight j) - x.weight idx := by linarith only [hdecomp]
          _ ≤ 17 / 50 - delta := sub_le_sub htotal hlower
          _ = 39 / 125 := by norm_num [delta]
      simpa [idx] using hcomp

def IsFourPartition {α : Type*} [Fintype α] [DecidableEq α]
    (I₁ I₂ I₃ I₄ : Finset α) : Prop :=
  I₁ ∪ I₂ ∪ I₃ ∪ I₄ = Finset.univ ∧
    Disjoint I₁ I₂ ∧ Disjoint I₁ I₃ ∧ Disjoint I₁ I₄ ∧
    Disjoint I₂ I₃ ∧ Disjoint I₂ I₄ ∧ Disjoint I₃ I₄

def TypeIIcPartitionAt {m n : ℕ} (x : XiTuple m n) (ω₀ γ : ℝ) : Prop :=
  ∃ I₁ I₂ I₃ I₄ : Finset (XiIndex m n),
    IsFourPartition I₁ I₂ I₃ I₄ ∧
      (∑ i ∈ I₁, x.weight i) ≤ γ - 2 * delta - 8 * ω₀ - criterionEpsilon ∧
      (∑ i ∈ I₂, x.weight i) ≤ 1 / 2 - γ - 2 * ω₀ - criterionEpsilon ∧
      (∑ i ∈ I₃, x.weight i) ≤ 4 * ω₀ + delta - criterionEpsilon ∧
      (∑ i ∈ I₄, x.weight i) ≤ 8 * ω₀

def paperXiWitness : XiTuple 1 1 where
  left := fun _ => delta
  right := fun _ => delta
  left_lower := fun _ => le_rfl
  right_lower := fun _ => le_rfl
  left_upper := by intro; norm_num [delta]
  right_upper := by intro; norm_num [delta]
  left_sum_le := by norm_num [delta, largeCoordinateBudget]
  right_sum_le := by norm_num [delta, largeCoordinateBudget]

/-- Literal Type-IIc range in Proposition 3, restricted to one nonempty `Xi` member. -/
def PaperTypeIIcCondition : Prop :=
  ∀ ω₀ γ : ℝ,
    -criterionEpsilon ≤ ω₀ →
    ω₀ ≤ omega →
    xiTwo - criterionEpsilon ≤ γ →
    γ ≤ 1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon →
    TypeIIcPartitionAt paperXiWitness ω₀ γ

/-- Proposition 3's Type-IIc condition is inconsistent at its negative endpoint. -/
theorem not_paperTypeIIcCondition : ¬PaperTypeIIcCondition := by
  intro h
  have hω : -criterionEpsilon ≤ omega := by
    norm_num [criterionEpsilon, omega, supportEndpoint]
  have hγlo : xiTwo - criterionEpsilon ≤ xiTwo := by
    norm_num [xiTwo, criterionEpsilon]
  have hγhi : xiTwo ≤
      1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon := by
    norm_num [xiTwo, criterionEpsilon, omega, supportEndpoint, delta]
  obtain ⟨I₁, I₂, I₃, I₄, -, -, -, -, hI₄⟩ :=
    h (-criterionEpsilon) xiTwo le_rfl hω hγlo hγhi
  have hnonneg : 0 ≤ ∑ i ∈ I₄, paperXiWitness.weight i := by
    apply Finset.sum_nonneg
    intro i hi
    rcases i with i | i <;> simp [paperXiWitness, XiTuple.weight, delta]
    all_goals norm_num
  norm_num [criterionEpsilon] at hI₄
  linarith

/-- Literal universal Type-IIc obligation imposed by Proposition 3 at the final parameters. -/
def LiteralPaperTypeIIcCondition : Prop :=
  ∀ (m n : ℕ) (x : XiTuple m n) (ω₀ γ : ℝ),
    -criterionEpsilon ≤ ω₀ →
    ω₀ ≤ omega →
    xiTwo - criterionEpsilon ≤ γ →
    γ ≤ 1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon →
    TypeIIcPartitionAt x ω₀ γ

/-- The universal published Type-IIc obligation fails already at `m = n = 1`. -/
theorem not_literalPaperTypeIIcCondition : ¬LiteralPaperTypeIIcCondition := by
  intro h
  apply not_paperTypeIIcCondition
  intro ω₀ γ hω₀ hω hγlo hγhi
  exact h 1 1 paperXiWitness ω₀ γ hω₀ hω hγlo hγhi

/-- Type-IIc condition with the forced correction `0 ≤ ω₀`. -/
def CorrectedTypeIIcCondition : Prop :=
  ∀ (m n : ℕ) (x : XiTuple m n) (ω₀ γ : ℝ),
    0 ≤ ω₀ →
    ω₀ ≤ omega →
    xiTwo - criterionEpsilon ≤ γ →
    γ ≤ 1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon →
    TypeIIcPartitionAt x ω₀ γ

/-- All finite tuple partitions close after replacing the impossible negative endpoint by zero. -/
theorem correctedTypeIIcCondition : CorrectedTypeIIcCondition := by
  intro m n x ω₀ γ hω₀ hω hγlo hγhi
  classical
  obtain ⟨I₂, hI₂, hI₁⟩ := x.exists_typeIIc_twoBinSplit
  refine ⟨Finset.univ \ I₂, I₂, ∅, ∅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsFourPartition]
    refine ⟨by simp, Finset.disjoint_sdiff.symm, by simp, by simp, by simp, by simp, by simp⟩
  · apply hI₁.trans
    norm_num [delta, criterionEpsilon, xiTwo, omega, supportEndpoint] at hω hγlo ⊢
    linarith
  · apply hI₂.trans
    norm_num [delta, criterionEpsilon, omega, supportEndpoint] at hω hγhi ⊢
    linarith
  · simp only [Finset.sum_empty]
    norm_num [delta, criterionEpsilon] at hω₀ ⊢
    linarith
  · simp only [Finset.sum_empty]
    linarith

/-- Closed certificate for every finite partition condition in Proposition 3 after the forced
Type-IIc endpoint repair. -/
theorem correctedPropositionThreePartitionCertificate :
    ∀ (m n : ℕ) (x : XiTuple m n),
      TypeIPartitionCondition x ∧
        TypeIIaPartitionCondition x ∧
        TypeIIbPartitionCondition x ∧
        (∀ ω₀ γ : ℝ,
          0 ≤ ω₀ →
          ω₀ ≤ omega →
          xiTwo - criterionEpsilon ≤ γ →
          γ ≤ 1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon →
          TypeIIcPartitionAt x ω₀ γ) ∧
        TypeIIIPartitionCondition x := by
  intro m n x
  refine ⟨x.typeIPartitionCondition, x.typeIIaPartitionCondition,
    x.typeIIbPartitionCondition, ?_, x.typeIIIPartitionCondition⟩
  intro ω₀ γ hω₀ hω hγlo hγhi
  exact correctedTypeIIcCondition m n x ω₀ γ hω₀ hω hγlo hγhi

end

end StadlmannBoundedGaps

end RHTower.Sieve
