import Mathlib

/-!
# Partitions by occupation numbers and the shift bijection

A partition is recorded by its occupation numbers: `g j` is the number of parts equal to `j + 1`.
Removing one from every part sends the partitions with exactly `n` parts to the partitions with at
most `n` parts and drops the size by exactly `n`.  This single bijection carries both halves of
Euler's generating-function computation for partitions with a prescribed number of parts.
-/

namespace GaloisForLFunctions.HTGeometry

open Finsupp

noncomputable section

/-- Occupation numbers of a partition: `g j` is the number of parts equal to `j + 1`. -/
abbrev PartConfig := ℕ →₀ ℕ

/-- The number of parts of a configuration. -/
def partCount (g : PartConfig) : ℕ := g.sum fun _ m => m

/-- The size of a configuration: the sum of its parts. -/
def partSize (g : PartConfig) : ℕ := g.sum fun j m => (j + 1) * m

@[simp] theorem partCount_zero : partCount 0 = 0 := by
  rw [partCount, Finsupp.sum_zero_index]

@[simp] theorem partSize_zero : partSize 0 = 0 := by
  rw [partSize, Finsupp.sum_zero_index]

/-! ## Adding one to every part -/

/-- Raise every part by one and adjoin `a` parts equal to one. -/
def unshift (a : ℕ) (h : PartConfig) : PartConfig :=
  Finsupp.single 0 a + Finsupp.mapDomain Nat.succ h

theorem partCount_unshift (a : ℕ) (h : PartConfig) :
    partCount (unshift a h) = a + partCount h := by
  rw [unshift, partCount, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl,
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  rfl

theorem partSize_unshift (a : ℕ) (h : PartConfig) :
    partSize (unshift a h) = a + (partSize h + partCount h) := by
  rw [unshift, partSize, Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring),
    Finsupp.sum_single_index (by ring),
    Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)]
  have hsplit : (h.sum fun a b => (Nat.succ a + 1) * b)
      = (h.sum fun a b => (a + 1) * b) + h.sum fun _ b => b := by
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun j _ => ?_
    simp only [Nat.succ_eq_add_one]
    ring
  rw [hsplit, partSize, partCount]
  ring

/-! ## Removing one from every part -/

/-- Lower every part by one, discarding the parts equal to one. -/
def shift (g : PartConfig) : PartConfig :=
  Finsupp.comapDomain Nat.succ g (Nat.succ_injective.injOn)

@[simp] theorem shift_apply (g : PartConfig) (j : ℕ) : shift g j = g (j + 1) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem unshift_shift (g : PartConfig) : unshift (g 0) (shift g) = g := by
  refine Finsupp.ext fun j => ?_
  rcases j with _ | k
  · rw [unshift, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp
  · rw [unshift, Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp),
      Finsupp.mapDomain_apply Nat.succ_injective]
    simp

theorem partCount_eq (g : PartConfig) : partCount g = g 0 + partCount (shift g) := by
  conv_lhs => rw [← unshift_shift g]
  rw [partCount_unshift]

theorem partSize_eq (g : PartConfig) :
    partSize g = g 0 + (partSize (shift g) + partCount (shift g)) := by
  conv_lhs => rw [← unshift_shift g]
  rw [partSize_unshift]

theorem partCount_shift_le (g : PartConfig) : partCount (shift g) ≤ partCount g := by
  rw [partCount_eq g]
  exact Nat.le_add_left _ _

/-- **The size drops by exactly the number of parts.** -/
theorem partSize_eq_add_partSize_shift {n : ℕ} {g : PartConfig} (hg : partCount g = n) :
    partSize g = n + partSize (shift g) := by
  have hc := partCount_eq g
  rw [hg] at hc
  rw [partSize_eq g]
  omega

theorem shift_unshift (a : ℕ) (h : PartConfig) : shift (unshift a h) = h := by
  refine Finsupp.ext fun j => ?_
  rw [shift_apply, unshift, Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp),
    Finsupp.mapDomain_apply Nat.succ_injective]
  simp

/-! ## The bijection -/

/-- **Removing one from every part** is a bijection from the configurations with exactly `n` parts
to the configurations with at most `n` parts. -/
def shiftEquiv (n : ℕ) :
    {g : PartConfig // partCount g = n} ≃ {h : PartConfig // partCount h ≤ n} where
  toFun g := ⟨shift g.1, by
    have h1 := partCount_shift_le g.1
    have h2 := g.2
    omega⟩
  invFun h := ⟨unshift (n - partCount h.1) h.1, by
    rw [partCount_unshift]
    have hle := h.2
    omega⟩
  left_inv g := by
    refine Subtype.ext ?_
    show unshift (n - partCount (shift g.1)) (shift g.1) = g.1
    have hc := partCount_eq g.1
    rw [g.2] at hc
    have h0 : n - partCount (shift g.1) = g.1 0 := by omega
    rw [h0, unshift_shift]
  right_inv h := by
    refine Subtype.ext ?_
    show shift (unshift (n - partCount h.1) h.1) = h.1
    rw [shift_unshift]

@[simp] theorem shiftEquiv_apply (n : ℕ) (g : {g : PartConfig // partCount g = n}) :
    ((shiftEquiv n) g).1 = shift g.1 := rfl

@[simp] theorem shiftEquiv_symm_apply (n : ℕ) (h : {h : PartConfig // partCount h ≤ n}) :
    ((shiftEquiv n).symm h).1 = unshift (n - partCount h.1) h.1 := rfl

/-! ## Generating functions -/

open scoped ENNReal

/-- The generating function of the partitions with exactly `n` parts. -/
def exactGF (q : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' g : {g : PartConfig // partCount g = n}, q ^ partSize g.1

/-- The generating function of the partitions with at most `n` parts. -/
def atMostGF (q : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' h : {h : PartConfig // partCount h ≤ n}, q ^ partSize h.1

/-- **Euler's shift.**  Removing one from every part factors `qⁿ` out of the exact generating
function. -/
theorem exactGF_eq_mul (q : ℝ≥0∞) (n : ℕ) : exactGF q n = q ^ n * atMostGF q n := by
  rw [exactGF, atMostGF, ← ENNReal.tsum_mul_left,
    ← (shiftEquiv n).tsum_eq (fun h : {h : PartConfig // partCount h ≤ n} =>
      q ^ n * q ^ partSize h.1)]
  refine tsum_congr fun g => ?_
  rw [shiftEquiv_apply, ← pow_add]
  congr 1
  exact partSize_eq_add_partSize_shift g.2

theorem partCount_eq_zero_iff (h : PartConfig) : partCount h = 0 ↔ h = 0 := by
  constructor
  · intro h0
    refine Finsupp.ext fun j => ?_
    by_cases hj : j ∈ h.support
    · have := (Finset.sum_eq_zero_iff.mp h0) j hj
      simpa using this
    · simpa using Finsupp.notMem_support_iff.mp hj
  · rintro rfl
    exact partCount_zero

theorem atMostGF_zero (q : ℝ≥0∞) : atMostGF q 0 = 1 := by
  rw [atMostGF]
  have hsingle : ∀ b : {h : PartConfig // partCount h ≤ 0},
      b ≠ ⟨0, by simp⟩ → q ^ partSize b.1 = 0 := by
    intro b hb
    exact absurd (Subtype.ext ((partCount_eq_zero_iff b.1).mp (Nat.le_zero.mp b.2))) hb
  rw [tsum_eq_single ⟨0, by simp⟩ hsingle]
  simp

theorem atMostGF_succ (q : ℝ≥0∞) (n : ℕ) :
    atMostGF q (n + 1) = atMostGF q n + exactGF q (n + 1) := by
  have hA := tsum_subtype {g : PartConfig | partCount g ≤ n + 1} (fun g => q ^ partSize g)
  have hB := tsum_subtype {g : PartConfig | partCount g ≤ n} (fun g => q ^ partSize g)
  have hC := tsum_subtype {g : PartConfig | partCount g = n + 1} (fun g => q ^ partSize g)
  have hsplit : (∑' g : PartConfig,
        {g : PartConfig | partCount g ≤ n + 1}.indicator (fun g => q ^ partSize g) g)
      = (∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n}.indicator (fun g => q ^ partSize g) g)
        + ∑' g : PartConfig,
          {g : PartConfig | partCount g = n + 1}.indicator (fun g => q ^ partSize g) g := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun g => ?_
    by_cases h1 : partCount g ≤ n
    · rw [Set.indicator_of_mem (show g ∈ {g : PartConfig | partCount g ≤ n + 1} by
          simp only [Set.mem_setOf_eq]; omega),
        Set.indicator_of_mem (show g ∈ {g : PartConfig | partCount g ≤ n} from h1),
        Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g = n + 1} by
          simp only [Set.mem_setOf_eq]; omega),
        add_zero]
    · by_cases h2 : partCount g = n + 1
      · rw [Set.indicator_of_mem (show g ∈ {g : PartConfig | partCount g ≤ n + 1} by
            simp only [Set.mem_setOf_eq]; omega),
          Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n} from h1),
          Set.indicator_of_mem (show g ∈ {g : PartConfig | partCount g = n + 1} from h2),
          zero_add]
      · rw [Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n + 1} by
            simp only [Set.mem_setOf_eq]; omega),
          Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n} from h1),
          Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g = n + 1} from h2),
          add_zero]
  calc atMostGF q (n + 1)
      = ∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n + 1}.indicator (fun g => q ^ partSize g) g := hA
    _ = (∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n}.indicator (fun g => q ^ partSize g) g)
        + ∑' g : PartConfig,
          {g : PartConfig | partCount g = n + 1}.indicator (fun g => q ^ partSize g) g := hsplit
    _ = atMostGF q n + exactGF q (n + 1) := by rw [← hB, ← hC]; rfl

/-- **The Euler recursion.**  `T_{n+1} = T_n + q^{n+1} T_{n+1}`. -/
theorem atMostGF_succ_self (q : ℝ≥0∞) (n : ℕ) :
    atMostGF q (n + 1) = atMostGF q n + q ^ (n + 1) * atMostGF q (n + 1) := by
  rw [← exactGF_eq_mul]
  exact atMostGF_succ q n

/-! ## Size-truncated generating functions -/

/-- The generating function of the partitions with at most `n` parts and size at most `N`. -/
def atMostGFTrunc (q : ℝ≥0∞) (n N : ℕ) : ℝ≥0∞ :=
  ∑' h : {h : PartConfig // partCount h ≤ n ∧ partSize h ≤ N}, q ^ partSize h.1

theorem partSize_eq_zero_iff (h : PartConfig) : partSize h = 0 ↔ h = 0 := by
  constructor
  · intro h0
    refine Finsupp.ext fun j => ?_
    by_cases hj : j ∈ h.support
    · have hz := (Finset.sum_eq_zero_iff.mp h0) j hj
      have : h j = 0 := by
        rcases Nat.eq_zero_or_pos (h j) with hh | hh
        · exact hh
        · exact absurd hz (by positivity)
      simpa using this
    · simpa using Finsupp.notMem_support_iff.mp hj
  · rintro rfl
    exact partSize_zero

theorem atMostGFTrunc_size_zero (q : ℝ≥0∞) (n : ℕ) : atMostGFTrunc q n 0 = 1 := by
  rw [atMostGFTrunc]
  have hsingle : ∀ b : {h : PartConfig // partCount h ≤ n ∧ partSize h ≤ 0},
      b ≠ ⟨0, by simp⟩ → q ^ partSize b.1 = 0 := by
    intro b hb
    exact absurd (Subtype.ext ((partSize_eq_zero_iff b.1).mp (Nat.le_zero.mp b.2.2))) hb
  rw [tsum_eq_single ⟨0, by simp⟩ hsingle]
  simp

theorem atMostGFTrunc_count_zero (q : ℝ≥0∞) (N : ℕ) : atMostGFTrunc q 0 N = 1 := by
  rw [atMostGFTrunc]
  have hsingle : ∀ b : {h : PartConfig // partCount h ≤ 0 ∧ partSize h ≤ N},
      b ≠ ⟨0, by simp⟩ → q ^ partSize b.1 = 0 := by
    intro b hb
    exact absurd (Subtype.ext ((partCount_eq_zero_iff b.1).mp (Nat.le_zero.mp b.2.1))) hb
  rw [tsum_eq_single ⟨0, by simp⟩ hsingle]
  simp

/-- A configuration is recovered from its shift and its number of parts. -/
theorem eq_unshift_of_partCount {n : ℕ} {g : PartConfig} (hg : partCount g = n) :
    g = unshift (n - partCount (shift g)) (shift g) := by
  have hc := partCount_eq g
  rw [hg] at hc
  have h0 : n - partCount (shift g) = g 0 := by omega
  rw [h0, unshift_shift]

theorem atMostGFTrunc_succ_le (q : ℝ≥0∞) (n N : ℕ) :
    atMostGFTrunc q (n + 1) N
      ≤ atMostGFTrunc q n N + q ^ (n + 1) * atMostGFTrunc q (n + 1) (N - (n + 1)) := by
  classical
  -- split off the configurations with exactly `n+1` parts
  have hA := tsum_subtype {g : PartConfig | partCount g ≤ n + 1 ∧ partSize g ≤ N}
    (fun g => q ^ partSize g)
  have hB := tsum_subtype {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}
    (fun g => q ^ partSize g)
  have hC := tsum_subtype {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}
    (fun g => q ^ partSize g)
  have hsplit : (∑' g : PartConfig,
        {g : PartConfig | partCount g ≤ n + 1 ∧ partSize g ≤ N}.indicator
          (fun g => q ^ partSize g) g)
      = (∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}.indicator
            (fun g => q ^ partSize g) g)
        + ∑' g : PartConfig,
          {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}.indicator
            (fun g => q ^ partSize g) g := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun g => ?_
    by_cases hN : partSize g ≤ N
    · by_cases h1 : partCount g ≤ n
      · rw [Set.indicator_of_mem (show g ∈ _ from ⟨by omega, hN⟩),
          Set.indicator_of_mem (show g ∈ _ from ⟨h1, hN⟩),
          Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}
            by rintro ⟨h2, -⟩; omega), add_zero]
      · by_cases h2 : partCount g = n + 1
        · rw [Set.indicator_of_mem (show g ∈ _ from ⟨by omega, hN⟩),
            Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}
              by rintro ⟨h3, -⟩; omega),
            Set.indicator_of_mem (show g ∈ _ from ⟨h2, hN⟩), zero_add]
        · rw [Set.indicator_of_notMem
              (show g ∉ {g : PartConfig | partCount g ≤ n + 1 ∧ partSize g ≤ N}
                by rintro ⟨h3, -⟩; omega),
            Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}
              by rintro ⟨h3, -⟩; omega),
            Set.indicator_of_notMem
              (show g ∉ {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}
                by rintro ⟨h3, -⟩; omega), add_zero]
    · rw [Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n + 1 ∧ partSize g ≤ N}
          by rintro ⟨-, h3⟩; omega),
        Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}
          by rintro ⟨-, h3⟩; omega),
        Set.indicator_of_notMem (show g ∉ {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}
          by rintro ⟨-, h3⟩; omega), add_zero]
  -- bound the exact part by the shifted truncated sum
  have hinj : (∑' g : {g : PartConfig // partCount g = n + 1 ∧ partSize g ≤ N},
        q ^ partSize g.1)
      ≤ q ^ (n + 1) * atMostGFTrunc q (n + 1) (N - (n + 1)) := by
    rw [atMostGFTrunc, ← ENNReal.tsum_mul_left]
    refine Summable.tsum_le_tsum_of_inj
      (e := fun g : {g : PartConfig // partCount g = n + 1 ∧ partSize g ≤ N} =>
        (⟨shift g.1, ?_, ?_⟩ : {h : PartConfig // partCount h ≤ n + 1 ∧ partSize h ≤ N - (n + 1)}))
      ?_ (fun c _ => zero_le _) ?_ ENNReal.summable ENNReal.summable
    · have := partCount_shift_le g.1
      have := g.2.1
      omega
    · have hsz := partSize_eq_add_partSize_shift g.2.1
      have := g.2.2
      omega
    · intro a b hab
      have hs : shift a.1 = shift b.1 := congrArg Subtype.val hab
      refine Subtype.ext ?_
      rw [eq_unshift_of_partCount a.2.1, eq_unshift_of_partCount b.2.1, hs]
    · intro g
      rw [← pow_add]
      exact le_of_eq (by rw [partSize_eq_add_partSize_shift g.2.1])
  calc atMostGFTrunc q (n + 1) N
      = ∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n + 1 ∧ partSize g ≤ N}.indicator
            (fun g => q ^ partSize g) g := hA
    _ = (∑' g : PartConfig,
          {g : PartConfig | partCount g ≤ n ∧ partSize g ≤ N}.indicator
            (fun g => q ^ partSize g) g)
        + ∑' g : PartConfig,
          {g : PartConfig | partCount g = n + 1 ∧ partSize g ≤ N}.indicator
            (fun g => q ^ partSize g) g := hsplit
    _ = atMostGFTrunc q n N
        + ∑' g : {g : PartConfig // partCount g = n + 1 ∧ partSize g ≤ N}, q ^ partSize g.1 := by
          rw [← hB, ← hC]; rfl
    _ ≤ atMostGFTrunc q n N + q ^ (n + 1) * atMostGFTrunc q (n + 1) (N - (n + 1)) :=
        add_le_add_left hinj _

end

end GaloisForLFunctions.HTGeometry
