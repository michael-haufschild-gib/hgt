import GaloisForLFunctions.RHTower.BeurlingRandomPrimeDeletion
import GaloisForLFunctions.HTGeometry.GroupedSelectionCount

/-!
# A thinning of the primes with square-root discrepancy and a controlled count

Fix `1/2 < α < 1` and weights `w(p) = p^{α−1}`.  In the dyadic block `[2^k, 2^{k+1})` let
`C_k(p) = Σ_{q ≤ p} w(q)` be the cumulative mass and cut the block into the windows
`i L_k < C_k(p) ≤ (i + 1) L_k`, `L_k = 1 − w*_k`, `w*_k = 2^{k(α−1)}` (`grp`).  A window has mass
at most `1`, and every window ending below the block mass has mass at least `1 − 2w*_k`
(`grpMass_le_one`, `one_sub_two_mul_le_grpMass`): the windows are almost full.

Select at most one prime per window independently.  Hoeffding over a net gives the twisted bound
(R) at every frequency as in `BeurlingRandomPrimeDeletion`.  Because the windows are almost full,
the number of selected primes has variance `≪ Σ_i min(W_i, 1 − W_i) ≪ 2^{k(2α−1)}`, and Chernoff's
bound for the hit indicators (`HTGeometry.GroupedSelection.exists_selection_count`) controls every
prefix count:

`|Σ_{p ≤ x} (1_S(p) − p^{α−1})| ≪ x^{α−1/2} (log x + 1)²`   (`exists_deletedPrimes_counted`).
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry.GroupedSelection
open scoped ENNReal

noncomputable section

namespace RHTower.BeurlingDeletion

namespace Counted

variable {α : ℝ}

/-! ## Cumulative-mass windows -/

/-- The cumulative mass `C_k(p) = Σ_{q ∈ block k, q ≤ p} w(q)`. -/
def cumMass (α : ℝ) (k p : ℕ) : ℝ := ∑ q ∈ (blockPrimes k).filter (· ≤ p), delWeight α q

/-- The block mass `W_k`. -/
def blockMass (α : ℝ) (k : ℕ) : ℝ := ∑ q ∈ blockPrimes k, delWeight α q

/-- The maximal weight `w*_k = 2^{k(α−1)}` of block `k`. -/
def maxWeight (α : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ ((k : ℝ) * (α - 1))

/-- The window length `L_k = 1 − w*_k`. -/
def winLen (α : ℝ) (k : ℕ) : ℝ := 1 - maxWeight α k

/-- The number of windows `⌈W_k/L_k⌉ + 1`. -/
def grpCount (α : ℝ) (k : ℕ) : ℕ := ⌈blockMass α k / winLen α k⌉₊ + 1

/-- The window index `⌈C_k(p)/L_k⌉ − 1`. -/
def grpIdx (α : ℝ) (k p : ℕ) : ℕ := ⌈cumMass α k p / winLen α k⌉₊ - 1

/-- The window `G_{k,i}`. -/
def grp (α : ℝ) (k : ℕ) (i : Fin (grpCount α k)) : Finset ℕ :=
  (blockPrimes k).filter fun p => grpIdx α k p = i

theorem grpCount_pos (α : ℝ) (k : ℕ) : 0 < grpCount α k := Nat.succ_pos _

theorem delWeight_pos {p : ℕ} (hp : 0 < p) : 0 < delWeight α p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

theorem maxWeight_pos (α : ℝ) (k : ℕ) : 0 < maxWeight α k := by unfold maxWeight; positivity

theorem one_le_of_mem_blockPrimes {k p : ℕ} (hp : p ∈ blockPrimes k) : 1 ≤ k := by
  rw [mem_blockPrimes] at hp
  by_contra h
  push Not at h
  have hk : k = 0 := by omega
  subst hk
  have := hp.1.two_le
  simp at hp
  omega

theorem maxWeight_le (hα : α < 1) {k : ℕ} (hk : 1 ≤ k) :
    maxWeight α k ≤ (2 : ℝ) ^ (α - 1) := by
  unfold maxWeight
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem winLen_ge (hα : α < 1) {k : ℕ} (hk : 1 ≤ k) : 1 - (2 : ℝ) ^ (α - 1) ≤ winLen α k := by
  unfold winLen; linarith [maxWeight_le hα hk]

theorem two_rpow_lt_one (hα : α < 1) : (2 : ℝ) ^ (α - 1) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem winLen_pos (hα : α < 1) {k : ℕ} (hk : 1 ≤ k) : 0 < winLen α k := by
  linarith [winLen_ge hα hk, two_rpow_lt_one hα]

theorem delWeight_le_maxWeight (hα : α < 1) {k p : ℕ} (hp : p ∈ blockPrimes k) :
    delWeight α p ≤ maxWeight α k :=
  delWeight_le hα (mem_blockPrimes.mp hp).2.1

theorem cumMass_mono (k : ℕ) {p q : ℕ} (hpq : p ≤ q) : cumMass α k p ≤ cumMass α k q := by
  unfold cumMass
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) fun r _ _ => delWeight_nonneg α r
  simp only [Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, hr.2.trans hpq⟩

theorem cumMass_le_blockMass (k p : ℕ) : cumMass α k p ≤ blockMass α k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun r _ _ => delWeight_nonneg α r

theorem delWeight_le_cumMass {k p : ℕ} (hp : p ∈ blockPrimes k) :
    delWeight α p ≤ cumMass α k p := by
  unfold cumMass
  exact Finset.single_le_sum (f := delWeight α) (fun r _ => delWeight_nonneg α r)
    (Finset.mem_filter.mpr ⟨hp, le_rfl⟩)

theorem cumMass_pos {k p : ℕ} (hp : p ∈ blockPrimes k) : 0 < cumMass α k p :=
  lt_of_lt_of_le (delWeight_pos (mem_blockPrimes.mp hp).1.pos) (delWeight_le_cumMass hp)

/-- `C_k(q) = C_k(p) + w(q)` for consecutive... more simply: `C_k(p) + w(q) ≤ C_k(q)` for
`p < q` in the block. -/
theorem cumMass_add_le {k p q : ℕ} (hq : q ∈ blockPrimes k) (hpq : p < q) :
    cumMass α k p + delWeight α q ≤ cumMass α k q := by
  unfold cumMass
  have hsub : insert q ((blockPrimes k).filter (· ≤ p)) ⊆ (blockPrimes k).filter (· ≤ q) := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact Finset.mem_filter.mpr ⟨hq, le_rfl⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨h1, by omega⟩
  have hnot : q ∉ (blockPrimes k).filter (· ≤ p) := by
    intro h; have := (Finset.mem_filter.mp h).2; omega
  calc ∑ r ∈ (blockPrimes k).filter (· ≤ p), delWeight α r + delWeight α q
      = ∑ r ∈ insert q ((blockPrimes k).filter (· ≤ p)), delWeight α r := by
        rw [Finset.sum_insert hnot]; ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => delWeight_nonneg α r

/-- The mass of the primes whose cumulative mass is at most `y`. -/
def lowMass (α : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (blockPrimes k).filter (fun p => cumMass α k p ≤ y), delWeight α p

/-- `F(y) ≤ y`. -/
theorem lowMass_le (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : lowMass α k y ≤ y := by
  classical
  set P := (blockPrimes k).filter (fun p => cumMass α k p ≤ y) with hP
  by_cases hne : P.Nonempty
  · set p₀ := P.max' hne with hp₀
    have hp₀P : p₀ ∈ P := P.max'_mem hne
    have hsub : P ⊆ (blockPrimes k).filter (· ≤ p₀) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, P.le_max' r hr⟩
    calc lowMass α k y = ∑ p ∈ P, delWeight α p := rfl
      _ ≤ cumMass α k p₀ := Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun r _ _ => delWeight_nonneg α r
      _ ≤ y := (Finset.mem_filter.mp hp₀P).2
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold lowMass
    rw [← hP, hne, Finset.sum_empty]
    exact hy

/-- `F(y) > y − w*` below the block mass. -/
theorem sub_lt_lowMass (hα : α < 1) (k : ℕ) {y : ℝ} (hy : y < blockMass α k) :
    y - maxWeight α k < lowMass α k y := by
  classical
  set Q := (blockPrimes k).filter (fun p => y < cumMass α k p) with hQ
  by_cases hQne : ¬ Q.Nonempty
  · rw [Finset.not_nonempty_iff_eq_empty] at hQne
    have hall : (blockPrimes k).filter (fun p => cumMass α k p ≤ y) = blockPrimes k := by
      refine Finset.filter_true_of_mem fun p hp => ?_
      by_contra h
      push Not at h
      have : p ∈ Q := Finset.mem_filter.mpr ⟨hp, h⟩
      rw [hQne] at this; simp at this
    have hW : lowMass α k y = blockMass α k := by unfold lowMass blockMass; rw [hall]
    rw [hW]
    linarith [maxWeight_pos α k]
  push Not at hQne
  set q₀ := Q.min' hQne with hq₀
  have hq₀Q : q₀ ∈ Q := Q.min'_mem hQne
  obtain ⟨hq₀b, hq₀y⟩ := Finset.mem_filter.mp hq₀Q
  -- the primes with `C ≤ y` are exactly those below `q₀`
  have hlow : (blockPrimes k).filter (fun p => cumMass α k p ≤ y) =
      (blockPrimes k).filter (· < q₀) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hry⟩
      refine ⟨hr, ?_⟩
      by_contra h
      push Not at h
      have := cumMass_mono (α := α) k h
      linarith
    · rintro ⟨hr, hrq⟩
      refine ⟨hr, ?_⟩
      by_contra h
      push Not at h
      have : q₀ ≤ r := Q.min'_le r (Finset.mem_filter.mpr ⟨hr, h⟩)
      omega
  have hsplit : cumMass α k q₀ = lowMass α k y + delWeight α q₀ := by
    have e1 : lowMass α k y = ∑ p ∈ (blockPrimes k).filter (· < q₀), delWeight α p := by
      unfold lowMass; rw [hlow]
    rw [e1]
    unfold cumMass
    have : (blockPrimes k).filter (· ≤ q₀) = insert q₀ ((blockPrimes k).filter (· < q₀)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hr, hrq⟩
        rcases eq_or_lt_of_le hrq with h | h
        · left; exact h
        · right; exact ⟨hr, h⟩
      · rintro (rfl | ⟨hr, h⟩)
        · exact ⟨hq₀b, le_rfl⟩
        · exact ⟨hr, h.le⟩
    rw [this, Finset.sum_insert (by simp)]
    ring
  have hw := delWeight_le_maxWeight hα hq₀b
  linarith

/-- `p` lies in window `i` iff `i L < C(p) ≤ (i + 1) L`. -/
theorem mem_grp_iff (hα : α < 1) {k : ℕ} (i : Fin (grpCount α k)) {p : ℕ} :
    p ∈ grp α k i ↔ p ∈ blockPrimes k ∧ (i : ℝ) * winLen α k < cumMass α k p ∧
      cumMass α k p ≤ ((i : ℝ) + 1) * winLen α k := by
  unfold grp grpIdx
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hidx⟩
    have hL := winLen_pos hα (one_le_of_mem_blockPrimes hp)
    have hC := cumMass_pos (α := α) hp
    have hc1 : 1 ≤ ⌈cumMass α k p / winLen α k⌉₊ := Nat.one_le_iff_ne_zero.mpr
      (Nat.ceil_pos.mpr (div_pos hC hL)).ne'
    have hceil : ⌈cumMass α k p / winLen α k⌉₊ = (i : ℕ) + 1 := by omega
    rw [Nat.ceil_eq_iff (by omega)] at hceil
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hceil
    refine ⟨hp, ?_, ?_⟩
    · have := hceil.1; rwa [lt_div_iff₀ hL] at this
    · have := hceil.2; rwa [div_le_iff₀ hL] at this
  · rintro ⟨hp, h1, h2⟩
    have hL := winLen_pos hα (one_le_of_mem_blockPrimes hp)
    refine ⟨hp, ?_⟩
    have hceil : ⌈cumMass α k p / winLen α k⌉₊ = (i : ℕ) + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      exact ⟨(lt_div_iff₀ hL).mpr h1, (div_le_iff₀ hL).mpr h2⟩
    omega

theorem grpIdx_lt (hα : α < 1) {k p : ℕ} (hp : p ∈ blockPrimes k) : grpIdx α k p < grpCount α k := by
  have hL := winLen_pos hα (one_le_of_mem_blockPrimes hp)
  unfold grpIdx grpCount
  have : ⌈cumMass α k p / winLen α k⌉₊ ≤ ⌈blockMass α k / winLen α k⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right (cumMass_le_blockMass k p) hL.le)
  omega

theorem zero_not_mem_grp (α : ℝ) (k : ℕ) (i : Fin (grpCount α k)) : 0 ∉ grp α k i := by
  simp [grp, mem_blockPrimes, Nat.not_prime_zero]

theorem grp_subset (α : ℝ) (k : ℕ) (i : Fin (grpCount α k)) : grp α k i ⊆ blockPrimes k :=
  Finset.filter_subset _ _

/-- The window mass is a difference of low masses. -/
theorem grpMass_eq (hα : α < 1) {k : ℕ} (i : Fin (grpCount α k)) :
    ∑ p ∈ grp α k i, delWeight α p =
      lowMass α k (((i : ℝ) + 1) * winLen α k) - lowMass α k ((i : ℝ) * winLen α k) := by
  classical
  have hle : ∀ p ∈ blockPrimes k, cumMass α k p ≤ (i : ℝ) * winLen α k →
      cumMass α k p ≤ ((i : ℝ) + 1) * winLen α k := by
    intro p hp h
    have := winLen_pos hα (one_le_of_mem_blockPrimes hp)
    nlinarith
  rw [eq_sub_iff_add_eq]
  unfold lowMass
  rw [← Finset.sum_union]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, mem_grp_iff hα i]
    constructor
    · rintro (⟨hp, h1, h2⟩ | ⟨hp, h⟩)
      · exact ⟨hp, h2⟩
      · exact ⟨hp, hle p hp h⟩
    · rintro ⟨hp, h⟩
      by_cases h' : cumMass α k p ≤ (i : ℝ) * winLen α k
      · exact Or.inr ⟨hp, h'⟩
      · exact Or.inl ⟨hp, not_le.mp h', h⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    rw [mem_grp_iff hα i] at hp
    have := (Finset.mem_filter.mp hp').2
    linarith [hp.2.1]

/-- **A window has mass at most `1`.** -/
theorem grpMass_le_one (hα : α < 1) {k : ℕ} (i : Fin (grpCount α k)) :
    ∑ p ∈ grp α k i, delWeight α p ≤ 1 := by
  by_cases hne : (grp α k i).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hk := one_le_of_mem_blockPrimes (grp_subset α k i hp)
    have hL := winLen_pos hα hk
    rw [grpMass_eq hα i]
    have hiW : (i : ℝ) * winLen α k < blockMass α k := by
      rw [mem_grp_iff hα i] at hp
      linarith [hp.2.1, cumMass_le_blockMass (α := α) k p]
    have h1 := lowMass_le (α := α) k (y := ((i : ℝ) + 1) * winLen α k) (by positivity)
    have h2 := sub_lt_lowMass hα k hiW
    have : winLen α k + maxWeight α k = 1 := by unfold winLen; ring
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty]; norm_num

/-- **Windows ending below the block mass are almost full.** -/
theorem one_sub_two_mul_le_grpMass (hα : α < 1) {k : ℕ} (hk : 1 ≤ k) (i : Fin (grpCount α k))
    (hi : ((i : ℝ) + 1) * winLen α k < blockMass α k) :
    1 - 2 * maxWeight α k ≤ ∑ p ∈ grp α k i, delWeight α p := by
  have hL := winLen_pos hα hk
  rw [grpMass_eq hα i]
  have h1 := sub_lt_lowMass hα k hi
  have h2 := lowMass_le (α := α) k (y := (i : ℝ) * winLen α k) (by positivity)
  have : winLen α k + maxWeight α k = 1 := by unfold winLen; ring
  nlinarith

/-! ## Sizes -/

theorem blockPrimes_zero : blockPrimes 0 = ∅ := by
  ext p; simp only [mem_blockPrimes, Finset.notMem_empty, iff_false]
  rintro ⟨hp, -, h⟩
  have := hp.two_le
  simp at h; omega

theorem blockMass_le (hα : α < 1) (k : ℕ) : blockMass α k ≤ (2 : ℝ) ^ ((k : ℝ) * α) := by
  calc blockMass α k ≤ ∑ _p ∈ blockPrimes k, maxWeight α k :=
        Finset.sum_le_sum fun p hp => delWeight_le_maxWeight hα hp
    _ = (blockPrimes k).card * maxWeight α k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * maxWeight α k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_blockPrimes_le k) (maxWeight_pos α k).le
    _ = (2 : ℝ) ^ ((k : ℝ) * α) := by
        unfold maxWeight
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        congr 1; ring

/-- The constant `A_α = 1/(1 − 2^{α−1}) + 2`. -/
def sizeConst (α : ℝ) : ℝ := 1 / (1 - (2 : ℝ) ^ (α - 1)) + 2

theorem sizeConst_ge (hα : α < 1) : 2 ≤ sizeConst α := by
  have := two_rpow_lt_one hα
  unfold sizeConst
  have : 0 < 1 / (1 - (2 : ℝ) ^ (α - 1)) := by apply div_pos one_pos; linarith
  linarith

/-- `n_k ≤ A_α 2^{kα}`. -/
theorem grpCount_le (hα0 : 0 < α) (hα : α < 1) (k : ℕ) :
    (grpCount α k : ℝ) ≤ sizeConst α * (2 : ℝ) ^ ((k : ℝ) * α) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * α) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hα0.le)
  have hA := sizeConst_ge hα
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : blockMass α 0 = 0 := by unfold blockMass; rw [blockPrimes_zero]; simp
    unfold grpCount
    rw [this, zero_div, Nat.ceil_zero]
    simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, mul_one, zero_add, Nat.cast_one]
    linarith
  have hL := winLen_pos hα hk
  have hL1 := winLen_ge hα hk
  have hr := two_rpow_lt_one hα
  unfold grpCount
  push_cast
  have hc : (⌈blockMass α k / winLen α k⌉₊ : ℝ) < blockMass α k / winLen α k + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Finset.sum_nonneg fun p _ => delWeight_nonneg α p) hL.le)
  have hdiv : blockMass α k / winLen α k ≤ (2 : ℝ) ^ ((k : ℝ) * α) / (1 - (2 : ℝ) ^ (α - 1)) := by
    apply div_le_div₀ (by positivity) (blockMass_le hα k) (by linarith) hL1
  have : (2 : ℝ) ^ ((k : ℝ) * α) / (1 - (2 : ℝ) ^ (α - 1)) =
      1 / (1 - (2 : ℝ) ^ (α - 1)) * (2 : ℝ) ^ ((k : ℝ) * α) := by ring
  unfold sizeConst
  nlinarith

/-- **The variance budget.**  `Σ_i min(W_i, 1 − W_i) ≤ 2 w*_k n_k + 1`. -/
theorem sum_min_grpMass_le (hα : α < 1) (k : ℕ) (s : Finset (Fin (grpCount α k))) :
    ∑ i ∈ s, min (groupMass (grp α k) (delWeight α) i) (1 - groupMass (grp α k) (delWeight α) i)
      ≤ 2 * maxWeight α k * grpCount α k + 1 := by
  classical
  set L := winLen α k with hLdef
  set W := blockMass α k with hW
  set m : Fin (grpCount α k) → ℝ := fun i =>
    min (groupMass (grp α k) (delWeight α) i) (1 - groupMass (grp α k) (delWeight α) i) with hm
  have hm_nonneg : ∀ i, 0 ≤ m i := fun i => le_min
    (Finset.sum_nonneg fun p _ => delWeight_nonneg α p)
    (by have := grpMass_le_one hα i; unfold groupMass; linarith)
  set T := Finset.univ.filter (fun i : Fin (grpCount α k) => W ≤ ((i : ℝ) + 1) * L) with hT
  have hbound : ∀ i, m i ≤ 2 * maxWeight α k + (if i ∈ T then 1 / 2 else 0) := by
    intro i
    by_cases hi : i ∈ T
    · rw [if_pos hi]
      have : m i ≤ 1 / 2 := by
        simp only [hm]
        rcases le_total (groupMass (grp α k) (delWeight α) i) (1 / 2) with h | h
        · exact (min_le_left _ _).trans h
        · exact (min_le_right _ _).trans (by linarith)
      linarith [maxWeight_pos α k]
    · rw [if_neg hi, add_zero]
      by_cases hne : (grp α k i).Nonempty
      · obtain ⟨p, hp⟩ := hne
        have hk := one_le_of_mem_blockPrimes (grp_subset α k i hp)
        have hlt : ((i : ℝ) + 1) * L < W := by
          by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp h⟩)
        have := one_sub_two_mul_le_grpMass hα hk i hlt
        exact (min_le_right _ _).trans (by unfold groupMass; linarith)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have : groupMass (grp α k) (delWeight α) i = 0 := by unfold groupMass; rw [hne]; simp
        simp only [hm, this]
        rw [min_eq_left (by norm_num)]
        linarith [maxWeight_pos α k]
  have hTcard : T.card ≤ 2 := by
    by_cases hk : k = 0
    · subst hk
      have : W = 0 := by rw [hW]; unfold blockMass; rw [blockPrimes_zero]; simp
      have hc : grpCount α 0 = 1 := by
        unfold grpCount; rw [show blockMass α 0 = 0 from this, zero_div, Nat.ceil_zero]
      calc T.card ≤ (Finset.univ : Finset (Fin (grpCount α 0))).card := Finset.card_filter_le _ _
        _ = 1 := by rw [Finset.card_univ, Fintype.card_fin, hc]
        _ ≤ 2 := by norm_num
    have hL : 0 < L := winLen_pos hα (Nat.one_le_iff_ne_zero.mpr hk)
    set c := ⌈W / L⌉₊ with hc
    have hsub : T.image (fun i : Fin (grpCount α k) => (i : ℕ)) ⊆ {c - 1, c} := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      have hiT := (Finset.mem_filter.mp hi).2
      have hilt : (i : ℕ) < grpCount α k := i.2
      have h1 : c ≤ (i : ℕ) + 1 := by
        rw [hc, Nat.ceil_le]
        rw [div_le_iff₀ hL]; push_cast; linarith
      have h2 : (i : ℕ) < c + 1 := by
        have : c = ⌈blockMass α k / winLen α k⌉₊ := rfl
        unfold grpCount at hilt; omega
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc T.card = (T.image (fun i : Fin (grpCount α k) => (i : ℕ))).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ ({c - 1, c} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  calc ∑ i ∈ s, m i ≤ ∑ i, m i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hm_nonneg i
    _ ≤ ∑ i, (2 * maxWeight α k + (if i ∈ T then 1 / 2 else 0)) := Finset.sum_le_sum fun i _ => hbound i
    _ = 2 * maxWeight α k * grpCount α k + 1 / 2 * T.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ 2 * maxWeight α k * grpCount α k + 1 := by
        have : (T.card : ℝ) ≤ 2 := by exact_mod_cast hTcard
        linarith

/-! ## The selection in one block -/

/-- The twisted deviation of block `k` under the choice `ω`. -/
def cDev (α : ℝ) (k : ℕ) (ω : Fin (grpCount α k) → ℕ) (x t : ℝ) : ℂ :=
  ∑ i, groupDev (grp α k) (delWeight α) (testFn x t) i (ω i)

/-- The net spacing `1/(n_k(k+1))`. -/
def cStep (α : ℝ) (k : ℕ) : ℝ := 1 / ((grpCount α k : ℝ) * ((k : ℝ) + 1))

theorem cStep_pos (α : ℝ) (k : ℕ) : 0 < cStep α k := by
  have := grpCount_pos α k
  unfold cStep
  positivity

/-- The net point `±m·step`. -/
def cPoint (α : ℝ) (k : ℕ) (b : Bool) (m : ℕ) : ℝ :=
  (if b then (1 : ℝ) else -1) * (m : ℝ) * cStep α k

/-- The Hoeffding threshold at net index `m`. -/
def cThr (α : ℝ) (k m : ℕ) : ℝ :=
  4 * Real.sqrt (grpCount α k) * Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))

theorem cThr_nonneg (α : ℝ) (k m : ℕ) : 0 ≤ cThr α k m := by unfold cThr; positivity

theorem exp_neg_cThr (α : ℝ) (k m : ℕ) :
    4 * Real.exp (-cThr α k m ^ 2 / (16 * (grpCount α k : ℝ))) =
      4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < grpCount α k := by exact_mod_cast grpCount_pos α k
  have harg := one_le_arg k m
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) := Real.log_nonneg harg
  unfold cThr
  rw [mul_pow, mul_pow, Real.sq_sqrt hn.le, Real.sq_sqrt hlog]
  rw [show -((4 : ℝ) ^ 2 * (grpCount α k : ℝ) *
      Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) / (16 * (grpCount α k : ℝ)) =
      -Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) by field_simp; ring,
    Real.exp_neg, Real.exp_log (by linarith)]
  ring

theorem tsum_cFailure_le (α : ℝ) (k : ℕ) :
    ∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ,
      ENNReal.ofReal (4 * Real.exp (-cThr α k e.2.2 ^ 2 / (16 * (grpCount α k : ℝ)))) ≤
        ENNReal.ofReal (Real.pi ^ 2 / 24) := by
  simp only [exp_neg_cThr]
  have hsum : HasSum (fun m : ℕ => 4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
      (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) := by
    have := hasSum_inv_succ_sq.mul_left (4 / (2 : ℝ) ^ (k + 5))
    refine this.congr_fun fun m => ?_
    field_simp
  have hm : ∑' m : ℕ, ENNReal.ofReal (4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) =
      ENNReal.ofReal (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum.summable]
  set F : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
    with hF
  have hsplit : (∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ, F e.2.2) =
      ∑' _q : {q // q ∈ blockPrimes k}, ∑' _b : Bool, ∑' m : ℕ, F m := by
    refine (ENNReal.tsum_prod (f := fun _q (bm : Bool × ℕ) => F bm.2)).trans ?_
    exact tsum_congr fun _ => ENNReal.tsum_prod (f := fun _b m => F m)
  change (∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ, F e.2.2) ≤ _
  rw [hsplit]
  set c : ℝ≥0∞ := ENNReal.ofReal (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) with hc
  have hm' : (∑' m : ℕ, F m) = c := hm
  simp only [hm', tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    Fintype.card_coe, nsmul_eq_mul]
  have hcard : ((blockPrimes k).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k := by
    exact_mod_cast card_blockPrimes_le k
  have hval : ((2 : ℕ) : ℝ≥0∞) * c = ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
    rw [hc, show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num),
      show ((2 : ℝ≥0∞) ^ k)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ k)⁻¹) by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_add]
    field_simp
    ring
  rw [hval]
  calc ((blockPrimes k).card : ℝ≥0∞) * (ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹)
      ≤ (2 : ℝ≥0∞) ^ k * (ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹) :=
        mul_le_mul_left hcard _
    _ = ENNReal.ofReal (Real.pi ^ 2 / 24) := by
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), mul_one]

/-- The count parameters: `ℓ_k = log(8(n_k + 1))`, `V_k = 2w*_k n_k + 1`. -/
def cLog (α : ℝ) (k : ℕ) : ℝ := Real.log (8 * ((grpCount α k : ℝ) + 1))

def cVar (α : ℝ) (k : ℕ) : ℝ := 2 * maxWeight α k * grpCount α k + 1

def cT (α : ℝ) (k : ℕ) : ℝ := min 1 (Real.sqrt (cLog α k / cVar α k))

/-- The count threshold `λ_k = 2√(V_k ℓ_k) + 2ℓ_k`. -/
def cLam (α : ℝ) (k : ℕ) : ℝ := 2 * Real.sqrt (cVar α k * cLog α k) + 2 * cLog α k

theorem cVar_pos (α : ℝ) (k : ℕ) : 0 < cVar α k := by
  have := maxWeight_pos α k
  unfold cVar; positivity

theorem cLog_pos (α : ℝ) (k : ℕ) : 0 < cLog α k := by
  unfold cLog
  apply Real.log_pos
  have : (0 : ℝ) ≤ grpCount α k := Nat.cast_nonneg _
  linarith

/-- The Chernoff exponent is at most `−ℓ_k`. -/
theorem cExponent_le (α : ℝ) (k : ℕ) :
    cT α k ^ 2 * cVar α k - cT α k * cLam α k ≤ -cLog α k := by
  set V := cVar α k with hV
  set l := cLog α k with hl
  have hV0 : 0 < V := cVar_pos α k
  have hl0 : 0 < l := cLog_pos α k
  have hlam : cLam α k = 2 * Real.sqrt (V * l) + 2 * l := rfl
  rw [hlam]
  have hsVl : 0 ≤ Real.sqrt (V * l) := Real.sqrt_nonneg _
  unfold cT
  rcases le_total (Real.sqrt (l / V)) 1 with h | h
  · rw [min_eq_right h]
    have hsq : Real.sqrt (l / V) ^ 2 = l / V := Real.sq_sqrt (by positivity)
    have hprod : Real.sqrt (l / V) * Real.sqrt (V * l) = l := by
      rw [← Real.sqrt_mul (by positivity), show l / V * (V * l) = l ^ 2 by field_simp,
        Real.sqrt_sq hl0.le]
    have hs0 : 0 ≤ Real.sqrt (l / V) := Real.sqrt_nonneg _
    rw [hsq]
    have : l / V * V = l := by field_simp
    nlinarith
  · rw [min_eq_left h]
    have hVl : V ≤ l := by
      have := Real.one_le_sqrt.mp h
      rwa [one_le_div hV0] at this
    nlinarith

theorem two_mul_exp_cExponent_le (α : ℝ) (k : ℕ) :
    2 * Real.exp (cT α k ^ 2 * cVar α k - cT α k * cLam α k) ≤
      1 / (4 * ((grpCount α k : ℝ) + 1)) := by
  have h := Real.exp_le_exp.mpr (cExponent_le α k)
  have hn : (0 : ℝ) < (grpCount α k : ℝ) + 1 := by positivity
  rw [Real.exp_neg, cLog, Real.exp_log (by positivity)] at h
  calc 2 * Real.exp (cT α k ^ 2 * cVar α k - cT α k * cLam α k) ≤
        2 * (8 * ((grpCount α k : ℝ) + 1))⁻¹ := by linarith
    _ = 1 / (4 * ((grpCount α k : ℝ) + 1)) := by field_simp; ring

theorem cT_nonneg (α : ℝ) (k : ℕ) : 0 ≤ cT α k := le_min zero_le_one (Real.sqrt_nonneg _)

theorem cT_le_one (α : ℝ) (k : ℕ) : cT α k ≤ 1 := min_le_left _ _

/-- The prefix of the first `m` windows. -/
def prefixSet (k : ℕ) (m : Fin (grpCount α k + 1)) : Finset (Fin (grpCount α k)) :=
  Finset.univ.filter fun i => (i : ℕ) < m

theorem tsum_count_failure_le (α : ℝ) (k : ℕ) :
    ∑' _m : Fin (grpCount α k + 1),
      ENNReal.ofReal (2 * Real.exp (cT α k ^ 2 * cVar α k - cT α k * cLam α k)) ≤
        ENNReal.ofReal (1 / 4) := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (0 : ℝ) < (grpCount α k : ℝ) + 1 := by positivity
  calc ((grpCount α k + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (cT α k ^ 2 * cVar α k - cT α k * cLam α k))
      ≤ ((grpCount α k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (4 * ((grpCount α k : ℝ) + 1))) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (two_mul_exp_cExponent_le α k))
    _ = ENNReal.ofReal (1 / 4) := by
        rw [show ((grpCount α k + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((grpCount α k : ℝ) + 1) by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl, ← ENNReal.ofReal_mul hn.le]
        congr 1
        field_simp

/-- **One block admits a selection good for the net and for every prefix count.** -/
theorem exists_cBlockChoice (hα : α < 1) (k : ℕ) :
    ∃ ω : Fin (grpCount α k) → ℕ, (∀ i, ω i = 0 ∨ ω i ∈ grp α k i) ∧
      (∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
        ‖cDev α k ω q (cPoint α k b m)‖ < cThr α k m) ∧
      ∀ m : Fin (grpCount α k + 1),
        |∑ i ∈ prefixSet k m, countDev (grp α k) (delWeight α) i (ω i)| < cLam α k := by
  have hlt : (∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ,
      ENNReal.ofReal (4 * Real.exp (-cThr α k e.2.2 ^ 2 / (16 * (grpCount α k : ℝ))))) +
      ∑' _m : Fin (grpCount α k + 1),
        ENNReal.ofReal (2 * Real.exp (cT α k ^ 2 * cVar α k - cT α k * cLam α k)) < 1 := by
    calc _ ≤ ENNReal.ofReal (Real.pi ^ 2 / 24) + ENNReal.ofReal (1 / 4) :=
          add_le_add (tsum_cFailure_le α k) (tsum_count_failure_le α k)
      _ = ENNReal.ofReal (Real.pi ^ 2 / 24 + 1 / 4) :=
          (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
      _ < 1 := by
          rw [← ENNReal.ofReal_one]
          refine (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr ?_
          have h1 := Real.pi_lt_d2
          have h0 := Real.pi_pos
          have hsq : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
          norm_num at hsq ⊢
          linarith
  obtain ⟨ω, hω, hdev, hcnt⟩ := exists_selection_count (G := grp α k) (w := delWeight α)
    (fun p => delWeight_nonneg α p) (fun i => grpMass_le_one hα i)
    (fun i => zero_not_mem_grp α k i)
    (E := {q // q ∈ blockPrimes k} × Bool × ℕ) (F := Fin (grpCount α k + 1))
    (fun e => testFn e.1 (cPoint α k e.2.1 e.2.2)) (fun e p => norm_testFn_le _ _ p)
    (fun e => cThr α k e.2.2) (fun e => cThr_nonneg α k e.2.2) (prefixSet k)
    (fun _ => cLam α k) (fun _ => cT α k) (fun _ => cVar α k) (fun _ => cT_nonneg α k)
    (fun _ => cT_le_one α k) (fun f => sum_min_grpMass_le hα k _) hlt
  exact ⟨ω, hω, fun q b m => hdev (q, b, m), hcnt⟩

/-! ## The block bound on the whole line -/

theorem norm_cDev_sub_le (hα : α < 1) (k : ℕ) (ω : Fin (grpCount α k) → ℕ) (x t t' : ℝ) :
    ‖cDev α k ω x t - cDev α k ω x t'‖ ≤
      2 * (grpCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
  unfold cDev
  rw [← Finset.sum_sub_distrib]
  have hD : 0 ≤ ((k : ℝ) + 1) * |t - t'| := by positivity
  calc ‖∑ i, (groupDev (grp α k) (delWeight α) (testFn x t) i (ω i) -
        groupDev (grp α k) (delWeight α) (testFn x t') i (ω i))‖
      ≤ ∑ i : Fin (grpCount α k), 2 * (((k : ℝ) + 1) * |t - t'|) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [groupDev_sub]
        refine norm_groupDev_le_of_le _ (fun p hp => ?_) (fun p => delWeight_nonneg α p)
          (fun i => grpMass_le_one hα i) hD _
        have hpb : p ∈ blockPrimes k := grp_subset α k i hp
        have hpos : 0 < p := (mem_blockPrimes.mp hpb).1.pos
        unfold testFn
        split_ifs with h
        · refine (norm_cpow_sub_cpow_le hpos t t').trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (log_le_of_mem_blockPrimes hpb) (abs_nonneg _)
        · simpa using hD
    _ = 2 * (grpCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem cDev_eq_of_cutoff (k : ℕ) (ω : Fin (grpCount α k) → ℕ) {x y : ℝ}
    (h : ∀ p ∈ blockPrimes k, ((p : ℝ) ≤ x ↔ (p : ℝ) ≤ y)) (t : ℝ) :
    cDev α k ω x t = cDev α k ω y t := by
  unfold cDev
  refine Finset.sum_congr rfl fun i _ => groupDev_congr (fun p hp => ?_) _
  have hpb : p ∈ blockPrimes k := grp_subset α k i hp
  unfold testFn
  simp only [h p hpb]

theorem cDev_zero_of_cutoff (k : ℕ) (ω : Fin (grpCount α k) → ℕ) {x : ℝ}
    (h : ∀ p ∈ blockPrimes k, x < p) (t : ℝ) : cDev α k ω x t = 0 := by
  unfold cDev
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [groupDev_congr (φ' := fun _ => 0) (fun p hp => ?_)]
  · simp [groupDev]
  · have hpb : p ∈ blockPrimes k := grp_subset α k i hp
    unfold testFn
    rw [if_neg fun h' => absurd h'.2 (not_le.mpr (h p hpb))]

/-- The constant `14 + 3 log A_α`. -/
def logConst (α : ℝ) : ℝ := 14 + 3 * Real.log (sizeConst α)

/-- **The threshold grows like `2^{kα/2}√(k+1)√log(|t|+2)`.** -/
theorem cThr_le (hα0 : 0 < α) (hα : α < 1) (k m : ℕ) {t : ℝ} (hm : (m : ℝ) ≤ |t| / cStep α k) :
    cThr α k m ≤ 4 * Real.sqrt (sizeConst α * logConst α) * (2 : ℝ) ^ ((k : ℝ) * α / 2) *
      Real.sqrt ((k : ℝ) + 1) * Real.sqrt (Real.log (|t| + 2)) := by
  set A := sizeConst α with hA
  have hA2 : 2 ≤ A := sizeConst_ge hα
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  set n : ℝ := (grpCount α k : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast grpCount_pos α k
  have hnle : n ≤ A * (2 : ℝ) ^ ((k : ℝ) * α) := grpCount_le hα0 hα k
  have h2a : (2 : ℝ) ^ ((k : ℝ) * α) ≤ (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  have hk2 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    have : k + 1 ≤ 2 ^ k := this
    exact_mod_cast this
  have hL : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (|t| + 2) with hLdef
  have hL0 : 1 / 2 ≤ L := by linarith
  have hstep : |t| / cStep α k = |t| * (n * ((k : ℝ) + 1)) := by
    unfold cStep; rw [← hn]; field_simp
  rw [hstep] at hm
  have h4k : n * ((k : ℝ) + 1) ≤ A * (4 : ℝ) ^ k := by
    have : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
    rw [this]
    have h3 : n ≤ A * (2 : ℝ) ^ k := hnle.trans (by gcongr)
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
  have hm1 : (m : ℝ) + 1 ≤ A * (4 : ℝ) ^ k * (|t| + 2) := by
    have hpow : (1 : ℝ) ≤ A * (4 : ℝ) ^ k := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := k); nlinarith
    nlinarith [abs_nonneg t]
  have harg : (2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2 ≤ 32 * A ^ 2 * (32 : ℝ) ^ k * (|t| + 2) ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) + 1 := by positivity
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ (A * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 :=
      pow_le_pow_left₀ hm0 hm1 2
    have e : (2 : ℝ) ^ (k + 5) * (A * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 =
        32 * A ^ 2 * (32 : ℝ) ^ k * (|t| + 2) ^ 2 := by
      rw [pow_add, mul_pow, mul_pow, ← pow_mul,
        show (32 : ℝ) ^ k = (2 : ℝ) ^ k * ((4 : ℝ) ^ k) ^ 2 by
          rw [← pow_mul, show (32 : ℝ) = 2 * 4 ^ 2 by norm_num, mul_pow, ← pow_mul, mul_comm k 2]]
      ring
    calc _ ≤ (2 : ℝ) ^ (k + 5) * (A * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := e
  have hlogarg : Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) ≤
      logConst α * ((k : ℝ) + 1) * L := by
    have h1 := Real.log_le_log (by have := one_le_arg k m; linarith) harg
    have h2 : Real.log (32 * A ^ 2 * (32 : ℝ) ^ k * (|t| + 2) ^ 2) =
        Real.log 32 + 2 * Real.log A + (k : ℝ) * Real.log 32 + 2 * L := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
        hLdef]
      push_cast; ring
    have h32 : Real.log 32 < 4 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (32 : ℝ) < 2.7182818283 ^ 4 := by norm_num
        _ < Real.exp 1 ^ 4 := by gcongr
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hL0' : 0 ≤ L := by linarith
    unfold logConst
    rw [← hA]
    nlinarith [mul_nonneg hk0 hL0', mul_nonneg hlogA.le hL0', mul_nonneg (mul_nonneg hk0 hlogA.le) hL0']
  have hsqrt : Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) ≤
      Real.sqrt (logConst α) * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L := by
    rw [← Real.sqrt_mul (by unfold logConst; positivity), ← Real.sqrt_mul (by unfold logConst; positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsn : Real.sqrt n ≤ Real.sqrt A * (2 : ℝ) ^ ((k : ℝ) * α / 2) := by
    rw [← sqrt_two_rpow, ← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hnle
  unfold cThr
  rw [← hn]
  have hB : Real.sqrt (A * logConst α) = Real.sqrt A * Real.sqrt (logConst α) :=
    Real.sqrt_mul (by linarith) _
  rw [hB]
  calc 4 * Real.sqrt n * Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
      ≤ 4 * (Real.sqrt A * (2 : ℝ) ^ ((k : ℝ) * α / 2)) *
          (Real.sqrt (logConst α) * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L) := by gcongr
    _ = _ := by ring

/-- **The block bound.** -/
theorem norm_cDev_le (hα0 : 0 < α) (hα : α < 1) (k : ℕ) {ω : Fin (grpCount α k) → ℕ}
    (hω : ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
      ‖cDev α k ω q (cPoint α k b m)‖ < cThr α k m) (x t : ℝ) :
    ‖cDev α k ω x t‖ ≤ 4 * Real.sqrt (sizeConst α * logConst α) * (2 : ℝ) ^ ((k : ℝ) * α / 2) *
      Real.sqrt ((k : ℝ) + 1) * Real.sqrt (Real.log (|t| + 2)) + 2 := by
  classical
  have hRHS : 0 ≤ 4 * Real.sqrt (sizeConst α * logConst α) * (2 : ℝ) ^ ((k : ℝ) * α / 2) *
      Real.sqrt ((k : ℝ) + 1) * Real.sqrt (Real.log (|t| + 2)) := by positivity
  set P := (blockPrimes k).filter fun p : ℕ => ((p : ℝ) ≤ x) with hP
  by_cases hne : P.Nonempty
  swap
  · rw [cDev_zero_of_cutoff k ω (fun p hp => ?_) t]
    · simp only [norm_zero]; linarith
    · by_contra hle
      exact hne ⟨p, Finset.mem_filter.mpr ⟨hp, not_lt.mp hle⟩⟩
  set q := P.max' hne with hq
  have hqP : q ∈ P := P.max'_mem hne
  have hqb : q ∈ blockPrimes k := (Finset.mem_filter.mp hqP).1
  have hcut : ∀ p ∈ blockPrimes k, ((p : ℝ) ≤ x ↔ (p : ℝ) ≤ (q : ℝ)) := by
    intro p hp
    constructor
    · intro hpx
      exact_mod_cast P.le_max' p (Finset.mem_filter.mpr ⟨hp, hpx⟩)
    · intro hpq
      exact hpq.trans (Finset.mem_filter.mp hqP).2
  rw [cDev_eq_of_cutoff k ω hcut t]
  set η := cStep α k with hη
  have hη0 : 0 < η := cStep_pos α k
  set m : ℕ := ⌊|t| / η⌋₊ with hm
  have hm1 : (m : ℝ) ≤ |t| / η := Nat.floor_le (div_nonneg (abs_nonneg t) hη0.le)
  have hm2 : |t| / η < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  set b : Bool := decide (0 ≤ t) with hb
  have hclose : |t - cPoint α k b m| ≤ η := by
    have hmη : (m : ℝ) * η ≤ |t| := by rwa [le_div_iff₀ hη0] at hm1
    have hmη' : |t| < ((m : ℝ) + 1) * η := by rwa [div_lt_iff₀ hη0] at hm2
    unfold cPoint
    rw [← hη]
    by_cases ht : 0 ≤ t
    · have : b = true := by rw [hb]; exact decide_eq_true ht
      rw [this, if_pos rfl, abs_of_nonneg ht] at *
      rw [abs_le]; constructor <;> nlinarith
    · have : b = false := by rw [hb]; exact decide_eq_false ht
      rw [this, if_neg (by simp)]
      rw [abs_of_neg (not_le.mp ht)] at hmη hmη'
      rw [abs_le]; constructor <;> nlinarith
  have hlip := norm_cDev_sub_le hα k ω q t (cPoint α k b m)
  have hlip' : 2 * (grpCount α k : ℝ) * (((k : ℝ) + 1) * |t - cPoint α k b m|) ≤ 2 := by
    have hn0 : (0 : ℝ) < grpCount α k := by exact_mod_cast grpCount_pos α k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc _ ≤ 2 * (grpCount α k : ℝ) * (((k : ℝ) + 1) * η) := by gcongr
      _ = 2 := by rw [hη]; unfold cStep; field_simp
  have hnet := hω ⟨q, hqb⟩ b m
  have hthr := cThr_le hα0 hα k m hm1
  calc ‖cDev α k ω q t‖
      ≤ ‖cDev α k ω q (cPoint α k b m)‖ +
          ‖cDev α k ω q t - cDev α k ω q (cPoint α k b m)‖ := by
        have := norm_add_le (cDev α k ω q (cPoint α k b m))
          (cDev α k ω q t - cDev α k ω q (cPoint α k b m))
        rwa [add_sub_cancel] at this
    _ ≤ cThr α k m + 2 := by
        have := hnet.le
        linarith [hlip.trans hlip']
    _ ≤ _ := by linarith

/-! ## Gluing the blocks -/

/-- A good selection in block `k`. -/
def goodC (hα : α < 1) (k : ℕ) : Fin (grpCount α k) → ℕ :=
  Classical.choose (exists_cBlockChoice hα k)

theorem goodC_mem (hα : α < 1) (k : ℕ) (i : Fin (grpCount α k)) :
    goodC hα k i = 0 ∨ goodC hα k i ∈ grp α k i :=
  (Classical.choose_spec (exists_cBlockChoice hα k)).1 i

theorem goodC_net (hα : α < 1) (k : ℕ) (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ) :
    ‖cDev α k (goodC hα k) q (cPoint α k b m)‖ < cThr α k m :=
  (Classical.choose_spec (exists_cBlockChoice hα k)).2.1 q b m

theorem goodC_count (hα : α < 1) (k : ℕ) (m : Fin (grpCount α k + 1)) :
    |∑ i ∈ prefixSet k m, countDev (grp α k) (delWeight α) i (goodC hα k i)| < cLam α k :=
  (Classical.choose_spec (exists_cBlockChoice hα k)).2.2 m

/-- The deleted primes. -/
def deletedC (hα : α < 1) : Set ℕ := {p | ∃ k i, goodC hα k i = p ∧ p ≠ 0}

theorem prime_of_mem_deletedC (hα : α < 1) {p : ℕ} (hp : p ∈ deletedC hα) : p.Prime := by
  obtain ⟨k, i, hki, hp0⟩ := hp
  rcases goodC_mem hα k i with h | h
  · exact absurd (hki ▸ h) hp0
  · rw [hki] at h
    exact (mem_blockPrimes.mp (grp_subset α k i h)).1

theorem mem_deletedC_iff (hα : α < 1) {k p : ℕ} (hp : p ∈ blockPrimes k) :
    p ∈ deletedC hα ↔ goodC hα k ⟨grpIdx α k p, grpIdx_lt hα hp⟩ = p := by
  constructor
  · rintro ⟨k', i, hki, hp0⟩
    rcases goodC_mem hα k' i with h | h
    · exact absurd (hki ▸ h) hp0
    · rw [hki] at h
      obtain ⟨hpb', hidx⟩ := Finset.mem_filter.mp h
      have hk : k' = k := (log_eq_of_mem_blockPrimes hpb').symm.trans (log_eq_of_mem_blockPrimes hp)
      subst hk
      have hi : (⟨grpIdx α k' p, grpIdx_lt hα hp⟩ : Fin (grpCount α k')) = i := Fin.ext hidx
      rw [hi]; exact hki
  · intro h
    exact ⟨k, _, h, (mem_blockPrimes.mp hp).1.ne_zero⟩

/-- The block deviation of the good selection as a sum over the block primes. -/
theorem cDev_goodC (hα : α < 1) (k : ℕ) (x t : ℝ) :
    cDev α k (goodC hα k) x t = ∑ p ∈ blockPrimes k,
      ((deletedC hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * testFn x t p := by
  classical
  set g : ℕ → Fin (grpCount α k) := fun p =>
    if h : p ∈ blockPrimes k then ⟨grpIdx α k p, grpIdx_lt hα h⟩ else ⟨0, grpCount_pos α k⟩
  have hgroup : ∀ i, grp α k i = (blockPrimes k).filter fun p => g p = i := by
    intro i
    unfold grp
    refine Finset.filter_congr fun p hp => ?_
    simp only [g, dif_pos hp, Fin.ext_iff]
  unfold cDev groupDev
  simp_rw [hgroup]
  rw [← Finset.sum_fiberwise_of_maps_to (s := blockPrimes k) (t := Finset.univ) (g := g)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpb, hgi⟩ := Finset.mem_filter.mp hp
  have hgi' : (⟨grpIdx α k p, grpIdx_lt hα hpb⟩ : Fin (grpCount α k)) = i := by
    rw [← hgi]; simp only [g, dif_pos hpb]
  congr 1
  rw [Set.indicator_apply]
  by_cases hdel : p ∈ deletedC hα
  · rw [if_pos hdel, if_pos (by rw [← hgi']; exact (mem_deletedC_iff hα hpb).mp hdel)]
  · rw [if_neg hdel, if_neg fun h => hdel ((mem_deletedC_iff hα hpb).mpr (by rw [hgi']; exact h))]

/-- **The deviation up to `x` is the sum of the block deviations.** -/
theorem sum_primes_eq_sum_cDev (hα : α < 1) {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      ((deletedC hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) *
        (p : ℂ) ^ (-((t : ℂ) * I)) =
      ∑ k ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1), cDev α k (goodC hα k) x t := by
  classical
  set K := Nat.log 2 ⌊x⌋₊ with hK
  set f : ℕ → ℂ := fun p =>
    ((deletedC hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * testFn x t p
  set T := (Finset.Iio (2 ^ (K + 1))).filter Nat.Prime with hT
  have hx0 : 0 ≤ x := by linarith
  simp_rw [cDev_goodC hα]
  have hfib : ∑ k ∈ Finset.range (K + 1), ∑ p ∈ blockPrimes k, f p = ∑ p ∈ T, f p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range (K + 1)) (g := Nat.log 2)
      (fun p hp => by
        rw [Finset.mem_range]
        have hp' := Finset.mem_filter.mp hp
        exact Nat.lt_succ_of_le (Nat.le_of_lt_succ
          (Nat.log_lt_of_lt_pow hp'.2.ne_zero (Finset.mem_Iio.mp hp'.1))))]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iio, mem_blockPrimes, hT]
    have hk' : k < K + 1 := Finset.mem_range.mp hk
    constructor
    · rintro ⟨hp, h2k, hlt⟩
      refine ⟨⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk'), hp⟩, ?_⟩
      exact Nat.log_eq_of_pow_le_of_lt_pow h2k hlt
    · rintro ⟨⟨_, hp⟩, hlog⟩
      refine ⟨hp, ?_, ?_⟩
      · rw [← hlog]; exact Nat.pow_log_le_self 2 hp.ne_zero
      · rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) p
  rw [hfib]
  have hsub : (Finset.Iic ⌊x⌋₊).filter Nat.Prime ⊆ T := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr ?_, hp2⟩
    exact lt_of_le_of_lt (Finset.mem_Iic.mp hp1) (Nat.lt_pow_succ_log_self (by norm_num) _)
  rw [← Finset.sum_subset hsub fun p hpT hpnot => ?_]
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    simp only [f, testFn]
    rw [if_pos ⟨hp2.pos, (Nat.cast_le.mpr (Finset.mem_Iic.mp hp1)).trans (Nat.floor_le hx0)⟩]
  · have hpx : x < p := by
      have hnot : ¬ p ≤ ⌊x⌋₊ := fun h =>
        hpnot (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr h, (Finset.mem_filter.mp hpT).2⟩)
      exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast not_le.mp hnot)
    simp only [f, testFn]
    rw [if_neg fun h => absurd h.2 (not_le.mpr hpx), mul_zero]

/-- **Square-root discrepancy at every frequency.** -/
theorem exists_twisted_bound (hα0 : 0 < α) (hα : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      ‖∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        ((deletedC hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) *
          (p : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        C * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt (Real.log (|t| + 2)) := by
  set B : ℝ := 4 * Real.sqrt (sizeConst α * logConst α) with hB
  have hB0 : 0 ≤ B := by positivity
  set r : ℝ := (2 : ℝ) ^ (α / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  have hr0 : 0 < r - 1 := by linarith
  refine ⟨2 * B * (r / (r - 1)) + 6, by positivity, fun x hx t => ?_⟩
  set K := Nat.log 2 ⌊x⌋₊ with hK
  set L := Real.log (|t| + 2) with hL
  have hx0 : 0 < x := by linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2 := Real.log_two_gt_d9
  have hsL : 4 / 5 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hxα : 1 ≤ x ^ (α / 2) := Real.one_le_rpow hx (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2K : (2 : ℝ) ^ K ≤ x := by
    have h1 : 2 ^ K ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (Nat.floor_pos.mpr hx).ne'
    calc (2 : ℝ) ^ K ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ x := Nat.floor_le hx0.le
  have hK1 : (K : ℝ) + 1 ≤ 2 * (Real.log x + 1) := by
    have h := Real.log_le_log (by positivity) h2K
    rw [Real.log_pow] at h
    nlinarith
  have hrK : r ^ K ≤ x ^ (α / 2) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) (by rwa [Real.rpow_natCast]) (by linarith)
  have hgeom : ∑ k ∈ Finset.range (K + 1), r ^ k ≤ r / (r - 1) * x ^ (α / 2) := by
    rw [geom_sum_eq hr1.ne', div_le_iff₀ (by linarith)]
    have hrK' : r ^ (K + 1) = r * r ^ K := by rw [pow_succ]; ring
    have : r / (r - 1) * x ^ (α / 2) * (r - 1) = r * x ^ (α / 2) := by field_simp
    rw [this, hrK']
    nlinarith [pow_pos (show (0:ℝ) < r by linarith) K]
  have hblock : ∀ k ∈ Finset.range (K + 1), ‖cDev α k (goodC hα k) x t‖ ≤
      B * r ^ k * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L + 2 := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      have h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : (k : ℝ) ≤ K := by exact_mod_cast h
      linarith
    have hb := norm_cDev_le hα0 hα k (goodC_net hα k) x t
    have hrk : (2 : ℝ) ^ ((k : ℝ) * α / 2) = r ^ k := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrk, ← hB] at hb
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((K : ℝ) + 1) := Real.sqrt_le_sqrt hkK
    calc _ ≤ B * r ^ k * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L + 2 := hb
      _ ≤ _ := by gcongr
  rw [sum_primes_eq_sum_cDev hα hx t]
  have hsK : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
  calc ‖∑ k ∈ Finset.range (K + 1), cDev α k (goodC hα k) x t‖
      ≤ ∑ k ∈ Finset.range (K + 1), (B * r ^ k * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L + 2) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
    _ = B * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L * ∑ k ∈ Finset.range (K + 1), r ^ k +
          2 * ((K : ℝ) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
        push_cast
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · ring
    _ ≤ B * (2 * (Real.log x + 1)) * Real.sqrt L * (r / (r - 1) * x ^ (α / 2)) +
          2 * (2 * (Real.log x + 1)) := by
        gcongr
        exact hsK.trans hK1
    _ ≤ (2 * B * (r / (r - 1)) + 6) * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt L := by
        have hq : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
        have h4 : 4 * (Real.log x + 1) ≤ 6 * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt L := by
          have : (1 : ℝ) ≤ x ^ (α / 2) * Real.sqrt L * (5 / 4) := by nlinarith
          nlinarith
        nlinarith

/-! ## The count -/

theorem grpIdx_mono (hα : α < 1) {k p q : ℕ} (hp : p ∈ blockPrimes k) (hpq : p ≤ q) :
    grpIdx α k p ≤ grpIdx α k q := by
  have hL := winLen_pos hα (one_le_of_mem_blockPrimes hp)
  unfold grpIdx
  exact Nat.sub_le_sub_right (Nat.ceil_mono (div_le_div_of_nonneg_right
    (cumMass_mono k hpq) hL.le)) 1

/-- **The count deviation of one block** is a prefix count up to one window. -/
theorem norm_cDev_zero_le (hα : α < 1) (k : ℕ) (x : ℝ) :
    ‖cDev α k (goodC hα k) x 0‖ ≤ cLam α k + 2 := by
  classical
  have hlam0 : 0 ≤ cLam α k := by
    unfold cLam; have := cLog_pos α k; positivity
  set P := (blockPrimes k).filter fun p : ℕ => ((p : ℝ) ≤ x) with hP
  by_cases hne : P.Nonempty
  swap
  · rw [cDev_zero_of_cutoff k _ (fun p hp => ?_) 0]
    · simp only [norm_zero]; linarith
    · by_contra hle
      exact hne ⟨p, Finset.mem_filter.mpr ⟨hp, not_lt.mp hle⟩⟩
  set q := P.max' hne with hq
  have hqP : q ∈ P := P.max'_mem hne
  have hqb : q ∈ blockPrimes k := (Finset.mem_filter.mp hqP).1
  have hqx : (q : ℝ) ≤ x := (Finset.mem_filter.mp hqP).2
  set j : Fin (grpCount α k) := ⟨grpIdx α k q, grpIdx_lt hα hqb⟩ with hj
  set ω := goodC hα k with hω
  -- the three kinds of windows
  have hlow : ∀ i : Fin (grpCount α k), (i : ℕ) < j →
      groupDev (grp α k) (delWeight α) (testFn x 0) i (ω i) =
        (countDev (grp α k) (delWeight α) i (ω i) : ℂ) := by
    intro i hi
    have htest : ∀ p ∈ grp α k i, testFn x 0 p = 1 := by
      intro p hp
      have hpb := grp_subset α k i hp
      have hidx : grpIdx α k p = i := (Finset.mem_filter.mp hp).2
      have hpq : p < q := by
        by_contra h
        push Not at h
        have := grpIdx_mono hα hqb h
        rw [hidx] at this
        exact absurd hi (not_lt.mpr this)
      unfold testFn
      rw [if_pos ⟨(mem_blockPrimes.mp hpb).1.pos, by
        have : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
        linarith⟩]
      simp
    unfold groupDev countDev groupMass
    rw [Finset.sum_congr rfl fun p hp => by rw [htest p hp, mul_one]]
    rw [Finset.sum_sub_distrib]
    have hind : ∑ p ∈ grp α k i, (if ω i = p then (1 : ℂ) else 0) =
        if ω i = 0 then 0 else 1 := by
      rw [Finset.sum_ite_eq]
      rcases goodC_mem hα k i with h | h
      · rw [← hω] at h
        rw [h, if_neg (zero_not_mem_grp α k i), if_pos rfl]
      · rw [← hω] at h
        have h0 : ω i ≠ 0 := fun h' => zero_not_mem_grp α k i (h' ▸ h)
        rw [if_pos h, if_neg h0]
    rw [hind]
    push_cast
    split_ifs <;> simp
  have hhigh : ∀ i : Fin (grpCount α k), (j : ℕ) < i →
      groupDev (grp α k) (delWeight α) (testFn x 0) i (ω i) = 0 := by
    intro i hi
    unfold groupDev
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpb := grp_subset α k i hp
    have hidx : grpIdx α k p = i := (Finset.mem_filter.mp hp).2
    have hqp : q < p := by
      by_contra h
      push Not at h
      have := grpIdx_mono hα hpb h
      rw [hidx] at this
      exact absurd hi (not_lt.mpr this)
    have hpx : x < p := by
      by_contra h
      push Not at h
      have := P.le_max' p (Finset.mem_filter.mpr ⟨hpb, h⟩)
      omega
    have ht : testFn x 0 p = 0 := by
      unfold testFn
      rw [if_neg fun h => absurd h.2 (not_le.mpr hpx)]
    rw [ht, mul_zero]
  have hsplit : cDev α k ω x 0 =
      (∑ i ∈ prefixSet k ⟨j, by omega⟩, countDev (grp α k) (delWeight α) i (ω i) : ℝ) +
        groupDev (grp α k) (delWeight α) (testFn x 0) j (ω j) := by
    unfold cDev
    have hpt : ∀ i : Fin (grpCount α k), groupDev (grp α k) (delWeight α) (testFn x 0) i (ω i) =
        (if (i : ℕ) < j then (countDev (grp α k) (delWeight α) i (ω i) : ℂ) else 0) +
          (if i = j then groupDev (grp α k) (delWeight α) (testFn x 0) j (ω j) else 0) := by
      intro i
      rcases lt_trichotomy (i : ℕ) j with h | h | h
      · rw [if_pos h, if_neg (fun h' => by rw [h'] at h; exact lt_irrefl _ h), add_zero, hlow i h]
      · have hij : i = j := Fin.ext h
        rw [if_neg (by omega), if_pos hij, zero_add, hij]
      · rw [if_neg (by omega), if_neg (fun h' => by rw [h'] at h; exact lt_irrefl _ h), add_zero,
          hhigh i h]
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    rw [← Finset.sum_filter]
    push_cast
    rfl
  rw [hsplit]
  have hc := goodC_count hα k ⟨j, by omega⟩
  rw [← hω] at hc
  have hg := norm_groupDev_le (testFn x 0) (fun p => norm_testFn_le x 0 p)
    (fun p => delWeight_nonneg α p) (fun i => grpMass_le_one hα i) j (ω j)
  calc _ ≤ ‖((∑ i ∈ prefixSet k ⟨j, by omega⟩, countDev (grp α k) (delWeight α) i (ω i) : ℝ) : ℂ)‖ +
        ‖groupDev (grp α k) (delWeight α) (testFn x 0) j (ω j)‖ := norm_add_le _ _
    _ ≤ cLam α k + 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith

/-- `λ_k + 2 ≤ a √(k+1) r^k + b (k+1)` with `r = 2^{α−1/2}`. -/
theorem cLam_add_two_le (hα0 : 0 < α) (hα : α < 1) (k : ℕ) :
    cLam α k + 2 ≤
      2 * Real.sqrt (2 * sizeConst α * (Real.log (16 * sizeConst α) + 1)) *
          Real.sqrt ((k : ℝ) + 1) * ((2 : ℝ) ^ (α - 1 / 2)) ^ k +
        (2 * Real.sqrt (Real.log (16 * sizeConst α) + 1) + 2 * (Real.log (16 * sizeConst α) + 1) + 2) *
          ((k : ℝ) + 1) := by
  set A := sizeConst α with hA
  have hA2 : 2 ≤ A := sizeConst_ge hα
  set c₁ := Real.log (16 * A) + 1 with hc₁
  have hc₁0 : 1 ≤ c₁ := by
    have : 0 ≤ Real.log (16 * A) := Real.log_nonneg (by linarith)
    linarith
  set r := (2 : ℝ) ^ (α - 1 / 2) with hr
  have hr0 : 0 < r := by positivity
  set n : ℝ := (grpCount α k : ℝ) with hn
  have hnle : n ≤ A * (2 : ℝ) ^ ((k : ℝ) * α) := grpCount_le hα0 hα k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2a : (2 : ℝ) ^ ((k : ℝ) * α) ≤ (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  -- the variance budget
  have hrk : (r ^ k) ^ 2 = maxWeight α k * (2 : ℝ) ^ ((k : ℝ) * α) := by
    rw [hr, maxWeight, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1; push_cast; ring
  have hV : cVar α k ≤ 2 * A * (r ^ k) ^ 2 + 1 := by
    unfold cVar
    rw [hrk, ← hn]
    have := maxWeight_pos α k
    nlinarith
  -- the logarithm
  have hlog : cLog α k ≤ c₁ * ((k : ℝ) + 1) := by
    unfold cLog
    rw [← hn]
    have harg : 8 * (n + 1) ≤ 16 * A * (2 : ℝ) ^ k := by
      have h1 : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hpos : 0 < 8 * (n + 1) := by positivity
    calc Real.log (8 * (n + 1)) ≤ Real.log (16 * A * (2 : ℝ) ^ k) := Real.log_le_log hpos harg
      _ = Real.log (16 * A) + k * Real.log 2 := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      _ ≤ c₁ * ((k : ℝ) + 1) := by
          have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
          have h0 : 0 ≤ Real.log (16 * A) := Real.log_nonneg (by linarith)
          rw [hc₁]; nlinarith
  have hl0 : 0 < cLog α k := cLog_pos α k
  have hV0 : 0 < cVar α k := cVar_pos α k
  -- the square root
  have hsqrt : Real.sqrt (cVar α k * cLog α k) ≤
      Real.sqrt (2 * A * c₁) * Real.sqrt ((k : ℝ) + 1) * r ^ k +
        Real.sqrt c₁ * Real.sqrt ((k : ℝ) + 1) := by
    have h1 : cVar α k * cLog α k ≤ (2 * A * (r ^ k) ^ 2 + 1) * (c₁ * ((k : ℝ) + 1)) :=
      mul_le_mul hV hlog hl0.le (by positivity)
    have h2 : Real.sqrt ((2 * A * (r ^ k) ^ 2 + 1) * (c₁ * ((k : ℝ) + 1))) ≤
        Real.sqrt (2 * A * c₁) * Real.sqrt ((k : ℝ) + 1) * r ^ k +
          Real.sqrt c₁ * Real.sqrt ((k : ℝ) + 1) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hs1 := Real.sq_sqrt (show 0 ≤ 2 * A * c₁ by positivity)
      have hs2 := Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity)
      have hs3 := Real.sq_sqrt (show 0 ≤ c₁ by positivity)
      set u := Real.sqrt (2 * A * c₁) * Real.sqrt ((k : ℝ) + 1) * r ^ k with hu
      set v := Real.sqrt c₁ * Real.sqrt ((k : ℝ) + 1) with hv
      have hp : 0 ≤ u * v := by positivity
      have hu2 : u ^ 2 = 2 * A * c₁ * ((k : ℝ) + 1) * (r ^ k) ^ 2 := by
        rw [hu, mul_pow, mul_pow, hs1, hs2]
      have hv2 : v ^ 2 = c₁ * ((k : ℝ) + 1) := by rw [hv, mul_pow, hs3, hs2]
      have e : (u + v) ^ 2 = u ^ 2 + 2 * (u * v) + v ^ 2 := by ring
      have e2 : (2 * A * (r ^ k) ^ 2 + 1) * (c₁ * ((k : ℝ) + 1)) =
          2 * A * c₁ * ((k : ℝ) + 1) * (r ^ k) ^ 2 + c₁ * ((k : ℝ) + 1) := by ring
      rw [e, e2, hu2, hv2]
      linarith
    exact (Real.sqrt_le_sqrt h1).trans h2
  have hsq1 : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hs2Ac : Real.sqrt (2 * A * c₁) = Real.sqrt 2 * Real.sqrt (A * c₁) := by
    rw [← Real.sqrt_mul (by norm_num)]; ring_nf
  unfold cLam
  have hc1s : 0 ≤ Real.sqrt c₁ := Real.sqrt_nonneg _
  calc 2 * Real.sqrt (cVar α k * cLog α k) + 2 * cLog α k + 2
      ≤ 2 * (Real.sqrt (2 * A * c₁) * Real.sqrt ((k : ℝ) + 1) * r ^ k +
          Real.sqrt c₁ * Real.sqrt ((k : ℝ) + 1)) + 2 * (c₁ * ((k : ℝ) + 1)) + 2 := by
        gcongr
    _ ≤ 2 * Real.sqrt (2 * A * c₁) * Real.sqrt ((k : ℝ) + 1) * r ^ k +
          (2 * Real.sqrt c₁ + 2 * c₁ + 2) * ((k : ℝ) + 1) := by
        have : Real.sqrt c₁ * Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt c₁ * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hsq1 hc1s
        nlinarith

/-- **The count of the deleted primes.** -/
theorem exists_count_bound (hα1 : 1 / 2 < α) (hα : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        ((deletedC hα).indicator (fun _ => (1 : ℝ)) p - delWeight α p)| ≤
        C * x ^ (α - 1 / 2) * (Real.log x + 1) ^ 2 := by
  have hα0 : 0 < α := by linarith
  set A := sizeConst α
  set c₁ := Real.log (16 * A) + 1
  set a := 2 * Real.sqrt (2 * A * c₁) with ha
  set b := 2 * Real.sqrt c₁ + 2 * c₁ + 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by
    have : 0 ≤ Real.log (16 * A) := Real.log_nonneg (by linarith [sizeConst_ge hα])
    positivity
  set r : ℝ := (2 : ℝ) ^ (α - 1 / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  have hr0 : 0 < r - 1 := by linarith
  refine ⟨2 * a * (r / (r - 1)) + 4 * b, by positivity, fun x hx => ?_⟩
  set K := Nat.log 2 ⌊x⌋₊ with hK
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxα : 1 ≤ x ^ (α - 1 / 2) := Real.one_le_rpow hx (by linarith)
  have h2K : (2 : ℝ) ^ K ≤ x := by
    have h1 : 2 ^ K ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (Nat.floor_pos.mpr hx).ne'
    calc (2 : ℝ) ^ K ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ x := Nat.floor_le hx0.le
  have hK1 : (K : ℝ) + 1 ≤ 2 * (Real.log x + 1) := by
    have h := Real.log_le_log (by positivity) h2K
    rw [Real.log_pow] at h
    have := Real.log_two_gt_d9
    nlinarith
  have hrK : r ^ K ≤ x ^ (α - 1 / 2) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) (by rwa [Real.rpow_natCast]) (by linarith)
  have hgeom : ∑ k ∈ Finset.range (K + 1), r ^ k ≤ r / (r - 1) * x ^ (α - 1 / 2) := by
    rw [geom_sum_eq hr1.ne', div_le_iff₀ (by linarith)]
    have hrK' : r ^ (K + 1) = r * r ^ K := by rw [pow_succ]; ring
    have : r / (r - 1) * x ^ (α - 1 / 2) * (r - 1) = r * x ^ (α - 1 / 2) := by field_simp
    rw [this, hrK']
    nlinarith [pow_pos (show (0:ℝ) < r by linarith) K]
  -- the real sum is the twisted sum at `t = 0`
  have hcast : ((∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      ((deletedC hα).indicator (fun _ => (1 : ℝ)) p - delWeight α p) : ℝ) : ℂ) =
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        ((deletedC hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) *
          (p : ℂ) ^ (-(((0 : ℝ) : ℂ) * I)) := by
    classical
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [zero_mul, neg_zero, Complex.cpow_zero, mul_one]
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  have hblock : ∀ k ∈ Finset.range (K + 1), ‖cDev α k (goodC hα k) x 0‖ ≤
      a * Real.sqrt ((K : ℝ) + 1) * r ^ k + b * ((K : ℝ) + 1) := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      have h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : (k : ℝ) ≤ K := by exact_mod_cast h
      linarith
    have h1 := norm_cDev_zero_le hα k x
    have h2 := cLam_add_two_le hα0 hα k
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((K : ℝ) + 1) := Real.sqrt_le_sqrt hkK
    calc _ ≤ cLam α k + 2 := h1
      _ ≤ a * Real.sqrt ((k : ℝ) + 1) * r ^ k + b * ((k : ℝ) + 1) := h2
      _ ≤ _ := by gcongr
  have hsK : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast, sum_primes_eq_sum_cDev hα hx 0]
  calc ‖∑ k ∈ Finset.range (K + 1), cDev α k (goodC hα k) x 0‖
      ≤ ∑ k ∈ Finset.range (K + 1), (a * Real.sqrt ((K : ℝ) + 1) * r ^ k + b * ((K : ℝ) + 1)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
    _ = a * Real.sqrt ((K : ℝ) + 1) * ∑ k ∈ Finset.range (K + 1), r ^ k +
          b * ((K : ℝ) + 1) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
        push_cast; ring
    _ ≤ a * (2 * (Real.log x + 1)) * (r / (r - 1) * x ^ (α - 1 / 2)) +
          b * (2 * (Real.log x + 1)) ^ 2 := by
        gcongr
        exact hsK.trans hK1
    _ ≤ (2 * a * (r / (r - 1)) + 4 * b) * x ^ (α - 1 / 2) * (Real.log x + 1) ^ 2 := by
        have hq : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
        have hl1 : 1 ≤ Real.log x + 1 := by linarith
        have h1 : a * (2 * (Real.log x + 1)) * (r / (r - 1) * x ^ (α - 1 / 2)) ≤
            2 * a * (r / (r - 1)) * x ^ (α - 1 / 2) * (Real.log x + 1) ^ 2 := by
          have : (Real.log x + 1) ≤ (Real.log x + 1) ^ 2 := by nlinarith
          have hpos : 0 ≤ 2 * a * (r / (r - 1)) * x ^ (α - 1 / 2) := by positivity
          nlinarith
        have h2 : b * (2 * (Real.log x + 1)) ^ 2 ≤ 4 * b * x ^ (α - 1 / 2) * (Real.log x + 1) ^ 2 := by
          have hpos : 0 ≤ 4 * b * (Real.log x + 1) ^ 2 := by positivity
          nlinarith
        nlinarith

/-- **A deletion set with square-root discrepancy at every frequency and a controlled count.** -/
theorem exists_deletedPrimes_counted (hα1 : 1 / 2 < α) (hα : α < 1) :
    ∃ S : Set ℕ, (∀ p ∈ S, p.Prime) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
        ‖∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * (p : ℂ) ^ (-((t : ℂ) * I))‖ ≤
          C * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt (Real.log (|t| + 2))) ∧
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, 1 ≤ x →
        |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (S.indicator (fun _ => (1 : ℝ)) p - delWeight α p)| ≤
          C' * x ^ (α - 1 / 2) * (Real.log x + 1) ^ 2 :=
  ⟨deletedC hα, fun _ hp => prime_of_mem_deletedC hα hp,
    exists_twisted_bound (by linarith) hα, exists_count_bound hα1 hα⟩

end Counted

end RHTower.BeurlingDeletion
