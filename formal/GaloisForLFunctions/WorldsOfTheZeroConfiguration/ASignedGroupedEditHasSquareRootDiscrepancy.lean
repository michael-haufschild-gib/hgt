import GaloisForLFunctions.RHTower.BeurlingRandomPrimeDeletion
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedPrimeEdits

/-!
# A signed grouped edit with square-root discrepancy at every frequency

Fix `β < α < 1`, `γ ∈ ℝ` and a block index `k₀` with `k₀ (α - β) ≥ 1`.  Give the prime `p` the
weight `w(p) = 2 p^{β-1} |cos(γ log p)|` (`sWeight`) and the sign `σ(p) = -sgn cos(γ log p)`
(`sgnCos`), so that `σ(p) w(p) = -2 p^{β-1} cos(γ log p)`.  In each dyadic block `k ≥ k₀` the
primes are cut into the groups `G_{k,i}` of `RHTower.BeurlingDeletion` (length `⌊2^{k(1-α)}⌋`);
a group has weight `≤ 2 · 2^{k(β-α)} ≤ 1`.  Selecting at most one prime per group, with
probability `w(p)`, and giving it the sign `σ(p)` defines a two-sided edit `e` (`sEdit`).

**Block bound** (`norm_sum_target_testFn_le`).  For the target coefficients
`c(p) = e(p) + 2 p^{β-1} cos(γ log p)` some selection gives, in every block `k ≥ k₀` and for all
real `x`, `t`,

`|Σ_{p ∈ block k, p ≤ x} c(p) p^{-it}| ≤ 26 · 2^{kα/2} √(k+1) √log(|t|+2) + 2`.

The tests and thresholds are those of the deletion construction, with the sign folded into the
test; the failure probabilities sum to `π²/24 < 1` independently of the weights.

**Sparsity** (`card_sEdit_ne_zero_le`).  At most `n_k ≤ 3 · 2^{kα}` primes of block `k` are
edited, and no prime below `2^{k₀}`.
-/

open Complex Finset
open RHTower.BeurlingDeletion GaloisForLFunctions.HTGeometry.GroupedSelection
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit

variable {α β : ℝ}

/-! ## Signs and weights -/

/-- The sign `σ(p) = -sgn cos(γ log p)`. -/
def sgnCos (γ : ℝ) (p : ℕ) : ℤ :=
  if 0 < Real.cos (γ * Real.log p) then -1
  else if Real.cos (γ * Real.log p) < 0 then 1 else 0

/-- The weight `w(p) = 2 p^{β-1} |cos(γ log p)|`. -/
def sWeight (β γ : ℝ) (p : ℕ) : ℝ := 2 * (p : ℝ) ^ (β - 1) * |Real.cos (γ * Real.log p)|

theorem sWeight_nonneg (β γ : ℝ) (p : ℕ) : 0 ≤ sWeight β γ p := by
  unfold sWeight; positivity

theorem sgnCos_mem (γ : ℝ) (p : ℕ) : sgnCos γ p = 1 ∨ sgnCos γ p = -1 ∨ sgnCos γ p = 0 := by
  unfold sgnCos; split_ifs <;> simp

theorem norm_sgnCos_le (γ : ℝ) (p : ℕ) : ‖(sgnCos γ p : ℂ)‖ ≤ 1 := by
  rcases sgnCos_mem γ p with h | h | h <;> rw [h] <;> simp

/-- `σ(p) w(p) = -2 p^{β-1} cos(γ log p)`. -/
theorem sgnCos_mul_sWeight (β γ : ℝ) (p : ℕ) :
    (sgnCos γ p : ℝ) * sWeight β γ p = -(2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) := by
  unfold sgnCos sWeight
  split_ifs with h1 h2
  · rw [abs_of_pos h1]; push_cast; ring
  · rw [abs_of_neg h2]; push_cast; ring
  · have : Real.cos (γ * Real.log p) = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    rw [this]; simp

/-- On the dyadic block `p ≥ 2^k` the selection weight is at most `2 · 2^{k(β - 1)}`. -/
theorem sWeight_le (hβ : β < 1) (γ : ℝ) {k p : ℕ} (hp : 2 ^ k ≤ p) :
    sWeight β γ p ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hpk : ((2 : ℝ) ^ k) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ^ (β - 1) ≤ (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := by
    calc (p : ℝ) ^ (β - 1) ≤ ((2 : ℝ) ^ k) ^ (β - 1) :=
          Real.rpow_le_rpow_of_nonpos h2k hpk (by linarith)
      _ = (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hcos : |Real.cos (γ * Real.log p)| ≤ 1 := Real.abs_cos_le_one _
  unfold sWeight
  calc 2 * (p : ℝ) ^ (β - 1) * |Real.cos (γ * Real.log p)| ≤ 2 * (p : ℝ) ^ (β - 1) * 1 := by
        gcongr
    _ ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := by rw [mul_one]; gcongr

/-- In a block with `k (α - β) ≥ 1` every group has weight `≤ 1`. -/
theorem sum_sWeight_blockGroup_le_one (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) (i : Fin (blockCount α k)) :
    ∑ p ∈ blockGroup α k i, sWeight β γ p ≤ 1 := by
  have hb : ∀ p ∈ blockGroup α k i, sWeight β γ p ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := by
    intro p hp
    simp only [blockGroup, Finset.mem_filter, mem_blockPrimes] at hp
    exact sWeight_le hβ γ hp.1.2.1
  have hcard : ((blockGroup α k i).card : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * (1 - α)) :=
    le_trans (by exact_mod_cast card_blockGroup_le hα k i) (blockLen_le hα k)
  have hexp : (2 : ℝ) ^ ((k : ℝ) * (1 - α)) * (2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1))) ≤ 1 := by
    rw [mul_left_comm, ← Real.rpow_add (by norm_num)]
    have h : (k : ℝ) * (1 - α) + (k : ℝ) * (β - 1) ≤ -1 := by nlinarith
    calc 2 * (2 : ℝ) ^ ((k : ℝ) * (1 - α) + (k : ℝ) * (β - 1)) ≤ 2 * (2 : ℝ) ^ (-1 : ℝ) := by
          gcongr; norm_num
      _ = 1 := by rw [Real.rpow_neg_one]; norm_num
  calc ∑ p ∈ blockGroup α k i, sWeight β γ p
      ≤ ∑ _p ∈ blockGroup α k i, 2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1)) := Finset.sum_le_sum hb
    _ = (blockGroup α k i).card * (2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ ((k : ℝ) * (1 - α)) * (2 * (2 : ℝ) ^ ((k : ℝ) * (β - 1))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 1 := hexp

/-! ## Signed tests and the block deviation -/

/-- The signed test `p ↦ σ(p) 1[0 < p ≤ x] p^{-it}`. -/
def sTest (γ x t : ℝ) (p : ℕ) : ℂ := (sgnCos γ p : ℂ) * testFn x t p

theorem norm_sTest_le (γ x t : ℝ) (p : ℕ) : ‖sTest γ x t p‖ ≤ 1 := by
  unfold sTest
  rw [norm_mul]
  calc ‖(sgnCos γ p : ℂ)‖ * ‖testFn x t p‖ ≤ 1 * 1 :=
        mul_le_mul (norm_sgnCos_le γ p) (norm_testFn_le x t p) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The signed deviation of block `k` under the choice `ω`. -/
def sBlockDev (α β γ : ℝ) (k : ℕ) (ω : Fin (blockCount α k) → ℕ) (x t : ℝ) : ℂ :=
  ∑ i, groupDev (blockGroup α k) (sWeight β γ) (sTest γ x t) i (ω i)

/-- **One block admits a good signed selection.** -/
theorem exists_sBlockChoice (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) :
    ∃ ω : Fin (blockCount α k) → ℕ, (∀ i, ω i = 0 ∨ ω i ∈ blockGroup α k i) ∧
      ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
        ‖sBlockDev α β γ k ω q (netPoint α k b m)‖ < threshold α k m := by
  obtain ⟨ω, hω, hdev⟩ := exists_selection (G := blockGroup α k) (w := sWeight β γ)
    (fun p => sWeight_nonneg β γ p) (fun i => sum_sWeight_blockGroup_le_one hα hβ γ hk i)
    (fun i => zero_not_mem_blockGroup α k i)
    (E := {q // q ∈ blockPrimes k} × Bool × ℕ)
    (fun e => sTest γ e.1 (netPoint α k e.2.1 e.2.2)) (fun e p => norm_sTest_le _ _ _ p)
    (fun e => threshold α k e.2.2) (fun e => threshold_nonneg α k e.2.2) (tsum_failure_lt α k)
  exact ⟨ω, hω, fun q b m => hdev (q, b, m)⟩

/-- Changing `t` by `h` moves the signed block deviation by at most `2 n_k (k+1) |h|`. -/
theorem norm_sBlockDev_sub_le (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) (ω : Fin (blockCount α k) → ℕ) (x t t' : ℝ) :
    ‖sBlockDev α β γ k ω x t - sBlockDev α β γ k ω x t'‖ ≤
      2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
  unfold sBlockDev
  rw [← Finset.sum_sub_distrib]
  have hD : 0 ≤ ((k : ℝ) + 1) * |t - t'| := by positivity
  calc ‖∑ i, (groupDev (blockGroup α k) (sWeight β γ) (sTest γ x t) i (ω i) -
        groupDev (blockGroup α k) (sWeight β γ) (sTest γ x t') i (ω i))‖
      ≤ ∑ i : Fin (blockCount α k), 2 * (((k : ℝ) + 1) * |t - t'|) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [groupDev_sub]
        refine norm_groupDev_le_of_le _ (fun p hp => ?_) (fun p => sWeight_nonneg β γ p)
          (fun i => sum_sWeight_blockGroup_le_one hα hβ γ hk i) hD _
        have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
        have hpos : 0 < p := (mem_blockPrimes.mp hpb).1.pos
        have hsub : sTest γ x t p - sTest γ x t' p =
            (sgnCos γ p : ℂ) * (testFn x t p - testFn x t' p) := by
          unfold sTest; ring
        rw [hsub, norm_mul]
        refine (mul_le_of_le_one_left (norm_nonneg _) (norm_sgnCos_le γ p)).trans ?_
        unfold testFn
        split_ifs with h
        · refine (norm_cpow_sub_cpow_le hpos t t').trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (log_le_of_mem_blockPrimes hpb) (abs_nonneg _)
        · simpa using hD
    _ = 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The signed block deviation only depends on the cutoff through the block primes below it. -/
theorem sBlockDev_eq_of_cutoff (γ : ℝ) (k : ℕ) (ω : Fin (blockCount α k) → ℕ) {x y : ℝ}
    (h : ∀ p ∈ blockPrimes k, ((p : ℝ) ≤ x ↔ (p : ℝ) ≤ y)) (t : ℝ) :
    sBlockDev α β γ k ω x t = sBlockDev α β γ k ω y t := by
  unfold sBlockDev
  refine Finset.sum_congr rfl fun i _ => groupDev_congr (fun p hp => ?_) _
  have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
  unfold sTest testFn
  simp only [h p hpb]

theorem sBlockDev_zero_of_cutoff (γ : ℝ) (k : ℕ) (ω : Fin (blockCount α k) → ℕ) {x : ℝ}
    (h : ∀ p ∈ blockPrimes k, x < p) (t : ℝ) : sBlockDev α β γ k ω x t = 0 := by
  unfold sBlockDev
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [groupDev_congr (φ' := fun _ => 0) (fun p hp => ?_)]
  · simp [groupDev]
  · have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
    unfold sTest testFn
    rw [if_neg fun h' => absurd h'.2 (not_le.mpr (h p hpb)), mul_zero]

/-- **The signed block bound on the whole line.** -/
theorem norm_sBlockDev_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) {ω : Fin (blockCount α k) → ℕ}
    (hω : ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
      ‖sBlockDev α β γ k ω q (netPoint α k b m)‖ < threshold α k m) (x t : ℝ) :
    ‖sBlockDev α β γ k ω x t‖ ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
      Real.sqrt (Real.log (|t| + 2)) + 2 := by
  classical
  have hRHS : 0 ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
      Real.sqrt (Real.log (|t| + 2)) := by positivity
  set P := (blockPrimes k).filter fun p : ℕ => ((p : ℝ) ≤ x) with hP
  by_cases hne : P.Nonempty
  swap
  · rw [sBlockDev_zero_of_cutoff γ k ω (fun p hp => ?_) t]
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
  rw [sBlockDev_eq_of_cutoff γ k ω hcut t]
  set η := netStep α k with hη
  have hη0 : 0 < η := netStep_pos α k
  set m : ℕ := ⌊|t| / η⌋₊ with hm
  have hm1 : (m : ℝ) ≤ |t| / η := Nat.floor_le (div_nonneg (abs_nonneg t) hη0.le)
  have hm2 : |t| / η < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  set b : Bool := decide (0 ≤ t) with hb
  have hclose : |t - netPoint α k b m| ≤ η := by
    have hmη : (m : ℝ) * η ≤ |t| := by rwa [le_div_iff₀ hη0] at hm1
    have hmη' : |t| < ((m : ℝ) + 1) * η := by rwa [div_lt_iff₀ hη0] at hm2
    unfold netPoint
    rw [← hη]
    by_cases ht : 0 ≤ t
    · have : b = true := by rw [hb]; exact decide_eq_true ht
      rw [this, if_pos rfl, abs_of_nonneg ht] at *
      rw [abs_le]; constructor <;> nlinarith
    · have : b = false := by rw [hb]; exact decide_eq_false ht
      rw [this, if_neg (by simp)]
      rw [abs_of_neg (not_le.mp ht)] at hmη hmη'
      rw [abs_le]; constructor <;> nlinarith
  have hlip := norm_sBlockDev_sub_le hα hβ γ hk ω q t (netPoint α k b m)
  have hlip' : 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - netPoint α k b m|) ≤ 2 := by
    have hn0 : (0 : ℝ) < blockCount α k := by exact_mod_cast blockCount_pos α k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc _ ≤ 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * η) := by gcongr
      _ = 2 := by rw [hη]; unfold netStep; field_simp
  have hnet := hω ⟨q, hqb⟩ b m
  have hthr := threshold_le hα0 hα k m hm1
  calc ‖sBlockDev α β γ k ω q t‖
      ≤ ‖sBlockDev α β γ k ω q (netPoint α k b m)‖ +
          ‖sBlockDev α β γ k ω q t - sBlockDev α β γ k ω q (netPoint α k b m)‖ := by
        have := norm_add_le (sBlockDev α β γ k ω q (netPoint α k b m))
          (sBlockDev α β γ k ω q t - sBlockDev α β γ k ω q (netPoint α k b m))
        rwa [add_sub_cancel] at this
    _ ≤ threshold α k m + 2 := by
        have := hnet.le
        linarith [hlip.trans hlip']
    _ ≤ _ := by linarith

/-! ## Gluing the blocks -/

theorem one_le_of_le {k₀ k : ℕ} (hαβ : β < α) (hk₀ : 1 ≤ (k₀ : ℝ) * (α - β)) (hk : k₀ ≤ k) :
    1 ≤ (k : ℝ) * (α - β) :=
  hk₀.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by linarith))

open Classical in
/-- A good signed selection in every block `k ≥ k₀`, and no selection below. -/
def sGood (α β γ : ℝ) (k₀ k : ℕ) : Fin (blockCount α k) → ℕ :=
  if h : α < 1 ∧ β < 1 ∧ 1 ≤ (k : ℝ) * (α - β) ∧ k₀ ≤ k then
    Classical.choose (exists_sBlockChoice h.1 h.2.1 γ h.2.2.1)
  else fun _ => 0

theorem sGood_spec (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) (hkk : k₀ ≤ k) :
    (∀ i, sGood α β γ k₀ k i = 0 ∨ sGood α β γ k₀ k i ∈ blockGroup α k i) ∧
      ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
        ‖sBlockDev α β γ k (sGood α β γ k₀ k) q (netPoint α k b m)‖ < threshold α k m := by
  have h : α < 1 ∧ β < 1 ∧ 1 ≤ (k : ℝ) * (α - β) ∧ k₀ ≤ k := ⟨hα, hβ, hk, hkk⟩
  unfold sGood
  rw [dif_pos h]
  exact Classical.choose_spec (exists_sBlockChoice h.1 h.2.1 γ h.2.2.1)

theorem sGood_mem (α β γ : ℝ) (k₀ k : ℕ) (i : Fin (blockCount α k)) :
    sGood α β γ k₀ k i = 0 ∨ sGood α β γ k₀ k i ∈ blockGroup α k i := by
  by_cases h : α < 1 ∧ β < 1 ∧ 1 ≤ (k : ℝ) * (α - β) ∧ k₀ ≤ k
  · exact (sGood_spec h.1 h.2.1 γ h.2.2.1 h.2.2.2).1 i
  · left; unfold sGood; rw [dif_neg h]

theorem sGood_eq_zero (α β γ : ℝ) {k₀ k : ℕ} (hk : k < k₀) (i : Fin (blockCount α k)) :
    sGood α β γ k₀ k i = 0 := by
  unfold sGood
  rw [dif_neg fun h => absurd h.2.2.2 (not_le.mpr hk)]

/-- The selected primes. -/
def selected (α β γ : ℝ) (k₀ : ℕ) : Set ℕ := {p | ∃ k i, sGood α β γ k₀ k i = p ∧ p ≠ 0}

open Classical in
/-- **The signed edit**: `e(p) = σ(p)` on the selected primes, `0` elsewhere. -/
def sEdit (α β γ : ℝ) (k₀ : ℕ) (p : ℕ) : ℤ := if p ∈ selected α β γ k₀ then sgnCos γ p else 0

theorem prime_of_mem_selected {γ : ℝ} {k₀ p : ℕ} (hp : p ∈ selected α β γ k₀) : p.Prime := by
  obtain ⟨k, i, hki, hp0⟩ := hp
  rcases sGood_mem α β γ k₀ k i with h | h
  · exact absurd (hki ▸ h) hp0
  · rw [hki] at h
    exact (mem_blockPrimes.mp (Finset.mem_filter.mp h).1).1

theorem isEdit_sEdit (α β γ : ℝ) (k₀ : ℕ) : IsEdit (sEdit α β γ k₀) := by
  classical
  refine ⟨fun p hp => ?_, fun p => ?_⟩
  · unfold sEdit
    rw [if_neg fun h => hp (prime_of_mem_selected h)]
  · unfold sEdit
    split_ifs
    · exact sgnCos_mem γ p
    · simp

/-- A block prime is selected exactly when it is the chosen prime of its group. -/
theorem mem_selected_iff {γ : ℝ} {k₀ k p : ℕ} (hp : p ∈ blockPrimes k) :
    p ∈ selected α β γ k₀ ↔ sGood α β γ k₀ k ⟨blockIdx α k p, blockIdx_lt hp⟩ = p := by
  constructor
  · rintro ⟨k', i, hki, hp0⟩
    rcases sGood_mem α β γ k₀ k' i with h | h
    · exact absurd (hki ▸ h) hp0
    · rw [hki] at h
      obtain ⟨hpb', hidx⟩ := Finset.mem_filter.mp h
      have hk : k' = k :=
        (log_eq_of_mem_blockPrimes hpb').symm.trans (log_eq_of_mem_blockPrimes hp)
      subst hk
      have hi : (⟨blockIdx α k' p, blockIdx_lt hp⟩ : Fin (blockCount α k')) = i := Fin.ext hidx
      rw [hi]; exact hki
  · intro h
    exact ⟨k, _, h, (mem_blockPrimes.mp hp).1.ne_zero⟩

/-- No prime below `2^{k₀}` is edited. -/
theorem sEdit_eq_zero_of_lt (γ : ℝ) {k₀ p : ℕ} (hp : p < 2 ^ k₀) : sEdit α β γ k₀ p = 0 := by
  classical
  unfold sEdit
  rw [if_neg]
  rintro ⟨k, i, hki, hp0⟩
  rcases sGood_mem α β γ k₀ k i with h | h
  · exact hp0 (hki ▸ h)
  · rw [hki] at h
    have hpb := (Finset.mem_filter.mp h).1
    by_cases hk : k < k₀
    · rw [sGood_eq_zero α β γ hk i] at hki; exact hp0 hki.symm
    · push Not at hk
      have h1 := (mem_blockPrimes.mp hpb).2.1
      have h2 : 2 ^ k₀ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega

/-- The target coefficient `c(p) = e(p) + 2 p^{β-1} cos(γ log p)` above the cutoff. -/
def target (α β γ : ℝ) (k₀ p : ℕ) : ℂ :=
  (sEdit α β γ k₀ p : ℂ) + ((2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) : ℝ) : ℂ)

/-- The signed block deviation of the good selection is the block sum of the target. -/
theorem sBlockDev_sGood (γ : ℝ) {k₀ k : ℕ} (x t : ℝ) :
    sBlockDev α β γ k (sGood α β γ k₀ k) x t =
      ∑ p ∈ blockPrimes k, target α β γ k₀ p * testFn x t p := by
  classical
  set g : ℕ → Fin (blockCount α k) := fun p =>
    if h : p ∈ blockPrimes k then ⟨blockIdx α k p, blockIdx_lt h⟩ else ⟨0, blockCount_pos α k⟩
  have hgroup : ∀ i, blockGroup α k i = (blockPrimes k).filter fun p => g p = i := by
    intro i
    unfold blockGroup
    refine Finset.filter_congr fun p hp => ?_
    simp only [g, dif_pos hp, Fin.ext_iff]
  unfold sBlockDev groupDev
  simp_rw [hgroup]
  rw [← Finset.sum_fiberwise_of_maps_to (s := blockPrimes k) (t := Finset.univ) (g := g)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpb, hgi⟩ := Finset.mem_filter.mp hp
  have hgi' : (⟨blockIdx α k p, blockIdx_lt hpb⟩ : Fin (blockCount α k)) = i := by
    rw [← hgi]; simp only [g, dif_pos hpb]
  have hsw := sgnCos_mul_sWeight β γ p
  unfold sTest target sEdit
  by_cases hdel : p ∈ selected α β γ k₀
  · rw [if_pos hdel, if_pos (by rw [← hgi']; exact (mem_selected_iff hpb).mp hdel)]
    have : ((2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) : ℝ) : ℂ) =
        -((sgnCos γ p : ℝ) * sWeight β γ p : ℝ) := by rw [hsw]; push_cast; ring
    rw [this]; push_cast; ring
  · rw [if_neg hdel, if_neg fun h => hdel ((mem_selected_iff hpb).mpr (by rw [hgi']; exact h))]
    have : ((2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) : ℝ) : ℂ) =
        -((sgnCos γ p : ℝ) * sWeight β γ p : ℝ) := by rw [hsw]; push_cast; ring
    rw [this]; push_cast; ring

/-- **The block bound for the target.**  In every block `k ≥ k₀` and for all real `x`, `t`,
`|Σ_{p ∈ block, p ≤ x} c(p) p^{-it}| ≤ 26 · 2^{kα/2} √(k+1) √log(|t|+2) + 2`. -/
theorem norm_sum_target_testFn_le (hα0 : 0 < α) (hα : α < 1) (hβ : β < 1) (γ : ℝ) {k₀ k : ℕ}
    (hk : 1 ≤ (k : ℝ) * (α - β)) (hkk : k₀ ≤ k) (x t : ℝ) :
    ‖∑ p ∈ blockPrimes k, target α β γ k₀ p * testFn x t p‖ ≤
      26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
        Real.sqrt (Real.log (|t| + 2)) + 2 := by
  rw [← sBlockDev_sGood γ x t]
  exact norm_sBlockDev_le hα0 hα hβ γ hk (sGood_spec hα hβ γ hk hkk).2 x t

/-! ## Sparsity -/

/-- **At most `n_k` primes of block `k` are edited.** -/
theorem card_sEdit_ne_zero_le (γ : ℝ) (k₀ k : ℕ) :
    ((blockPrimes k).filter fun p => sEdit α β γ k₀ p ≠ 0).card ≤ blockCount α k := by
  classical
  calc ((blockPrimes k).filter fun p => sEdit α β γ k₀ p ≠ 0).card
      ≤ (Finset.univ : Finset (Fin (blockCount α k))).card := by
        refine Finset.card_le_card_of_injOn
          (fun p => if h : p ∈ blockPrimes k then ⟨blockIdx α k p, blockIdx_lt h⟩
            else ⟨0, blockCount_pos α k⟩) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
          (fun p hp q hq hpq => ?_)
        obtain ⟨hpb, hpe⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqb, hqe⟩ := Finset.mem_filter.mp hq
        have hps : p ∈ selected α β γ k₀ := by
          by_contra h; apply hpe; unfold sEdit; rw [if_neg h]
        have hqs : q ∈ selected α β γ k₀ := by
          by_contra h; apply hqe; unfold sEdit; rw [if_neg h]
        have h1 := (mem_selected_iff hpb).mp hps
        have h2 := (mem_selected_iff hqb).mp hqs
        simp only [dif_pos hpb, dif_pos hqb] at hpq
        rw [← h1, ← h2, hpq]
    _ = blockCount α k := by rw [Finset.card_univ, Fintype.card_fin]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
