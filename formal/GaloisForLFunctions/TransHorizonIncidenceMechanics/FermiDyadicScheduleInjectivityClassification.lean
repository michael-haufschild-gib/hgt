import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiValuationSamplingAndPronicObservability
import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicIncidenceRecurrenceAndArbitraryPhaseObservability

/-!
# Which dyadic Fermi schedules see the sieve

A **dyadic schedule** `S ⊆ ℕ` reads the Fermi boundary jumps `J(n)` at the boundaries `n ≥ 1`
whose dyadic level `v₂(n)` lies in `S`. Along a dyadic ray `n = 2^k b` (`b` odd) put
`z_k = s_{N,c}(2^k b)`. The level-`0` reading is `-z_0`, the level-`k` reading is
`2 z_{k-1} - z_k`, and the ray saturates at `L = ⌊log₂ N⌋`: `z_k = z_L` for `k ≥ L`, so every
level above `L` reads the same value `z_L`. The schedule therefore sees `L + 2` **slots**: the
levels `0, …, L`, and the saturated slot `L + 1` (observed when `S` meets `[L+1, ∞)`). The slots
give the relations `z_0 = 0`, `z_k = 2 z_{k-1}` and `z_L = 0`, a chain pinned at both ends.

**Classification.** For `N ≥ 1` a schedule determines every horizon-`N` row if and only if it
misses at most one slot. With one missing slot the chain is pinned from both sides; with two
missing slots `a < b` the profile `z_k = 2^k` on `[a, b)` (realized by a row supported on powers
of two) is invisible. In particular the odd-and-four-divisible schedule (missing slot `1`) and the
full schedule are injective, odd boundaries alone are not once `N ≥ 2`, and an injective schedule
needs at least `⌊log₂ N⌋ + 1` slots: the observation depth equals the dyadic depth of the horizon.
-/

open Finset
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The schedule reading `J(n)` at the levels `v₂(n) ∈ S` determines every row on `[1, N]`. -/
def FermiScheduleInjective (N : ℕ) (S : Set ℕ) : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, 1 ≤ n → padicValNat 2 n ∈ S → fermiBoundaryJump N c n = 0) →
    ∀ d ∈ Icc 1 N, c d = 0

/-- Slot `k ≤ log₂ N` is the level `k`; slot `log₂ N + 1` is observed when some level above
`log₂ N` is read. -/
def FermiSlotObserved (N : ℕ) (S : Set ℕ) (k : ℕ) : Prop :=
  if k ≤ Nat.log 2 N then k ∈ S else ∃ j, Nat.log 2 N + 1 ≤ j ∧ j ∈ S

/-! ### Dyadic rays -/

/-- The dyadic level of `2 ^ k * b` at odd `b` is `k`. -/
theorem padicValNat_two_pow_mul_odd {b : ℕ} (hb : ¬ 2 ∣ b) (k : ℕ) :
    padicValNat 2 (2 ^ k * b) = k := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [padicValNat.mul (by positivity) hb0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hb, add_zero]

private theorem two_pow_dvd_two_pow_mul_odd_iff {b : ℕ} (hb : ¬ 2 ∣ b) (j k : ℕ) :
    2 ^ j ∣ 2 ^ k * b ↔ j ≤ k := by
  have hcop : Nat.Coprime (2 ^ j) b :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hb)
  rw [hcop.dvd_mul_right, Nat.pow_dvd_pow_iff_le_right (by norm_num)]

/-- **Saturation.** Above level `⌊log₂ N⌋` a dyadic ray is constant. -/
theorem sieveSeq_two_pow_mul_saturate (N : ℕ) (c : ℕ → ℝ) (b : ℕ) {k : ℕ}
    (hk : Nat.log 2 N ≤ k) :
    sieveSeq N c (2 ^ k * b) = sieveSeq N c (2 ^ Nat.log 2 N * b) := by
  unfold sieveSeq
  refine sum_congr (filter_congr fun d hd => ?_) fun _ _ => rfl
  have hdN := (mem_Icc.mp hd).2
  constructor
  · intro h
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp h
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h₁
    have hd2 : 0 < d₂ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hd
    have hiL : i ≤ Nat.log 2 N := by
      have h2i : 2 ^ i ≤ N := le_trans (Nat.le_mul_of_pos_right _ hd2) hdN
      exact Nat.le_log_of_pow_le (by norm_num) h2i
    exact mul_dvd_mul (Nat.pow_dvd_pow 2 hiL) h₂
  · intro h
    exact h.trans (mul_dvd_mul_right (Nat.pow_dvd_pow 2 hk) b)

/-- The level-`0` boundary of a dyadic ray reads minus the response at the odd base. -/
theorem fermiBoundaryJump_level_zero (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : ¬ 2 ∣ b) :
    fermiBoundaryJump N c b = -sieveSeq N c b := by
  obtain ⟨m, rfl⟩ : ∃ m, b = 2 * m + 1 := ⟨b / 2, by omega⟩
  exact fermiBoundaryJump_odd N c m

/-- The level-`k+1` boundary of a dyadic ray reads twice the level-`k` response minus its own. -/
theorem fermiBoundaryJump_level_succ (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : ¬ 2 ∣ b) (k : ℕ) :
    fermiBoundaryJump N c (2 ^ (k + 1) * b) =
      2 * sieveSeq N c (2 ^ k * b) - sieveSeq N c (2 ^ (k + 1) * b) := by
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hb)
  have h1 : 1 ≤ 2 ^ k * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ k * b = m + 1 := ⟨2 ^ k * b - 1, by omega⟩
  have h2 : 2 ^ (k + 1) * b = 2 * m + 2 := by rw [pow_succ]; linarith
  rw [h2, fermiBoundaryJump_even N c m, ← hm, ← h2]

/-! ### Pinned chains -/

/-- A chain with relations `z_0 = 0`, `z_k = 2 z_{k-1}` (`1 ≤ k ≤ L`) and `z_L = 0`, of which at
most one is missing, vanishes on `[0, L]`. -/
private theorem pinned_chain_vanish {L : ℕ} (z : ℕ → ℝ) (obs : ℕ → Prop)
    (huniq : ∀ a b, a ≤ L + 1 → b ≤ L + 1 → ¬ obs a → ¬ obs b → a = b)
    (h0 : obs 0 → z 0 = 0) (hk : ∀ k, 1 ≤ k → k ≤ L → obs k → z k = 2 * z (k - 1))
    (htop : obs (L + 1) → z L = 0) : ∀ k ≤ L, z k = 0 := by
  by_cases hall : ∀ k ≤ L, obs k
  · intro k hkL
    induction k with
    | zero => exact h0 (hall 0 (Nat.zero_le _))
    | succ k ih => rw [hk (k + 1) (by omega) hkL (hall _ hkL), Nat.add_sub_cancel,
        ih (by omega)]; ring
  push Not at hall
  obtain ⟨a, haL, ha⟩ := hall
  have hother : ∀ k ≤ L + 1, k ≠ a → obs k := fun k hk hne => by
    by_contra h; exact hne (huniq k a hk (by omega) h ha)
  have hzL : z L = 0 := htop (hother (L + 1) le_rfl (by omega))
  have hlow : ∀ k < a, z k = 0 := by
    intro k hka
    induction k with
    | zero => exact h0 (hother 0 (by omega) (by omega))
    | succ k ih => rw [hk (k + 1) (by omega) (by omega) (hother _ (by omega) (by omega)),
        Nat.add_sub_cancel, ih (by omega)]; ring
  have hhigh : ∀ j, a + j ≤ L → z (L - j) = 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using hzL
    | succ j ih =>
      intro hj
      have h := hk (L - j) (by omega) (by omega) (hother _ (by omega) (by omega))
      rw [ih (by omega), show L - j - 1 = L - (j + 1) by omega] at h
      linarith
  intro k hkL
  by_cases hka : k < a
  · exact hlow k hka
  · have := hhigh (L - k) (by omega); rwa [show L - (L - k) = k by omega] at this

/-! ### Powers-of-two rows -/

/-- The row `c(2^j) = g(j)` for `j ≤ L`, zero elsewhere: it synthesizes a prescribed dyadic
ray profile from its discrete differences. -/
def fermiDyadicPowerRow (L : ℕ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d = 2 ^ Nat.log 2 d ∧ Nat.log 2 d ≤ L then g (Nat.log 2 d) else 0

/-- The response of a powers-of-two row along a dyadic ray is the prefix sum of its weights,
saturating at level `L`. -/
theorem sieveSeq_fermiDyadicPowerRow {N L : ℕ} (hLN : 2 ^ L ≤ N) (g : ℕ → ℝ) {b : ℕ}
    (hb : ¬ 2 ∣ b) (k : ℕ) :
    sieveSeq N (fermiDyadicPowerRow L g) (2 ^ k * b) = ∑ j ∈ range (min k L + 1), g j := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  unfold sieveSeq
  have himg : (range (min k L + 1)).image (fun j => 2 ^ j) ⊆
      (Icc 1 N).filter (fun d => d ∣ 2 ^ k * b) := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    have hjm := mem_range.mp hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_two_pow, ?_⟩,
      (two_pow_dvd_two_pow_mul_odd_iff hb j k).mpr (by omega)⟩
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hLN
  rw [← sum_subset himg ?_, sum_image fun i _ j _ h => Nat.pow_right_injective le_rfl h]
  · refine sum_congr rfl fun j hj => ?_
    have hjm := mem_range.mp hj
    unfold fermiDyadicPowerRow
    rw [Nat.log_pow (by norm_num), if_pos ⟨rfl, by omega⟩]
  · intro d hd hnot
    unfold fermiDyadicPowerRow
    rw [if_neg]
    rintro ⟨hdp, hdL⟩
    apply hnot
    obtain ⟨-, hdvd⟩ := mem_filter.mp hd
    rw [hdp] at hdvd ⊢
    exact mem_image.mpr ⟨Nat.log 2 d, mem_range.mpr (by
      have := (two_pow_dvd_two_pow_mul_odd_iff hb _ k).mp hdvd; omega), rfl⟩

/-- Discrete differences telescope to the profile value. -/
theorem sum_range_discreteDiff_telescope (z : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (m + 1), (z j - if j = 0 then 0 else z (j - 1)) = z m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), Nat.add_sub_cancel]; ring

/-! ### The classification -/

/-- **Dyadic schedule classification.** For `N ≥ 1`, a dyadic schedule determines every
horizon-`N` row if and only if it misses at most one of the `⌊log₂ N⌋ + 2` slots. -/
theorem fermiScheduleInjective_iff {N : ℕ} (hN : 1 ≤ N) (S : Set ℕ) :
    FermiScheduleInjective N S ↔
      ∀ a b, a ≤ Nat.log 2 N + 1 → b ≤ Nat.log 2 N + 1 →
        ¬ FermiSlotObserved N S a → ¬ FermiSlotObserved N S b → a = b := by
  set L := Nat.log 2 N
  have hLN : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  constructor
  · -- two missing slots `a < b`: the profile `z_k = 2^k` on `[a, b)` is invisible
    intro hinj
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, b₀, ha₀, hb₀, hna₀, hnb₀, hne⟩ := hcon
    wlog hab : a₀ < b₀ generalizing a₀ b₀
    · exact this b₀ a₀ hb₀ ha₀ hnb₀ hna₀ hne.symm (by omega)
    set z : ℕ → ℝ := fun j => if a₀ ≤ j ∧ j < b₀ then (2 : ℝ) ^ j else 0
    set g : ℕ → ℝ := fun j => z j - if j = 0 then 0 else z (j - 1)
    have hs : ∀ b, ¬ 2 ∣ b → ∀ k, sieveSeq N (fermiDyadicPowerRow L g) (2 ^ k * b) = z (min k L) := by
      intro b hb k
      rw [sieveSeq_fermiDyadicPowerRow hLN g hb k, sum_range_discreteDiff_telescope]
    have hread : ∀ n, 1 ≤ n → padicValNat 2 n ∈ S → fermiBoundaryJump N (fermiDyadicPowerRow L g) n = 0 := by
      intro n hn hS
      obtain ⟨k, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
      rw [padicValNat_two_pow_mul_odd hb] at hS
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- level zero is observed, so `a₀ ≥ 1` and `z_0 = 0`
        have hobs : FermiSlotObserved N S 0 := by
          unfold FermiSlotObserved; rw [if_pos (Nat.zero_le _)]; exact hS
        have ha1 : a₀ ≠ 0 := fun h => hna₀ (h ▸ hobs)
        rw [pow_zero, one_mul, fermiBoundaryJump_level_zero N _ hb, show b = 2 ^ 0 * b by simp, hs b hb 0]
        simp [z]; omega
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [fermiBoundaryJump_level_succ N _ hb k, hs b hb k, hs b hb (k + 1)]
      by_cases hkL : k + 1 ≤ L
      · have hobs : FermiSlotObserved N S (k + 1) := by
          unfold FermiSlotObserved; rw [if_pos hkL]; exact hS
        have h1 : k + 1 ≠ a₀ := fun h => hna₀ (h ▸ hobs)
        have h2 : k + 1 ≠ b₀ := fun h => hnb₀ (h ▸ hobs)
        rw [min_eq_left (by omega), min_eq_left hkL]
        simp only [z]
        by_cases hin : a₀ ≤ k ∧ k < b₀
        · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, pow_succ]; ring
        · rw [if_neg hin, if_neg (by omega)]; ring
      · -- the saturated slot is observed, so `b₀ ≤ L` and `z_L = 0`
        have hobs : FermiSlotObserved N S (L + 1) := by
          unfold FermiSlotObserved; rw [if_neg (by omega)]; exact ⟨k + 1, by omega, hS⟩
        have hb1 : b₀ ≠ L + 1 := fun h => hnb₀ (h ▸ hobs)
        rw [min_eq_right (by omega), min_eq_right (by omega)]
        simp only [z]
        rw [if_neg (by omega)]; ring
    have h := hinj _ hread (2 ^ a₀) (mem_Icc.mpr ⟨Nat.one_le_two_pow,
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hLN⟩)
    unfold fermiDyadicPowerRow at h
    rw [Nat.log_pow (by norm_num), if_pos ⟨rfl, by omega⟩] at h
    simp only [g, z] at h
    rw [if_pos ⟨le_rfl, hab⟩] at h
    split_ifs at h with h0 h1
    · norm_num at h
    · omega
    · norm_num at h
  · -- at most one missing slot: every dyadic ray is a pinned chain
    intro huniq c hread
    have hray : ∀ b, ¬ 2 ∣ b → ∀ k ≤ L, sieveSeq N c (2 ^ k * b) = 0 := by
      intro b hb
      have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hb)
      refine pinned_chain_vanish (L := L) (fun k => sieveSeq N c (2 ^ k * b))
        (FermiSlotObserved N S) huniq ?_ ?_ ?_
      · intro hobs
        unfold FermiSlotObserved at hobs; rw [if_pos (Nat.zero_le _)] at hobs
        have h := hread b hb1 (by rw [padicValNat.eq_zero_of_not_dvd hb]; exact hobs)
        rw [fermiBoundaryJump_level_zero N c hb] at h
        simp only [pow_zero, one_mul]; linarith
      · intro k hk1 hkL hobs
        unfold FermiSlotObserved at hobs; rw [if_pos hkL] at hobs
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have h := hread (2 ^ (k + 1) * b) (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)))
          (by rw [padicValNat_two_pow_mul_odd hb]; exact hobs)
        rw [fermiBoundaryJump_level_succ N c hb k] at h
        simp only [Nat.add_sub_cancel]; linarith
      · intro hobs
        unfold FermiSlotObserved at hobs; rw [if_neg (by omega)] at hobs
        obtain ⟨j, hj, hjS⟩ := hobs
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have h := hread (2 ^ (j + 1) * b) (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)))
          (by rw [padicValNat_two_pow_mul_odd hb]; exact hjS)
        rw [fermiBoundaryJump_level_succ N c hb j, sieveSeq_two_pow_mul_saturate N c b (by omega : L ≤ j),
          sieveSeq_two_pow_mul_saturate N c b (by omega : L ≤ j + 1)] at h
        linarith
    apply eq_zero_of_sieveSeq_initial
    intro n hn
    obtain ⟨k, b, hb, rfl⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by have := (mem_Icc.mp hn).1; omega : n ≠ 0) 2
        (by norm_num)
    by_cases hkL : k ≤ L
    · exact hray b hb k hkL
    · rw [sieveSeq_two_pow_mul_saturate N c b (by omega : L ≤ k)]
      exact hray b hb L le_rfl

/-! ### Consequences -/

/-- The odd-and-four-divisible schedule (missing only level `1`) is injective. -/
theorem fermiScheduleInjective_selected {N : ℕ} (hN : 1 ≤ N) :
    FermiScheduleInjective N {k | k ≠ 1} := by
  rw [fermiScheduleInjective_iff hN]
  intro a b ha hb hna hnb
  unfold FermiSlotObserved at hna hnb
  split_ifs at hna hnb with h1 h2 h2
  · simp only [Set.mem_setOf_eq, not_not] at hna hnb; omega
  · exact absurd ⟨Nat.log 2 N + 2, by omega, by simp⟩ hnb
  · exact absurd ⟨Nat.log 2 N + 2, by omega, by simp⟩ hna
  · exact absurd ⟨Nat.log 2 N + 2, by omega, by simp⟩ hna

/-- The full schedule is injective. -/
theorem fermiScheduleInjective_univ {N : ℕ} (hN : 1 ≤ N) :
    FermiScheduleInjective N Set.univ := by
  rw [fermiScheduleInjective_iff hN]
  intro a b _ _ hna
  unfold FermiSlotObserved at hna
  split_ifs at hna
  · exact absurd (Set.mem_univ a) hna
  · exact absurd ⟨Nat.log 2 N + 1, le_rfl, Set.mem_univ _⟩ hna

/-- Odd boundaries alone see the sieve only at horizon `1`. -/
theorem fermiScheduleInjective_odd_iff {N : ℕ} (hN : 1 ≤ N) :
    FermiScheduleInjective N {0} ↔ N = 1 := by
  rw [fermiScheduleInjective_iff hN]
  constructor
  · intro h
    by_contra hN1
    have hL : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by omega)
    have := h 1 (Nat.log 2 N + 1) (by omega) le_rfl
      (by unfold FermiSlotObserved; rw [if_pos hL]; simp)
      (by unfold FermiSlotObserved; rw [if_neg (by omega)]; rintro ⟨j, hj, hj0⟩
          simp only [Set.mem_singleton_iff] at hj0; omega)
    omega
  · rintro rfl
    intro a b ha hb hna hnb
    simp only [Nat.log_one_right, zero_add] at ha hb
    unfold FermiSlotObserved at hna hnb
    simp only [Nat.log_one_right, nonpos_iff_eq_zero, Set.mem_singleton_iff] at hna hnb
    split_ifs at hna hnb <;> omega

/-- **Observation depth.** An injective schedule observes at least `⌊log₂ N⌋ + 1` slots; and
any two missing levels `a ≠ b ≤ ⌊log₂ N⌋` destroy injectivity. -/
theorem not_fermiScheduleInjective_of_two_missing_levels {N : ℕ} (hN : 1 ≤ N) {S : Set ℕ}
    {a b : ℕ} (hab : a ≠ b) (ha : a ≤ Nat.log 2 N) (hb : b ≤ Nat.log 2 N) (haS : a ∉ S)
    (hbS : b ∉ S) : ¬ FermiScheduleInjective N S := by
  rw [fermiScheduleInjective_iff hN]
  intro h
  exact hab (h a b (by omega) (by omega)
    (by unfold FermiSlotObserved; rw [if_pos ha]; exact haS)
    (by unfold FermiSlotObserved; rw [if_pos hb]; exact hbS))

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
