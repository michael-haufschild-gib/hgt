import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicScheduleInjectivityClassification
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapScheduleTwoChainRayBound
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PrefixStabilityAndCriticalWienerClosureOfMoebiusRows
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PronicEnergyCommutesWithDamping

/-!
# Multi-gap Fermi schedules, `p`-adic valuation traces, and origin–bulk tightness

This module resolves the three structural questions on the Fermi–Nyman reciprocal-cell side:

1. **Multi-gap dyadic Fermi schedules (§1).**
   Under a schedule missing two dyadic levels `1 ≤ g₁ < g₂ ≤ ⌊log₂ N⌋` (`g₁ = h₁ + 1`,
   `g₂ = h₂ + 1`), each odd ray `b` splits into three chains:
   - the bottom chain `[0, h₁]`, pinned at `0` by the observed odd boundary `b`;
   - the interior floating block `[h₁ + 1, h₂]`, unpinned at both gap boundaries;
   - the top chain `[h₂ + 1, ⌊log₂ N⌋ + 1]` with the saturated geometric tail, pinned above by
     horizon saturation.
   The interval power row `fermiIntervalKernelRow L g₁ g₂` is supported on `[1, N]`, has constant
   normalized ray value `1` on `[g₁, g₂)` and `0` outside, and has zero boundary jump at every
   level `k ∉ {g₁, g₂}`. Conversely, any row in the kernel of the two-gap schedule vanishes on
   `[0, h₁]` and `[h₂ + 1, ∞)` along every odd ray and is constant on the floating block
   `[h₁ + 1, h₂]` (`twoGap_ray_profile_of_zero_jumps`). Consequently, the two-gap schedule is
   injective on the anchor-pinned subspace (`y_{h₂}(b) = 0`) and on the block-mean-zero subspace
   (`∑_{k=h₁+1}^{h₂} y_k(b) = 0`), and satisfies the three-chain sine coercivity inequality
   (`floating_block_variance_sine_bound`, `fermiRayTwoGapEnergy_ge`,
   `fermiRaySieveEnergy_anchored_le_twoGap`).

2. **Non-dyadic (`p`-adic) Fermi schedules and weighted ray traces (§2).**
   For every integer base `p ≥ 2`, the `p`-adic Fermi cell matrix
   `pAdicFermiCellMatrix p d n = p ⌊n / (p d)⌋ − ⌊n / d⌋` has cell response
   `pAdicFermiCellResponse p N c n = p ∑_{k=1}^{⌊n/p⌋} s_{N,c}(k) − ∑_{k=1}^n s_{N,c}(k)` and
   inter-cell boundary jump
   `pAdicFermiBoundaryJump p N c n = p · 1_{p ∣ n} · s_{N,c}(n / p) − s_{N,c}(n)`. Along a `p`-adic
   ray `n = p^k b` (`p ∤ b`), level `0` reads `−s_{N,c}(b)`, level `k + 1` reads
   `p s_{N,c}(p^k b) − s_{N,c}(p^{k+1} b)`, and the ray saturates at `L_p = ⌊log_p N⌋`. For every
   prime `p` and `N ≥ 1`, a `p`-adic schedule determines every horizon-`N` row **if and only if**
   it misses at most one of the `⌊log_p N⌋ + 2` slots (`pAdicFermiScheduleInjective_iff`). For
   general positive ray weight profiles `w_k > 0`, the weighted trace energy controls every node by
   the series resistance `∑_{j ≤ k} 1 / w_j` (`sq_le_rayResistance_mul_weightedRayTraceEnergy`) and
   inherits the mixed-chain sine constant above any weight floor (`weighted_mixed_chain_sine_bound`).

3. **Origin and bulk tightness on explicit Fermi–Nyman approximation sequences (§3).**
   At every horizon `N` and cell `n`, `fermiCellResponse N c n` satisfies the exact centered-prefix
   wavelet identity (`fermiCellResponse_eq_weightCenteredPrefix_horizonRow`):
   `fermiCellResponse N c n = 2 A_{row(c,N)}(⌊n/2⌋) − A_{row(c,N)}(n) − (n mod 2) m_c(N)`.
   By the pronic dilation contraction (`pronicNorm_dilate_le` at `p = 2`), the bulk cell norm up to
   `T` is bounded by `(1 + √2) ‖A_{row(c,N)}‖_T + |m_c(N)|` (`pronicNorm_fermiCellResponse_le`),
   and whenever `|A_{row(c,N)}(n)| ≤ B n^γ` (`0 ≤ γ < 1/2`) and `|m_c(N)| ≤ H`, the origin-tail
   window energy `∑_{n = M + 1}^T fermiCellResponse N c n ^ 2 / (n(n + 1))` decays to `0` as
   `M → ∞` **uniformly in both the horizon `N` and the cutoff `T`**
   (`fermiBulk_and_originTail_tight_of_prefix_rpow`). This establishes unconditional uniform bulk
   boundedness and uniform origin-tail tightness for `dampedSignWeight s ε` above half the
   partial-sum exponent (`ε > β / 2`) and for `pmPowerDampedRealWeight ε` above half the zero
   abscissa (`ε > Θ / 2`).
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open _root_.RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Multi-Gap Dyadic Fermi Schedules: Exact Kernel, Subspace Uniqueness, and Three-Chain Ray Coercivity -/

/-- The dyadic power profile supported on the slot interval `[a, b₀)`:
`z(j) = 2^j` for `a ≤ j < b₀`, and `0` otherwise. -/
def fermiIntervalPowerProfile (a b₀ j : ℕ) : ℝ :=
  if a ≤ j ∧ j < b₀ then (2 : ℝ) ^ j else 0

/-- The powers-of-two row synthesizing `fermiIntervalPowerProfile a b₀` at horizon depth `L`. -/
def fermiIntervalKernelRow (L a b₀ : ℕ) : ℕ → ℝ :=
  fermiDyadicPowerRow L (fun j =>
    fermiIntervalPowerProfile a b₀ j - if j = 0 then 0 else fermiIntervalPowerProfile a b₀ (j - 1))

/-- Along any odd ray `b`, the sieve response of `fermiIntervalKernelRow L a b₀` is
`fermiIntervalPowerProfile a b₀ (min k L)`. -/
theorem sieveSeq_fermiIntervalKernelRow {N L : ℕ} (hLN : 2 ^ L ≤ N) (a b₀ : ℕ) {b : ℕ}
    (hb : ¬ 2 ∣ b) (k : ℕ) :
    sieveSeq N (fermiIntervalKernelRow L a b₀) (2 ^ k * b) =
      fermiIntervalPowerProfile a b₀ (min k L) := by
  unfold fermiIntervalKernelRow
  rw [sieveSeq_fermiDyadicPowerRow hLN _ hb k, sum_range_discreteDiff_telescope]

/-- In normalized ray coordinates, `fermiIntervalKernelRow L a b₀` is the exact indicator of the
interval `[a, b₀)` on `k ≤ L`. -/
theorem fermiNormalizedDyadicSieve_fermiIntervalKernelRow {N L : ℕ} (hLN : 2 ^ L ≤ N) (a b₀ : ℕ)
    {b : ℕ} (hb : ¬ 2 ∣ b) {k : ℕ} (hk : k ≤ L) :
    fermiNormalizedDyadicSieve N (fermiIntervalKernelRow L a b₀) b k =
      if a ≤ k ∧ k < b₀ then 1 else 0 := by
  unfold fermiNormalizedDyadicSieve
  rw [sieveSeq_fermiIntervalKernelRow hLN a b₀ hb k, min_eq_left hk]
  unfold fermiIntervalPowerProfile
  split_ifs
  · exact div_self (by positivity)
  · exact zero_div _

/-- For `a < b₀ ≤ L`, `fermiIntervalKernelRow L a b₀` is non-zero at `d = 2^a`. -/
theorem fermiIntervalKernelRow_two_pow_ne_zero {L a b₀ : ℕ} (hab : a < b₀) (haL : a ≤ L) :
    fermiIntervalKernelRow L a b₀ (2 ^ a) ≠ 0 := by
  unfold fermiIntervalKernelRow fermiDyadicPowerRow
  rw [Nat.log_pow (by norm_num), if_pos ⟨rfl, haL⟩]
  dsimp only
  unfold fermiIntervalPowerProfile
  rw [if_pos ⟨le_rfl, hab⟩]
  have hsub : (if a = 0 then (0 : ℝ) else
      if a ≤ a - 1 ∧ a - 1 < b₀ then (2 : ℝ) ^ (a - 1) else 0) = 0 := by
    split_ifs with h0 h1
    · rfl
    · omega
    · rfl
  rw [hsub, sub_zero]
  positivity

/-- Every boundary `n ≥ 1` whose dyadic level `v₂(n)` avoids the two endpoint levels `g₁ < g₂`
(`1 ≤ g₁ < g₂ ≤ ⌊log₂ N⌋`) has zero boundary jump on `fermiIntervalKernelRow (Nat.log 2 N) g₁ g₂`. -/
theorem fermiBoundaryJump_fermiIntervalKernelRow_eq_zero_of_ne {N g₁ g₂ : ℕ}
    (hN : 1 ≤ N) (hg₁ : 1 ≤ g₁) (hgg : g₁ < g₂) (hg₂ : g₂ ≤ Nat.log 2 N)
    {n : ℕ} (hn : 1 ≤ n) (hn₁ : padicValNat 2 n ≠ g₁) (hn₂ : padicValNat 2 n ≠ g₂) :
    fermiBoundaryJump N (fermiIntervalKernelRow (Nat.log 2 N) g₁ g₂) n = 0 := by
  set L := Nat.log 2 N
  have hLN : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨k, b, hb, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
  rw [padicValNat_two_pow_mul_odd hb] at hn₁ hn₂
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, one_mul, fermiBoundaryJump_level_zero N _ hb,
      show b = 2 ^ 0 * b by simp, sieveSeq_fermiIntervalKernelRow hLN g₁ g₂ hb 0]
    unfold fermiIntervalPowerProfile
    rw [if_neg (by omega)]; ring
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [fermiBoundaryJump_level_succ N _ hb k,
      sieveSeq_fermiIntervalKernelRow hLN g₁ g₂ hb k,
      sieveSeq_fermiIntervalKernelRow hLN g₁ g₂ hb (k + 1)]
    by_cases hkL : k + 1 ≤ L
    · rw [min_eq_left (by omega), min_eq_left hkL]
      unfold fermiIntervalPowerProfile
      by_cases hin : g₁ ≤ k ∧ k < g₂
      · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, pow_succ]; ring
      · rw [if_neg hin, if_neg (by omega)]; ring
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
      unfold fermiIntervalPowerProfile
      rw [if_neg (by omega)]; ring

/-- **Exact two-gap ray kernel profile.**
If `c` has zero Fermi boundary jump at every level except `h₁ + 1` and `h₂ + 1`
(`h₁ < h₂ ≤ ⌊log₂ N⌋`), then along every odd ray `b`:
1. `y_k(b) = 0` on the bottom chain `k ≤ h₁`;
2. `y_k(b) = y_{h₂}(b)` is constant on the floating interior block `h₁ + 1 ≤ k ≤ h₂`;
3. `sieveSeq N c (2^k b) = 0` (and hence `y_k(b) = 0`) on the top chain `k ≥ h₂ + 1`. -/
theorem twoGap_ray_profile_of_zero_jumps {N h₁ h₂ : ℕ} (hh : h₁ < h₂) (hh₂ : h₂ ≤ Nat.log 2 N)
    {c : ℕ → ℝ}
    (hread : ∀ n, 1 ≤ n → padicValNat 2 n ≠ h₁ + 1 → padicValNat 2 n ≠ h₂ + 1 →
      fermiBoundaryJump N c n = 0)
    {b : ℕ} (hb : ¬ 2 ∣ b) :
    (∀ k ≤ h₁, fermiNormalizedDyadicSieve N c b k = 0) ∧
    (∀ k, h₁ + 1 ≤ k → k ≤ h₂ →
      fermiNormalizedDyadicSieve N c b k = fermiNormalizedDyadicSieve N c b h₂) ∧
    (∀ k, h₂ + 1 ≤ k → sieveSeq N c (2 ^ k * b) = 0) := by
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hb)
  have hjump_zero : ∀ k, k ≠ h₁ → k ≠ h₂ →
      fermiNormalizedDyadicSieve N c b k = fermiNormalizedDyadicSieve N c b (k + 1) := by
    intro k hk₁ hk₂
    have hn1 : 1 ≤ 2 ^ (k + 1) * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hj := hread (2 ^ (k + 1) * b) hn1
      (by rw [padicValNat_two_pow_mul_odd hb]; omega)
      (by rw [padicValNat_two_pow_mul_odd hb]; omega)
    have hsub := fermiNormalizedDyadicJump_eq_sub N c hb0 k
    unfold fermiNormalizedDyadicJump at hsub
    rw [hj, zero_div] at hsub
    linarith
  have hy0 : fermiNormalizedDyadicSieve N c b 0 = 0 := by
    have hj0 := hread b hb0
      (by rw [padicValNat.eq_zero_of_not_dvd hb]; omega)
      (by rw [padicValNat.eq_zero_of_not_dvd hb]; omega)
    rw [fermiBoundaryJump_level_zero N c hb] at hj0
    unfold fermiNormalizedDyadicSieve
    simp only [pow_zero, one_mul, div_one]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    induction k with
    | zero => exact hy0
    | succ k ih =>
      rw [← hjump_zero k (by omega) (by omega)]
      exact ih (by omega)
  · have hconst : ∀ j, h₁ + 1 + j ≤ h₂ →
        fermiNormalizedDyadicSieve N c b (h₁ + 1 + j) =
          fermiNormalizedDyadicSieve N c b (h₁ + 1) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        rw [show h₁ + 1 + (j + 1) = (h₁ + 1 + j) + 1 by omega,
          ← hjump_zero (h₁ + 1 + j) (by omega) (by omega)]
        exact ih (by omega)
    intro k hk1 hk2
    have h1 := hconst (k - (h₁ + 1)) (by omega)
    have h2 := hconst (h₂ - (h₁ + 1)) (by omega)
    rw [show h₁ + 1 + (k - (h₁ + 1)) = k by omega] at h1
    rw [show h₁ + 1 + (h₂ - (h₁ + 1)) = h₂ by omega] at h2
    exact h1.trans h2.symm
  · set L := Nat.log 2 N
    have hh₂L : h₂ ≤ L := hh₂
    have hh₁L : h₁ < L := lt_of_lt_of_le hh hh₂L
    have htopL : sieveSeq N c (2 ^ L * b) = 0 := by
      have hn1 : 1 ≤ 2 ^ (L + 1 + 1) * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hj := hread (2 ^ (L + 1 + 1) * b) hn1
        (by rw [padicValNat_two_pow_mul_odd hb]; omega)
        (by rw [padicValNat_two_pow_mul_odd hb]; omega)
      rw [fermiBoundaryJump_level_succ N c hb (L + 1),
        sieveSeq_two_pow_mul_saturate N c b (Nat.le_succ L),
        sieveSeq_two_pow_mul_saturate N c b (by omega : L ≤ L + 1 + 1)] at hj
      linarith
    have hdown : ∀ j, j ≤ L - (h₂ + 1) → sieveSeq N c (2 ^ (L - j) * b) = 0 := by
      intro j
      induction j with
      | zero => intro _; simpa using htopL
      | succ j ih =>
        intro hj
        have hlt2 : h₂ + 1 < L - j := by omega
        have hlt1 : h₁ + 1 < L - j := lt_trans (Nat.succ_lt_succ hh) hlt2
        have hn1 : 1 ≤ 2 ^ (L - j) * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hstep := hread (2 ^ (L - j) * b) hn1
          (by rw [padicValNat_two_pow_mul_odd hb]; exact Nat.ne_of_gt hlt1)
          (by rw [padicValNat_two_pow_mul_odd hb]; exact Nat.ne_of_gt hlt2)
        have hsub : L - j = (L - (j + 1)) + 1 := by omega
        rw [hsub, fermiBoundaryJump_level_succ N c hb (L - (j + 1)), ← hsub, ih (by omega)] at hstep
        linarith
    intro k hk
    by_cases hkL : k ≤ L
    · have h := hdown (L - k) (by omega)
      rwa [show L - (L - k) = k by omega] at h
    · rw [sieveSeq_two_pow_mul_saturate N c b (by omega : L ≤ k)]
      exact htopL

/-- **Anchor-pinned uniqueness under a two-gap schedule.**
A two-gap schedule missing levels `h₁ + 1` and `h₂ + 1` (`h₁ < h₂ ≤ ⌊log₂ N⌋`) uniquely determines
every horizon-`N` row whose floating block is anchored (`y_{h₂}(b) = 0` for every odd `b`). -/
theorem twoGap_schedule_injective_on_anchored_rows {N h₁ h₂ : ℕ} (hh : h₁ < h₂)
    (hh₂ : h₂ ≤ Nat.log 2 N) {c : ℕ → ℝ}
    (hread : ∀ n, 1 ≤ n → padicValNat 2 n ≠ h₁ + 1 → padicValNat 2 n ≠ h₂ + 1 →
      fermiBoundaryJump N c n = 0)
    (hanchor : ∀ b, ¬ 2 ∣ b → fermiNormalizedDyadicSieve N c b h₂ = 0) :
    ∀ d ∈ Icc 1 N, c d = 0 := by
  apply eq_zero_of_sieveSeq_initial
  intro n hn
  obtain ⟨k, b, hb, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by have := (mem_Icc.mp hn).1; omega : n ≠ 0) 2 (by norm_num)
  obtain ⟨hbot, hmid, htop⟩ := twoGap_ray_profile_of_zero_jumps hh hh₂ hread hb
  by_cases hk1 : k ≤ h₁
  · have h := hbot k hk1
    unfold fermiNormalizedDyadicSieve at h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · by_cases hk2 : k ≤ h₂
    · have h := (hmid k (by omega) hk2).trans (hanchor b hb)
      unfold fermiNormalizedDyadicSieve at h
      exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
    · exact htop k (by omega)

/-- **Block-mean-zero uniqueness under a two-gap schedule.**
A two-gap schedule missing levels `h₁ + 1` and `h₂ + 1` (`h₁ < h₂ ≤ ⌊log₂ N⌋`) uniquely determines
every horizon-`N` row whose floating block has mean zero
(`∑_{k=h₁+1}^{h₂} y_k(b) = 0` for every odd `b`). -/
theorem twoGap_schedule_injective_on_meanZero_rows {N h₁ h₂ : ℕ} (hh : h₁ < h₂)
    (hh₂ : h₂ ≤ Nat.log 2 N) {c : ℕ → ℝ}
    (hread : ∀ n, 1 ≤ n → padicValNat 2 n ≠ h₁ + 1 → padicValNat 2 n ≠ h₂ + 1 →
      fermiBoundaryJump N c n = 0)
    (hmean : ∀ b, ¬ 2 ∣ b →
      ∑ k ∈ Icc (h₁ + 1) h₂, fermiNormalizedDyadicSieve N c b k = 0) :
    ∀ d ∈ Icc 1 N, c d = 0 := by
  refine twoGap_schedule_injective_on_anchored_rows hh hh₂ hread fun b hb => ?_
  obtain ⟨-, hmid, -⟩ := twoGap_ray_profile_of_zero_jumps hh hh₂ hread hb
  have hsum := hmean b hb
  have hconst : ∑ k ∈ Icc (h₁ + 1) h₂, fermiNormalizedDyadicSieve N c b k =
      ((h₂ - h₁ : ℕ) : ℝ) * fermiNormalizedDyadicSieve N c b h₂ := by
    rw [sum_congr rfl fun k hk => hmid k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2,
      sum_const, Nat.card_Icc, show h₂ + 1 - (h₁ + 1) = h₂ - h₁ by omega, nsmul_eq_mul]
  rw [hconst] at hsum
  have hlen : ((h₂ - h₁ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show h₂ - h₁ ≠ 0 by omega)
  exact (mul_eq_zero.mp hsum).resolve_left hlen

/-- **Least-squares optimality of the arithmetic mean on a finite block.**
For any sequence `x : ℕ → ℝ`, block length `n + 1`, and scalar `c₀ : ℝ`, the variance around the
arithmetic mean `μ = (∑_{k ≤ n} x_k) / (n + 1)` never exceeds `∑_{k ≤ n} (x_k − c₀)²`. -/
theorem sum_range_sq_sub_mean_le (x : ℕ → ℝ) (n : ℕ) (c₀ : ℝ) :
    let μ := (∑ k ∈ range (n + 1), x k) / ((n : ℝ) + 1)
    ∑ k ∈ range (n + 1), (x k - μ) ^ 2 ≤ ∑ k ∈ range (n + 1), (x k - c₀) ^ 2 := by
  intro μ
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsum : ∑ k ∈ range (n + 1), x k = ((n : ℝ) + 1) * μ := by
    dsimp [μ]; field_simp
  have hident : ∑ k ∈ range (n + 1), (x k - c₀) ^ 2 =
      ∑ k ∈ range (n + 1), (x k - μ) ^ 2 + ((n : ℝ) + 1) * (μ - c₀) ^ 2 := by
    have hexp : ∀ k : ℕ, (x k - c₀) ^ 2 =
        (x k - μ) ^ 2 + 2 * (μ - c₀) * x k + (c₀ ^ 2 - μ ^ 2) := fun k => by ring
    simp_rw [hexp, sum_add_distrib, ← mul_sum, hsum, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  rw [hident]
  linarith [mul_nonneg hn1.le (sq_nonneg (μ - c₀))]

/-- **Floating-block least-squares variance sine bound.**
On any interior floating block `a, …, a + n` of a normalized Fermi ray, the variance around the
block mean `μ = (∑_{k ≤ n} y_{a+k}) / (n + 1)` is controlled by the `n` interior boundary jumps
with constant `mixedChainConstant n = 2 − 2 cos(π / (2n + 1))`. -/
theorem floating_block_variance_sine_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) (a n : ℕ) :
    let y := fun k => fermiNormalizedDyadicSieve N c b (a + k)
    let μ := (∑ k ∈ range (n + 1), y k) / ((n : ℝ) + 1)
    mixedChainConstant n * (∑ k ∈ range (n + 1), (y k - μ) ^ 2) ≤
      ∑ k ∈ range n, fermiNormalizedDyadicJump N c b (a + k) ^ 2 := by
  intro y μ
  have hlam : 0 ≤ mixedChainConstant n := (mixedChainConstant_pos n).le
  have hmean := sum_range_sq_sub_mean_le y n (y n)
  have hdrop : ∑ k ∈ range (n + 1), (y k - y n) ^ 2 = ∑ k ∈ range n, (y k - y n) ^ 2 := by
    rw [Finset.sum_range_succ, sub_self, sq, mul_zero, add_zero]
  rw [hdrop] at hmean
  have hsine := fermiNormalizedDyadicSieve_terminal_sine_bound N c hb a n
  have hcast : (((2 * n : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 1 := by push_cast; ring
  unfold mixedChainConstant
  rw [← hcast]
  exact (mul_le_mul_of_nonneg_left hmean (by rw [hcast]; exact hlam)).trans hsine

/-- The two-gap energy of the ray over `b`, omitting dyadic levels `h₁ + 1` and `h₂ + 1`. -/
def fermiRayTwoGapEnergy (N : ℕ) (c : ℕ → ℝ) (b h₁ h₂ : ℕ) : ℝ :=
  fermiRayAllBoundaryEnergy N c b -
    fermiNormalizedDyadicJump N c b h₁ ^ 2 * fermiDyadicPronicWeight (h₁ + 1) b -
    fermiNormalizedDyadicJump N c b h₂ ^ 2 * fermiDyadicPronicWeight (h₂ + 1) b

/-- The **two-gap trace** energy: every reciprocal-cell boundary except those of dyadic levels
`g₁` and `g₂`. -/
def fermiTwoGapPronicEnergy (N : ℕ) (c : ℕ → ℝ) (g₁ g₂ : ℕ) : ℝ :=
  fermiAllBoundaryPronicEnergy N c - fermiLevelPronicEnergy N c g₁ - fermiLevelPronicEnergy N c g₂

/-- **Three-chain boundary decomposition of a two-gap ray.**
For `m ≤ h₁ < h₂ ≤ ⌊log₂ N⌋` (`D = ⌊log₂ N⌋ + 1`), the two-gap ray energy dominates the bottom
chain `[0, h₁]`, the interior floating block `[h₁ + 1, h₂]`, and the top chain `[h₂ + 1, D]`. -/
theorem fermiRayTwoGapEnergy_ge (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) {h₁ h₂ m : ℕ}
    (hmh₁ : m ≤ h₁) (hh : h₁ < h₂) (hh₂L : h₂ ≤ Nat.log 2 N) :
    let y := fun k => fermiNormalizedDyadicSieve N c b k
    let D := Nat.log 2 N + 1
    fermiRayWeightFloor m *
        ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
          ∑ j ∈ range (h₁ - m), (y (m + j) - y (m + j + 1)) ^ 2 +
          ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 +
          (y D ^ 2 / 3 + ∑ k ∈ range (D - h₂ - 1), (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2)) ≤
      (b : ℝ) ^ 2 * fermiRayTwoGapEnergy N c b h₁ h₂ := by
  intro y D
  have hxy (k : ℕ) : fermiNormalizedDyadicJump N c b k = y k - y (k + 1) :=
    fermiNormalizedDyadicJump_eq_sub N c hb k
  set f : ℕ → ℝ := fun k => fermiNormalizedDyadicJump N c b k ^ 2 *
    fermiDyadicPronicWeight (k + 1) b with hf
  set ρ := fermiRayWeightFloor m
  have hρ0 : 0 ≤ ρ := (fermiRayWeightFloor_pos m).le
  have h1gap := fermiRayGapEnergy_ge N c hb hmh₁ (hh.le.trans hh₂L)
  dsimp only at h1gap
  -- Split the top sum `∑ k ∈ range (D - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2`
  -- at the second gap `h₂`
  have hsplit_f : ∑ k ∈ range (D - h₁ - 1), f (h₁ + 1 + k) =
      (∑ k ∈ range (h₂ - h₁ - 1), f (h₁ + 1 + k)) + f h₂ +
        ∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k) := by
    have h1 := sum_range_add (fun k => f (h₁ + 1 + k)) (h₂ - h₁ - 1) (D - h₂)
    rw [show h₂ - h₁ - 1 + (D - h₂) = D - h₁ - 1 by omega] at h1
    have h2 : ∑ j ∈ range (D - h₂), f (h₁ + 1 + (h₂ - h₁ - 1 + j)) =
        f h₂ + ∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k) := by
      rw [show D - h₂ = (D - h₂ - 1) + 1 by omega, sum_range_succ', add_comm]
      congr 1
      · congr 1; omega
      · exact sum_congr rfl fun k _ => by congr 1; omega
    rw [h1, h2]; ring
  -- Re-use the exact decomposition of `fermiRayGapEnergy N c b h₁`
  have hQs := (fermiRay_weighted_summable N c hb).2
  have hsplit := hQs.sum_add_tsum_nat_add D
  have ha1 : (∑ k ∈ range D, f k) = (∑ k ∈ range m, f k) + ∑ j ∈ range (D - m), f (m + j) := by
    have := sum_range_add f m (D - m); rwa [show m + (D - m) = D by omega] at this
  have ha2 : (∑ j ∈ range (D - m), f (m + j)) = (∑ j ∈ range (h₁ - m), f (m + j)) +
      ∑ j ∈ range (D - h₁), f (h₁ + j) := by
    have := sum_range_add (fun j => f (m + j)) (h₁ - m) (D - h₁)
    rw [show h₁ - m + (D - h₁) = D - m by omega] at this
    rw [this]; congr 1; exact sum_congr rfl fun j _ => by congr 1; omega
  have ha3 : (∑ j ∈ range (D - h₁), f (h₁ + j)) =
      f h₁ + ∑ k ∈ range (D - h₁ - 1), f (h₁ + 1 + k) := by
    rw [show D - h₁ = (D - h₁ - 1) + 1 by omega, sum_range_succ', add_comm]
    congr 1
    exact sum_congr rfl fun k _ => by congr 1; omega
  have h2gap : fermiRayTwoGapEnergy N c b h₁ h₂ =
      fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
        ((∑ k ∈ range m, f k) + (∑ j ∈ range (h₁ - m), f (m + j)) +
          (∑ k ∈ range (h₂ - h₁ - 1), f (h₁ + 1 + k)) +
          (∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k)) + ∑' j, f (j + D)) := by
    unfold fermiRayTwoGapEnergy fermiRayAllBoundaryEnergy
    have hfh₁ : fermiNormalizedDyadicJump N c b h₁ ^ 2 * fermiDyadicPronicWeight (h₁ + 1) b = f h₁ := rfl
    have hfh₂ : fermiNormalizedDyadicJump N c b h₂ ^ 2 * fermiDyadicPronicWeight (h₂ + 1) b = f h₂ := rfl
    rw [hfh₁, hfh₂, ← hsplit, ha1, ha2, ha3, hsplit_f]
    ring
  have hw_half (k : ℕ) : (1 / 2 : ℝ) ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b :=
    (half_le_fermiWeightRatio k).trans (fermiDyadicPronicWeight_floor k b hb)
  have hw_ρ (k : ℕ) (hk : m + 1 ≤ k) : ρ ≤ (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b :=
    (fermiWeightRatio_mono hk).trans (fermiDyadicPronicWeight_floor k b hb)
  have hρ1 : ρ ≤ 1 := fermiRayWeightFloor_le_one m
  have hbase : (1 / 2) * y 0 ^ 2 ≤
      (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) := by
    have := hw_half 0
    have e : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 *
        fermiDyadicPronicWeight 0 b) = y 0 ^ 2 * ((b : ℝ) ^ 2 * fermiDyadicPronicWeight 0 b) := by
      simp only [y]; ring
    rw [e]; exact (mul_le_mul_of_nonneg_left this (sq_nonneg _)).trans_eq' (mul_comm _ _)
  have hlow : (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ k ∈ range m, f k := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have e : (b : ℝ) ^ 2 * f k = (y k - y (k + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (k + 1) b) := by
      simp only [hf, hxy k]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_half (k + 1)) (sq_nonneg _)).trans_eq' (mul_comm _ _)
  have hmid1 : ρ * ∑ j ∈ range (h₁ - m), (y (m + j) - y (m + j + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ j ∈ range (h₁ - m), f (m + j) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    have e : (b : ℝ) ^ 2 * f (m + j) = (y (m + j) - y (m + j + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (m + j + 1) b) := by
      simp only [hf, hxy (m + j)]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (m + j + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have hmid2 : ρ * ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ k ∈ range (h₂ - h₁ - 1), f (h₁ + 1 + k) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have e : (b : ℝ) ^ 2 * f (h₁ + 1 + k) = (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (h₁ + 1 + k + 1) b) := by
      simp only [hf, hxy (h₁ + 1 + k)]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (h₁ + 1 + k + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have htopQ : ρ * ∑ k ∈ range (D - h₂ - 1), (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2 ≤
      (b : ℝ) ^ 2 * ∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    have e : (b : ℝ) ^ 2 * f (h₂ + 1 + k) = (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (h₂ + 1 + k + 1) b) := by
      simp only [hf, hxy (h₂ + 1 + k)]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (h₂ + 1 + k + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have htailQ : ρ * (y D ^ 2 / 3) ≤ (b : ℝ) ^ 2 * ∑' j : ℕ, f (j + D) := by
    have ht := fermiRay_jump_tail N c hb
    have hyD : y D ^ 2 / 3 = ∑' j : ℕ, fermiNormalizedDyadicJump N c b (j + D) ^ 2 := ht.symm
    rw [hyD, ← tsum_mul_left, ← tsum_mul_left]
    have hsum1 : Summable (fun j => ρ * fermiNormalizedDyadicJump N c b (j + D) ^ 2) :=
      (((summable_nat_add_iff D).mpr (fermiRay_jump_sq_summable N c hb))).mul_left _
    have hsum2 : Summable (fun j => (b : ℝ) ^ 2 * f (j + D)) :=
      ((summable_nat_add_iff D).mpr hQs).mul_left _
    refine Summable.tsum_le_tsum (fun j => ?_) hsum1 hsum2
    have e : (b : ℝ) ^ 2 * f (j + D) = fermiNormalizedDyadicJump N c b (j + D) ^ 2 *
        ((b : ℝ) ^ 2 * fermiDyadicPronicWeight (j + D + 1) b) := by simp only [hf]; ring
    rw [e]
    exact (mul_le_mul_of_nonneg_left (hw_ρ (j + D + 1) (by omega)) (sq_nonneg _)).trans_eq'
      (mul_comm _ _)
  have hhalf : ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) ≤
      (1 / 2) * y 0 ^ 2 + (1 / 2) * ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
    have h0 : 0 ≤ (1 / 2 : ℝ) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))
    calc ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) ≤
        1 * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_right hρ1 h0
      _ = _ := by ring
  rw [h2gap]
  have hL : ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
        ∑ j ∈ range (h₁ - m), (y (m + j) - y (m + j + 1)) ^ 2 +
        ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 +
        (y D ^ 2 / 3 + ∑ k ∈ range (D - h₂ - 1), (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2)) =
      ρ * ((1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2)) +
        ρ * ∑ j ∈ range (h₁ - m), (y (m + j) - y (m + j + 1)) ^ 2 +
        ρ * ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 +
        ρ * (y D ^ 2 / 3) +
        ρ * ∑ k ∈ range (D - h₂ - 1), (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2 := by ring
  have hR : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
        ((∑ k ∈ range m, f k) + (∑ j ∈ range (h₁ - m), f (m + j)) +
          (∑ k ∈ range (h₂ - h₁ - 1), f (h₁ + 1 + k)) +
          (∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k)) + ∑' j, f (j + D))) =
      (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) +
        (b : ℝ) ^ 2 * (∑ k ∈ range m, f k) +
        (b : ℝ) ^ 2 * (∑ j ∈ range (h₁ - m), f (m + j)) +
        (b : ℝ) ^ 2 * (∑ k ∈ range (h₂ - h₁ - 1), f (h₁ + 1 + k)) +
        (b : ℝ) ^ 2 * (∑ k ∈ range (D - h₂ - 1), f (h₂ + 1 + k)) +
        (b : ℝ) ^ 2 * ∑' j, f (j + D) := by ring
  rw [hL, hR]
  linarith

/-- **Three-chain ray inequality on anchored rows (`fermiRaySieveEnergy_anchored_le_twoGap`).**
With two gaps at levels `h₁ + 1` and `h₂ + 1` (`m ≤ h₁ < h₂ ≤ ⌊log₂ N⌋`), whenever the floating
block is anchored at `y_{h₂}(b) = 0`, the ray sieve energy is controlled by the two-gap ray energy
with constant `1 / (ρ_m min(λ_{h₁+m+2}, λ_{h₂-h₁-1}, λ_{⌊log₂ N⌋-h₂+3}))`. -/
theorem fermiRaySieveEnergy_anchored_le_twoGap (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    {h₁ h₂ m : ℕ} (hmh₁ : m ≤ h₁) (hh : h₁ < h₂) (hh₂L : h₂ ≤ Nat.log 2 N)
    (hanchor : fermiNormalizedDyadicSieve N c b h₂ = 0) :
    fermiRaySieveEnergy N c b ≤
      1 / (fermiRayWeightFloor m *
        min (mixedChainConstant (h₁ + m + 2))
          (min (mixedChainConstant (h₂ - h₁ - 1))
            (mixedChainConstant (Nat.log 2 N - h₂ + 3)))) *
        fermiRayTwoGapEnergy N c b h₁ h₂ := by
  set y : ℕ → ℝ := fun k => fermiNormalizedDyadicSieve N c b k with hy
  set D := Nat.log 2 N + 1 with hD
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hρ := fermiRayWeightFloor_pos m
  set lb := mixedChainConstant (h₁ + m + 2)
  set lm := mixedChainConstant (h₂ - h₁ - 1)
  set lt := mixedChainConstant (Nat.log 2 N - h₂ + 3)
  have hlb := mixedChainConstant_pos (h₁ + m + 2)
  have hlm := mixedChainConstant_pos (h₂ - h₁ - 1)
  have hlt := mixedChainConstant_pos (Nat.log 2 N - h₂ + 3)
  set lam := min lb (min lm lt)
  have hlam : 0 < lam := lt_min hlb (lt_min hlm hlt)
  have hlam_lb : lam ≤ lb := min_le_left _ _
  have hlam_lm : lam ≤ lm := (min_le_right _ _).trans (min_le_left _ _)
  have hlam_lt : lam ≤ lt := (min_le_right _ _).trans (min_le_right _ _)
  have hP := fermiRaySieveEnergy_sq_mul_le N c hb
  have hbot := gap_bottom_chain_bound y hmh₁
  have htop := gap_top_chain_bound y (show h₂ + 1 ≤ D by omega)
  rw [show D - h₂ + 2 = Nat.log 2 N - h₂ + 3 by omega] at htop
  have hmid_sine := fermiNormalizedDyadicSieve_terminal_sine_bound N c hb (h₁ + 1) (h₂ - h₁ - 1)
  have hmid : lm * (∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2) ≤
      ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 := by
    have hsplit_m : ∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2 =
        ∑ k ∈ range (h₂ - h₁ - 1),
          (fermiNormalizedDyadicSieve N c b (h₁ + 1 + k) -
            fermiNormalizedDyadicSieve N c b (h₁ + 1 + (h₂ - h₁ - 1))) ^ 2 := by
      have hend : h₁ + 1 + (h₂ - h₁ - 1) = h₂ := by omega
      conv_lhs => rw [show h₂ - h₁ = (h₂ - h₁ - 1) + 1 by omega, Finset.sum_range_succ]
      dsimp only [y]
      rw [hend, hanchor]
      simp only [sub_zero]
      ring
    have hjump_m : ∑ k ∈ range (h₂ - h₁ - 1),
        fermiNormalizedDyadicJump N c b (h₁ + 1 + k) ^ 2 =
        ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2 := by
      refine sum_congr rfl fun k _ => ?_
      rw [fermiNormalizedDyadicJump_eq_sub N c hb]
    have hcast : (((2 * (h₂ - h₁ - 1) : ℕ) : ℝ) + 1) =
        2 * ((h₂ - h₁ - 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hsplit_m, ← hjump_m]
    dsimp [lm, mixedChainConstant]
    rw [← hcast]
    exact hmid_sine
  have hQ := fermiRayTwoGapEnergy_ge N c hb hmh₁ hh hh₂L
  simp only at hQ
  set Eb := (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
    ∑ j ∈ range (h₁ - m), (y (m + j) - y (m + j + 1)) ^ 2
  set Em := ∑ k ∈ range (h₂ - h₁ - 1), (y (h₁ + 1 + k) - y (h₁ + 1 + k + 1)) ^ 2
  set Et := y D ^ 2 / 3 + ∑ k ∈ range (D - h₂ - 1), (y (h₂ + 1 + k) - y (h₂ + 1 + k + 1)) ^ 2
  have hsplitY : (∑ k ∈ range (D + 1), y k ^ 2) =
      (∑ k ∈ range (h₁ + 1), y k ^ 2) +
      (∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2) +
      ∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2 := by
    have s1 := sum_range_add (fun k => y k ^ 2) (h₁ + 1) (D - h₁)
    rw [show h₁ + 1 + (D - h₁) = D + 1 by omega] at s1
    have s2 := sum_range_add (fun k => y (h₁ + 1 + k) ^ 2) (h₂ - h₁) (D - h₂)
    rw [show h₂ - h₁ + (D - h₂) = D - h₁ by omega] at s2
    have s3 : ∑ x ∈ range (D - h₂), y (h₁ + 1 + (h₂ - h₁ + x)) ^ 2 =
        ∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2 :=
      sum_congr rfl fun k _ => by congr 2; omega
    rw [s1, s2, s3, add_assoc]
  have hbot' : (∑ k ∈ range (h₁ + 1), y k ^ 2) ≤ Eb / lam := by
    rw [le_div_iff₀ hlam]
    have : lam * (∑ k ∈ range (h₁ + 1), y k ^ 2) ≤ lb * (∑ k ∈ range (h₁ + 1), y k ^ 2) :=
      mul_le_mul_of_nonneg_right hlam_lb (sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  have hmid' : (∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2) ≤ Em / lam := by
    rw [le_div_iff₀ hlam]
    have : lam * (∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2) ≤
        lm * (∑ k ∈ range (h₂ - h₁), y (h₁ + 1 + k) ^ 2) :=
      mul_le_mul_of_nonneg_right hlam_lm (sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  have htop' : (∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2) + y D ^ 2 / 3 ≤ Et / lam := by
    rw [le_div_iff₀ hlam]
    have h59 : (∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2) + y D ^ 2 / 3 ≤
        5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2 := by
      linarith [sq_nonneg (y D)]
    have h1 := mul_le_mul_of_nonneg_left h59 hlam.le
    have h2 : lam * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2) ≤
        lt * (5 / 9 * y D ^ 2 + ∑ k ∈ range (D - h₂), y (h₂ + 1 + k) ^ 2) :=
      mul_le_mul_of_nonneg_right hlam_lt
        (add_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _))
    linarith
  have hcomb : (b : ℝ) ^ 2 * fermiRaySieveEnergy N c b ≤ (Eb + Em + Et) / lam := by
    have : (∑ k ∈ range (D + 1), y k ^ 2) + y D ^ 2 / 3 ≤ Eb / lam + Em / lam + Et / lam := by
      rw [hsplitY]; linarith
    have hd : Eb / lam + Em / lam + Et / lam = (Eb + Em + Et) / lam := by ring
    linarith
  have hQ' : (Eb + Em + Et) / lam ≤
      (b : ℝ) ^ 2 * (1 / (fermiRayWeightFloor m * lam) * fermiRayTwoGapEnergy N c b h₁ h₂) := by
    rw [div_le_iff₀ hlam]
    have e : (b : ℝ) ^ 2 * (1 / (fermiRayWeightFloor m * lam) * fermiRayTwoGapEnergy N c b h₁ h₂) * lam =
        (b : ℝ) ^ 2 * fermiRayTwoGapEnergy N c b h₁ h₂ / fermiRayWeightFloor m := by
      field_simp
    rw [e, le_div_iff₀ hρ]
    linarith
  exact le_of_mul_le_mul_left (hcomb.trans hQ') hb2

/-! ## §2. Non-Dyadic (`p`-adic) Fermi Schedules and Weighted Ray Traces -/

/-- The `p`-adic Fermi cell matrix `p ⌊n / (p d)⌋ − ⌊n / d⌋`. At `p = 2` this is `fermiCellMatrix`. -/
def pAdicFermiCellMatrix (p d n : ℕ) : ℝ :=
  (p : ℝ) * ((n / (p * d) : ℕ) : ℝ) - ((n / d : ℕ) : ℝ)

/-- The `p`-adic cellular Fermi–Nyman response of a weight `c` at horizon `N` on cell `n`. -/
def pAdicFermiCellResponse (p N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, c d * pAdicFermiCellMatrix p d n

/-- The `p`-adic Fermi boundary jump at cell boundary `n`:
`p · 1_{p ∣ n} · s_{N,c}(n / p) − s_{N,c}(n)`. -/
def pAdicFermiBoundaryJump (p N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  (if p ∣ n then (p : ℝ) * sieveSeq N c (n / p) else 0) - sieveSeq N c n

/-- At `p = 2`, `pAdicFermiCellMatrix 2` is the dyadic `fermiCellMatrix`. -/
theorem pAdicFermiCellMatrix_two (d n : ℕ) :
    pAdicFermiCellMatrix 2 d n = fermiCellMatrix d n := by
  unfold pAdicFermiCellMatrix fermiCellMatrix; norm_num

/-- **Exact `p`-adic Prefix Decomposition of `pAdicFermiCellResponse`:**
`pAdicFermiCellResponse p N c n = p ∑_{k=1}^{⌊n/p⌋} s_{N,c}(k) − ∑_{k=1}^n s_{N,c}(k)`. -/
theorem pAdicFermiCellResponse_eq_prefix_div_sub_prefix (p N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    pAdicFermiCellResponse p N c n =
      (p : ℝ) * (∑ k ∈ Icc 1 (n / p), sieveSeq N c k) -
        ∑ k ∈ Icc 1 n, sieveSeq N c k := by
  unfold pAdicFermiCellResponse pAdicFermiCellMatrix
  have hdiv : ∀ d : ℕ, n / (p * d) = (n / p) / d :=
    fun d => (Nat.div_div_eq_div_mul n p d).symm
  simp_rw [hdiv, mul_sub, ← mul_assoc]
  rw [sum_sub_distrib, ← sum_mul_nat_div_eq_sum_sieveSeq N n c,
    ← sum_mul_nat_div_eq_sum_sieveSeq N (n / p) c, mul_sum]
  refine congrArg (· - _) (sum_congr rfl fun d _ => by ring)

/-- For `p ≥ 1`, `(n + 1) / p = n / p + (if p ∣ (n + 1) then 1 else 0)`. -/
theorem succ_div_eq_add_ite {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (n + 1) / p = n / p + if p ∣ (n + 1) then 1 else 0 := by
  by_cases h : p ∣ (n + 1)
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp at hk
      · exact hk0
    have hn : n = p * (k - 1) + (p - 1) := by
      have : p * k = p * (k - 1) + p := by
         conv_lhs => rw [← Nat.sub_add_cancel hk1, Nat.mul_add, Nat.mul_one]
      omega
    have h1 : (n + 1) / p = k := by rw [hk, Nat.mul_div_right k (by omega)]
    have h2 : n / p = k - 1 := by
      rw [hn, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (by omega : p - 1 < p), zero_add]
    omega
  · rw [if_neg h, add_zero]
    have hmod : (n + 1) % p ≠ 0 := fun hm => h (Nat.dvd_of_mod_eq_zero hm)
    have hdiv := (Nat.div_add_mod (n + 1) p).symm
    have hn : n = p * ((n + 1) / p) + ((n + 1) % p - 1) := by omega
    have hlt : (n + 1) % p - 1 < p := by
      have := Nat.mod_lt (n + 1) (show 0 < p by omega)
      omega
    conv_rhs => rw [hn, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hlt, zero_add]

/-- **Exact Inter-Cell Jump Reciprocity for `pAdicFermiCellResponse`:**
For `p ≥ 1`, stepping from cell `n` to `n + 1` changes `pAdicFermiCellResponse p N c` by
`pAdicFermiBoundaryJump p N c (n + 1)`. -/
theorem pAdicFermiCellResponse_succ_sub_eq {p : ℕ} (hp : 1 ≤ p) (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    pAdicFermiCellResponse p N c (n + 1) - pAdicFermiCellResponse p N c n =
      pAdicFermiBoundaryJump p N c (n + 1) := by
  rw [pAdicFermiCellResponse_eq_prefix_div_sub_prefix p N c (n + 1),
    pAdicFermiCellResponse_eq_prefix_div_sub_prefix p N c n]
  unfold pAdicFermiBoundaryJump
  have hIcc_full : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
    ext k; simp only [mem_Icc, mem_insert]; omega
  have hnot_full : n + 1 ∉ Icc 1 n := by simp only [mem_Icc]; omega
  rw [hIcc_full, sum_insert hnot_full]
  have hstep := succ_div_eq_add_ite hp n
  by_cases hpd : p ∣ (n + 1)
  · rw [if_pos hpd] at hstep ⊢
    have hnp : 0 ≤ n / p := Nat.zero_le _
    have h1 : 1 ≤ (n + 1) / p := by
      rw [hstep]; omega
    have hIcc_p : Icc 1 ((n + 1) / p) = insert ((n + 1) / p) (Icc 1 (n / p)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    have hnot_p : (n + 1) / p ∉ Icc 1 (n / p) := by
      simp only [mem_Icc]; omega
    rw [hIcc_p, sum_insert hnot_p]
    ring
  · rw [if_neg hpd] at hstep ⊢
    rw [add_zero] at hstep
    rw [hstep]
    ring

/-- The level-`0` boundary of a `p`-adic ray (`p ∤ b`) reads `-sieveSeq N c b`. -/
theorem pAdicFermiBoundaryJump_level_zero (p N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : ¬ p ∣ b) :
    pAdicFermiBoundaryJump p N c b = -sieveSeq N c b := by
  unfold pAdicFermiBoundaryJump
  rw [if_neg hb, zero_sub]

/-- The level-`k+1` boundary of a `p`-adic ray reads `p s_{N,c}(p^k b) − s_{N,c}(p^{k+1} b)`. -/
theorem pAdicFermiBoundaryJump_level_succ {p : ℕ} (hp : 1 ≤ p) (N : ℕ) (c : ℕ → ℝ) (b k : ℕ) :
    pAdicFermiBoundaryJump p N c (p ^ (k + 1) * b) =
      (p : ℝ) * sieveSeq N c (p ^ k * b) - sieveSeq N c (p ^ (k + 1) * b) := by
  unfold pAdicFermiBoundaryJump
  have hdvd : p ∣ p ^ (k + 1) * b := by
    rw [pow_succ', Nat.mul_assoc]; exact dvd_mul_right p (p ^ k * b)
  have hdiv : p ^ (k + 1) * b / p = p ^ k * b := by
    rw [pow_succ', Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
  rw [if_pos hdvd, hdiv]

/-- The `p`-adic valuation of `p ^ k * b` when `p` is prime and `p ∤ b` is `k`. -/
theorem padicValNat_prime_pow_mul {p : ℕ} (hp : Nat.Prime p) {b : ℕ} (hb : ¬ p ∣ b) (k : ℕ) :
    padicValNat p (p ^ k * b) = k := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [padicValNat.mul (pow_ne_zero k hp.ne_zero) hb0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hb, add_zero]

private theorem prime_pow_dvd_prime_pow_mul_iff {p : ℕ} (hp : Nat.Prime p) {b : ℕ} (hb : ¬ p ∣ b)
    (j k : ℕ) : p ^ j ∣ p ^ k * b ↔ j ≤ k := by
  have hcop : Nat.Coprime (p ^ j) b :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb)
  rw [hcop.dvd_mul_right, Nat.pow_dvd_pow_iff_le_right hp.one_lt]

/-- **`p`-adic Saturation.** Above level `⌊log_p N⌋`, a `p`-adic ray is constant. -/
theorem sieveSeq_prime_pow_mul_saturate {p : ℕ} (hp : Nat.Prime p) (N : ℕ) (c : ℕ → ℝ) (b : ℕ)
    {k : ℕ} (hk : Nat.log p N ≤ k) :
    sieveSeq N c (p ^ k * b) = sieveSeq N c (p ^ Nat.log p N * b) := by
  unfold sieveSeq
  refine sum_congr (filter_congr fun d hd => ?_) fun _ _ => rfl
  have hdN := (mem_Icc.mp hd).2
  constructor
  · intro h
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp h
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp h₁
    have hd2 : 0 < d₂ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hd
    have hiL : i ≤ Nat.log p N := by
      have hpi : p ^ i ≤ N := le_trans (Nat.le_mul_of_pos_right _ hd2) hdN
      exact Nat.le_log_of_pow_le hp.one_lt hpi
    exact mul_dvd_mul (Nat.pow_dvd_pow p hiL) h₂
  · intro h
    exact h.trans (mul_dvd_mul_right (Nat.pow_dvd_pow p hk) b)

/-- A `p`-adic schedule `S ⊆ ℕ` reading `pAdicFermiBoundaryJump p N c n` at `v_p(n) ∈ S`
is injective if it uniquely determines every row on `[1, N]`. -/
def PAdicFermiScheduleInjective (p N : ℕ) (S : Set ℕ) : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, 1 ≤ n → padicValNat p n ∈ S → pAdicFermiBoundaryJump p N c n = 0) →
    ∀ d ∈ Icc 1 N, c d = 0

/-- Slot `k ≤ log_p N` is level `k`; slot `log_p N + 1` is observed when some level above
`log_p N` is in `S`. -/
def PAdicFermiSlotObserved (p N : ℕ) (S : Set ℕ) (k : ℕ) : Prop :=
  if k ≤ Nat.log p N then k ∈ S else ∃ j, Nat.log p N + 1 ≤ j ∧ j ∈ S

/-- A chain with relations `z_0 = 0`, `z_k = p z_{k-1}` (`1 ≤ k ≤ L`) and `z_L = 0` (`p ≥ 1`),
of which at most one is missing, vanishes on `[0, L]`. -/
private theorem pAdic_pinned_chain_vanish {p L : ℕ} (hp : 1 ≤ p) (z : ℕ → ℝ) (obs : ℕ → Prop)
    (huniq : ∀ a b, a ≤ L + 1 → b ≤ L + 1 → ¬ obs a → ¬ obs b → a = b)
    (h0 : obs 0 → z 0 = 0) (hk : ∀ k, 1 ≤ k → k ≤ L → obs k → z k = (p : ℝ) * z (k - 1))
    (htop : obs (L + 1) → z L = 0) : ∀ k ≤ L, z k = 0 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  by_cases hall : ∀ k ≤ L, obs k
  · intro k hkL
    induction k with
    | zero => exact h0 (hall 0 (Nat.zero_le _))
    | succ k ih =>
      rw [hk (k + 1) (by omega) hkL (hall _ hkL), Nat.add_sub_cancel, ih (by omega), mul_zero]
  push Not at hall
  obtain ⟨a, haL, ha⟩ := hall
  have hother : ∀ k ≤ L + 1, k ≠ a → obs k := fun k hk hne => by
    by_contra h; exact hne (huniq k a hk (by omega) h ha)
  have hzL : z L = 0 := htop (hother (L + 1) le_rfl (by omega))
  have hlow : ∀ k < a, z k = 0 := by
    intro k hka
    induction k with
    | zero => exact h0 (hother 0 (by omega) (by omega))
    | succ k ih =>
      rw [hk (k + 1) (by omega) (by omega) (hother _ (by omega) (by omega)),
        Nat.add_sub_cancel, ih (by omega), mul_zero]
  have hhigh : ∀ j, a + j ≤ L → z (L - j) = 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using hzL
    | succ j ih =>
      intro hj
      have h := hk (L - j) (by omega) (by omega) (hother _ (by omega) (by omega))
      rw [ih (by omega), show L - j - 1 = L - (j + 1) by omega] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hp0
  intro k hkL
  by_cases hka : k < a
  · exact hlow k hka
  · have := hhigh (L - k) (by omega); rwa [show L - (L - k) = k by omega] at this

/-- The powers-of-`p` row `c(p^j) = g(j)` for `j ≤ L`, zero elsewhere. -/
def pAdicFermiPowerRow (p L : ℕ) (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d = p ^ Nat.log p d ∧ Nat.log p d ≤ L then g (Nat.log p d) else 0

/-- The response of `pAdicFermiPowerRow p L g` along a `p`-adic ray `p^k b` (`p ∤ b`) is the
prefix sum `∑_{j ≤ min(k, L)} g(j)`. -/
theorem sieveSeq_pAdicFermiPowerRow {p N L : ℕ} (hp : Nat.Prime p) (hLN : p ^ L ≤ N) (g : ℕ → ℝ)
    {b : ℕ} (hb : ¬ p ∣ b) (k : ℕ) :
    sieveSeq N (pAdicFermiPowerRow p L g) (p ^ k * b) = ∑ j ∈ range (min k L + 1), g j := by
  unfold sieveSeq
  have himg : (range (min k L + 1)).image (fun j => p ^ j) ⊆
      (Icc 1 N).filter (fun d => d ∣ p ^ k * b) := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    have hjm := mem_range.mp hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_pow j p hp.pos, ?_⟩,
      (prime_pow_dvd_prime_pow_mul_iff hp hb j k).mpr (by omega)⟩
    exact le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hLN
  rw [← sum_subset himg ?_, sum_image fun i _ j _ h => Nat.pow_right_injective hp.two_le h]
  · refine sum_congr rfl fun j hj => ?_
    have hjm := mem_range.mp hj
    unfold pAdicFermiPowerRow
    rw [Nat.log_pow hp.one_lt, if_pos ⟨rfl, by omega⟩]
  · intro d hd hnot
    unfold pAdicFermiPowerRow
    rw [if_neg]
    rintro ⟨hdp, hdL⟩
    apply hnot
    obtain ⟨-, hdvd⟩ := mem_filter.mp hd
    rw [hdp] at hdvd ⊢
    exact mem_image.mpr ⟨Nat.log p d, mem_range.mpr (by
      have := (prime_pow_dvd_prime_pow_mul_iff hp hb _ k).mp hdvd; omega), rfl⟩

/-- **`p`-adic Fermi schedule injectivity classification.**
For every prime `p` and `N ≥ 1`, a `p`-adic schedule determines every horizon-`N` row if and only
if it misses at most one of the `⌊log_p N⌋ + 2` slots `0, …, ⌊log_p N⌋ + 1`. -/
theorem pAdicFermiScheduleInjective_iff {p N : ℕ} (hp : Nat.Prime p) (hN : 1 ≤ N) (S : Set ℕ) :
    PAdicFermiScheduleInjective p N S ↔
      ∀ a b, a ≤ Nat.log p N + 1 → b ≤ Nat.log p N + 1 →
        ¬ PAdicFermiSlotObserved p N S a → ¬ PAdicFermiSlotObserved p N S b → a = b := by
  set L := Nat.log p N
  have hLN : p ^ L ≤ N := Nat.pow_log_le_self p (by omega)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  constructor
  · intro hinj
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, b₀, ha₀, hb₀, hna₀, hnb₀, hne⟩ := hcon
    wlog hab : a₀ < b₀ generalizing a₀ b₀
    · exact this b₀ a₀ hb₀ ha₀ hnb₀ hna₀ hne.symm (by omega)
    set z : ℕ → ℝ := fun j => if a₀ ≤ j ∧ j < b₀ then (p : ℝ) ^ j else 0
    set g : ℕ → ℝ := fun j => z j - if j = 0 then 0 else z (j - 1)
    have hs : ∀ b, ¬ p ∣ b → ∀ k,
        sieveSeq N (pAdicFermiPowerRow p L g) (p ^ k * b) = z (min k L) := by
      intro b hb k
      rw [sieveSeq_pAdicFermiPowerRow hp hLN g hb k, sum_range_discreteDiff_telescope]
    have hread : ∀ n, 1 ≤ n → padicValNat p n ∈ S →
        pAdicFermiBoundaryJump p N (pAdicFermiPowerRow p L g) n = 0 := by
      intro n hn hS
      obtain ⟨k, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
      rw [padicValNat_prime_pow_mul hp hb] at hS
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have hobs : PAdicFermiSlotObserved p N S 0 := by
          unfold PAdicFermiSlotObserved; rw [if_pos (Nat.zero_le _)]; exact hS
        have ha1 : a₀ ≠ 0 := fun h => hna₀ (h ▸ hobs)
        rw [pow_zero, one_mul, pAdicFermiBoundaryJump_level_zero p N _ hb,
          show b = p ^ 0 * b by simp, hs b hb 0]
        simp [z]; omega
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [pAdicFermiBoundaryJump_level_succ hp1 N _ b k, hs b hb k, hs b hb (k + 1)]
      by_cases hkL : k + 1 ≤ L
      · have hobs : PAdicFermiSlotObserved p N S (k + 1) := by
          unfold PAdicFermiSlotObserved; rw [if_pos hkL]; exact hS
        have h1 : k + 1 ≠ a₀ := fun h => hna₀ (h ▸ hobs)
        have h2 : k + 1 ≠ b₀ := fun h => hnb₀ (h ▸ hobs)
        rw [min_eq_left (by omega), min_eq_left hkL]
        simp only [z]
        by_cases hin : a₀ ≤ k ∧ k < b₀
        · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, pow_succ]; ring
        · rw [if_neg hin, if_neg (by omega)]; ring
      · have hobs : PAdicFermiSlotObserved p N S (L + 1) := by
          unfold PAdicFermiSlotObserved; rw [if_neg (by omega)]; exact ⟨k + 1, by omega, hS⟩
        have hb1 : b₀ ≠ L + 1 := fun h => hnb₀ (h ▸ hobs)
        rw [min_eq_right (by omega), min_eq_right (by omega)]
        simp only [z]
        rw [if_neg (by omega)]; ring
    have h := hinj _ hread (p ^ a₀) (mem_Icc.mpr ⟨Nat.one_le_pow a₀ p hp.pos,
      le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hLN⟩)
    unfold pAdicFermiPowerRow at h
    rw [Nat.log_pow hp.one_lt, if_pos ⟨rfl, by omega⟩] at h
    simp only [g, z] at h
    rw [if_pos ⟨le_rfl, hab⟩] at h
    have hpa : (0 : ℝ) < (p : ℝ) ^ a₀ := by positivity
    split_ifs at h with h0 h1
    · linarith
    · omega
    · linarith
  · intro huniq c hread
    have hray : ∀ b, ¬ p ∣ b → ∀ k ≤ L, sieveSeq N c (p ^ k * b) = 0 := by
      intro b hb
      have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hb)
      refine pAdic_pinned_chain_vanish hp1 (L := L) (fun k => sieveSeq N c (p ^ k * b))
        (PAdicFermiSlotObserved p N S) huniq ?_ ?_ ?_
      · intro hobs
        unfold PAdicFermiSlotObserved at hobs; rw [if_pos (Nat.zero_le _)] at hobs
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        have h := hread b hb1 (by rw [padicValNat.eq_zero_of_not_dvd hb]; exact hobs)
        rw [pAdicFermiBoundaryJump_level_zero p N c hb] at h
        simp only [pow_zero, one_mul]; linarith
      · intro k hk1 hkL hobs
        unfold PAdicFermiSlotObserved at hobs; rw [if_pos hkL] at hobs
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have h := hread (p ^ (k + 1) * b)
          (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)))
          (by rw [padicValNat_prime_pow_mul hp hb]; exact hobs)
        rw [pAdicFermiBoundaryJump_level_succ hp1 N c b k] at h
        simp only [Nat.add_sub_cancel]; linarith
      · intro hobs
        unfold PAdicFermiSlotObserved at hobs; rw [if_neg (by omega)] at hobs
        obtain ⟨j, hj, hjS⟩ := hobs
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have h := hread (p ^ (j + 1) * b)
          (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)))
          (by rw [padicValNat_prime_pow_mul hp hb]; exact hjS)
        rw [pAdicFermiBoundaryJump_level_succ hp1 N c b j,
          sieveSeq_prime_pow_mul_saturate hp N c b (by omega : L ≤ j),
          sieveSeq_prime_pow_mul_saturate hp N c b (by omega : L ≤ j + 1)] at h
        have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        nlinarith
    apply eq_zero_of_sieveSeq_initial
    intro n hn
    obtain ⟨k, b, hb, rfl⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by have := (mem_Icc.mp hn).1; omega : n ≠ 0) p hp.ne_one
    by_cases hkL : k ≤ L
    · exact hray b hb k hkL
    · rw [sieveSeq_prime_pow_mul_saturate hp N c b (by omega : L ≤ k)]
      exact hray b hb L le_rfl

/-- Every one-gap `p`-adic schedule `{k | k ≠ g}` (`g ≥ 0`) is injective for every prime `p`. -/
theorem pAdicFermiScheduleInjective_oneGap {p N : ℕ} (hp : Nat.Prime p) (hN : 1 ≤ N) (g : ℕ) :
    PAdicFermiScheduleInjective p N {k | k ≠ g} := by
  rw [pAdicFermiScheduleInjective_iff hp hN]
  intro a b ha hb hna hnb
  unfold PAdicFermiSlotObserved at hna hnb
  split_ifs at hna hnb with h1 h2 h2
  · simp only [Set.mem_setOf_eq, not_not] at hna hnb; omega
  · exact absurd ⟨max (Nat.log p N + 1) (g + 1), le_max_left _ _,
      by simp only [Set.mem_setOf_eq]; omega⟩ hnb
  · exact absurd ⟨max (Nat.log p N + 1) (g + 1), le_max_left _ _,
      by simp only [Set.mem_setOf_eq]; omega⟩ hna
  · exact absurd ⟨max (Nat.log p N + 1) (g + 1), le_max_left _ _,
      by simp only [Set.mem_setOf_eq]; omega⟩ hna

/-- The weighted ray trace energy `w_0 y_0² + ∑_{k < n} w_{k+1} (y_k − y_{k+1})²` on a finite
chain of length `n`. -/
def weightedRayTraceEnergy (w y : ℕ → ℝ) (n : ℕ) : ℝ :=
  w 0 * y 0 ^ 2 + ∑ k ∈ range n, w (k + 1) * (y k - y (k + 1)) ^ 2

/-- The series resistance `∑_{j ≤ k} 1 / w_j` along a weighted ray up to node `k`. -/
def rayResistance (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), 1 / w j

/-- **Exact Cauchy–Schwarz Resistance Inequality for Weighted Ray Traces.**
For any positive ray weights `w_j > 0` (`j ≤ k ≤ n`), the square value at node `k` is bounded by
the series resistance `∑_{j ≤ k} 1 / w_j` times the weighted ray trace energy. -/
theorem sq_le_rayResistance_mul_weightedRayTraceEnergy {w : ℕ → ℝ} (y : ℕ → ℝ) {k n : ℕ}
    (hkn : k ≤ n) (hw : ∀ j ≤ n, 0 < w j) :
    y k ^ 2 ≤ rayResistance w k * weightedRayTraceEnergy w y n := by
  set d : ℕ → ℝ := fun j => if j = 0 then y 0 else y j - y (j - 1)
  have htel : ∑ j ∈ range (k + 1), d j = y k := by
    clear hkn
    induction k with
    | zero => simp [d]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp [d]
  set u : ℕ → ℝ := fun j => Real.sqrt (w j) * d j
  set v : ℕ → ℝ := fun j => 1 / Real.sqrt (w j)
  have huv : ∑ j ∈ range (k + 1), u j * v j = y k := by
    rw [← htel]
    refine sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ n := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hkn
    have hpos : Real.sqrt (w j) ≠ 0 := (Real.sqrt_pos.mpr (hw j hj_le)).ne'
    simp only [u, v]
    field_simp
  have hu2 : ∑ j ∈ range (k + 1), u j ^ 2 ≤ weightedRayTraceEnergy w y n := by
    have hsplit : ∑ j ∈ range (k + 1), u j ^ 2 =
        w 0 * y 0 ^ 2 + ∑ j ∈ range k, w (j + 1) * (y j - y (j + 1)) ^ 2 := by
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      · simp only [u, d, ite_true]
        rw [mul_pow, Real.sq_sqrt (hw 0 (Nat.zero_le _)).le]
      · refine sum_congr rfl fun j hj => ?_
        have hj_le : j + 1 ≤ n := by have := mem_range.mp hj; omega
        simp only [u, d, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
        rw [mul_pow, Real.sq_sqrt (hw (j + 1) hj_le).le]
        ring
    rw [hsplit]
    unfold weightedRayTraceEnergy
    refine add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (range_mono hkn) fun j hj _ => ?_)
    have hj_le : j + 1 ≤ n := by have := mem_range.mp hj; omega
    exact mul_nonneg (hw (j + 1) hj_le).le (sq_nonneg _)
  have hv2 : ∑ j ∈ range (k + 1), v j ^ 2 = rayResistance w k := by
    unfold rayResistance
    refine sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ n := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hkn
    simp only [v, div_pow, one_pow, Real.sq_sqrt (hw j hj_le).le]
  have hcs := sum_mul_sq_le_sq_mul_sq (range (k + 1)) u v
  rw [huv, hv2] at hcs
  have hres0 : 0 ≤ rayResistance w k :=
    sum_nonneg fun j hj => by
      have hj_le : j ≤ n := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hkn
      exact div_nonneg zero_le_one (hw j hj_le).le
  calc y k ^ 2 ≤ (∑ j ∈ range (k + 1), u j ^ 2) * rayResistance w k := hcs
    _ ≤ weightedRayTraceEnergy w y n * rayResistance w k :=
        mul_le_mul_of_nonneg_right hu2 hres0
    _ = rayResistance w k * weightedRayTraceEnergy w y n := mul_comm _ _

/-- **Weighted Mixed-Chain Sine Inequality.**
Whenever a weight profile satisfies `w_j ≥ w_min ≥ 0` on `0, …, n`, the weighted ray trace energy
controls the square sum of the chain with constant `w_min * mixedChainConstant (n + 1)`. -/
theorem weighted_mixed_chain_sine_bound {w : ℕ → ℝ} {w_min : ℝ} (hw0 : 0 ≤ w_min)
    (y : ℕ → ℝ) (n : ℕ) (hw : ∀ j ≤ n, w_min ≤ w j) :
    w_min * mixedChainConstant (n + 1) * (∑ k ∈ range (n + 1), y k ^ 2) ≤
      weightedRayTraceEnergy w y n := by
  set z : ℕ → ℝ := fun i => if i = 0 then 0 else y (i - 1)
  have hz0 : z 0 = 0 := by simp [z]
  have hzs (k : ℕ) : z (k + 1) = y k := by simp [z]
  have hm := mixed_chain_energy_bound (n + 1) z hz0
  have hzm : ∑ i ∈ range (n + 1 + 1), z i ^ 2 = ∑ k ∈ range (n + 1), y k ^ 2 := by
    rw [sum_range_succ', hz0]; simp only [hzs]; ring
  have hze : ∑ i ∈ range (n + 1), (z (i + 1) - z i) ^ 2 =
      y 0 ^ 2 + ∑ k ∈ range n, (y k - y (k + 1)) ^ 2 := by
    rw [sum_range_succ', hzs, hz0]
    simp only [hzs]
    rw [add_comm]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by ring
  rw [hzm, hze] at hm
  have hcast : 2 * ((n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 3 := by push_cast; ring
  have hlam : mixedChainConstant (n + 1) * (∑ k ∈ range (n + 1), y k ^ 2) ≤
      y 0 ^ 2 + ∑ k ∈ range n, (y k - y (k + 1)) ^ 2 := by
    unfold mixedChainConstant
    convert hm using 3
  have h1 := mul_le_mul_of_nonneg_left hlam hw0
  have h2 : w_min * (y 0 ^ 2 + ∑ k ∈ range n, (y k - y (k + 1)) ^ 2) ≤
      weightedRayTraceEnergy w y n := by
    unfold weightedRayTraceEnergy
    rw [mul_add, mul_sum]
    refine add_le_add (mul_le_mul_of_nonneg_right (hw 0 (Nat.zero_le _)) (sq_nonneg _)) ?_
    refine sum_le_sum fun k hk => ?_
    have hk_le : k + 1 ≤ n := by have := mem_range.mp hk; omega
    exact mul_le_mul_of_nonneg_right (hw (k + 1) hk_le) (sq_nonneg _)
  linarith

/-! ## §3. Origin and Bulk Tightness on Explicit Fermi–Nyman Approximation Sequences -/

/-- The prefix sum of `sieveSeq N c` up to `M` equals the centered prefix of `horizonRow c N` plus
its linear harmonic-mean drift `horizonRowMean c N * M`. -/
theorem sum_Icc_sieveSeq_eq_weightCenteredPrefix_horizonRow (N : ℕ) (c : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Icc 1 M, sieveSeq N c k =
      weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) M +
        horizonRowMean c N * (M : ℝ) := by
  rw [← sum_mul_nat_div_eq_sum_sieveSeq N M c, weightCenteredPrefix,
    sum_Icc_sum_divisors_eq_floor]
  have hfloor : ∑ d ∈ Icc 1 M, horizonRow c N d * ((M / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 N, c d * ((M / d : ℕ) : ℝ) := by
    have h1 : ∑ d ∈ Icc 1 M, horizonRow c N d * ((M / d : ℕ) : ℝ) =
        ∑ d ∈ Icc 1 (min M N), c d * ((M / d : ℕ) : ℝ) := by
      rw [← sum_subset (Icc_subset_Icc_right (min_le_left M N))]
      · refine sum_congr rfl fun d hd => ?_
        have hdN : d ≤ N := (mem_Icc.mp hd).2.trans (min_le_right M N)
        simp [horizonRow, hdN]
      · intro d hd hnot
        simp only [mem_Icc, le_min_iff, not_and] at hd hnot
        have hNd : N < d := by omega
        simp [horizonRow, not_le.mpr hNd]
    have h2 : ∑ d ∈ Icc 1 N, c d * ((M / d : ℕ) : ℝ) =
        ∑ d ∈ Icc 1 (min M N), c d * ((M / d : ℕ) : ℝ) := by
      rw [← sum_subset (Icc_subset_Icc_right (min_le_right M N))]
      intro d hd hnot
      simp only [mem_Icc, le_min_iff, not_and] at hd hnot
      have hMd : M < d := by omega
      rw [Nat.div_eq_of_lt hMd, Nat.cast_zero, mul_zero]
    exact h1.trans h2.symm
  rw [hfloor]; ring

/-- **Exact Centered-Prefix Wavelet Identity for `fermiCellResponse`:**
At every horizon `N` and cell `n`, the cellular Fermi–Nyman response decomposes into the dyadic
centered-prefix wavelet `2 A_{row(c,N)}(⌊n/2⌋) − A_{row(c,N)}(n)` minus the bounded parity
remainder `(n mod 2) m_c(N)`:
`fermiCellResponse N c n = 2 A_{row(c,N)}(⌊n/2⌋) − A_{row(c,N)}(n) − (n mod 2) m_c(N)`. -/
theorem fermiCellResponse_eq_weightCenteredPrefix_horizonRow (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    fermiCellResponse N c n =
      2 * weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) (n / 2) -
        weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n -
        ((n % 2 : ℕ) : ℝ) * horizonRowMean c N := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix,
    sum_Icc_sieveSeq_eq_weightCenteredPrefix_horizonRow N c (n / 2),
    sum_Icc_sieveSeq_eq_weightCenteredPrefix_horizonRow N c n]
  have hdiv : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n 2).symm
  rw [hdiv]; ring

/-- The bulk cell energy of the Fermi–Nyman approximation up to cell `T`
(measuring `[1/(T+1), 1]`). -/
def fermiBulkCellEnergy (N : ℕ) (c : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The origin-tail window cell energy of the Fermi–Nyman approximation across `M + 1 ≤ n ≤ T`
(measuring `(1/(T+1), 1/(M+1)]` near `t = 0`). -/
def fermiOriginTailWindowEnergy (N : ℕ) (c : ℕ → ℝ) (M T : ℕ) : ℝ :=
  ∑ n ∈ Icc (M + 1) T, fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem fermiBulkCellEnergy_eq_sq_pronicNorm (N : ℕ) (c : ℕ → ℝ) (T : ℕ) :
    fermiBulkCellEnergy N c T = pronicNorm (fermiCellResponse N c) T ^ 2 := by
  unfold fermiBulkCellEnergy pronicNorm
  rw [Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]

/-- **Pronic Norm Wavelet Bound for `fermiCellResponse`.**
By the pronic dilation contraction at `p = 2`, the bulk pronic norm of `fermiCellResponse N c`
up to `T` is controlled by the centered-prefix pronic norm of `horizonRow c N` plus its finite
harmonic mean `|horizonRowMean c N|`. -/
theorem pronicNorm_fermiCellResponse_le (N : ℕ) (c : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fermiCellResponse N c) T ≤
      (1 + 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) *
        pronicNorm (weightCenteredPrefix (horizonRow c N) (horizonRowMean c N)) T +
      |horizonRowMean c N| := by
  set A := weightCenteredPrefix (horizonRow c N) (horizonRowMean c N)
  set m := horizonRowMean c N
  have hA0 : A 0 = 0 := by simp [A, weightCenteredPrefix]
  have hpar : ∀ n : ℕ, |(-(((n % 2 : ℕ) : ℝ) * m))| ≤ |m| := by
    intro n
    rw [abs_neg, abs_mul]
    have hmod : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num))
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg m) hmod
  calc pronicNorm (fermiCellResponse N c) T
      = pronicNorm (fun n => (2 * A (n / 2) + (-1) * A n) + (-(((n % 2 : ℕ) : ℝ) * m))) T := by
        unfold pronicNorm
        congr 1
        refine sum_congr rfl fun n _ => ?_
        rw [fermiCellResponse_eq_weightCenteredPrefix_horizonRow]; ring
    _ ≤ pronicNorm (fun n => 2 * A (n / 2) + (-1) * A n) T +
          pronicNorm (fun n => -(((n % 2 : ℕ) : ℝ) * m)) T :=
        pronicNorm_add_le _ _ T
    _ ≤ (pronicNorm (fun n => 2 * A (n / 2)) T + pronicNorm (fun n => (-1) * A n) T) + |m| :=
        add_le_add (pronicNorm_add_le _ _ T) (pronicNorm_le_of_abs_le (abs_nonneg m) hpar T)
    _ ≤ (2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * pronicNorm A T) + 1 * pronicNorm A T) + |m| := by
        rw [pronicNorm_smul 2 (fun n => A (n / 2)), pronicNorm_smul (-1) A,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_neg, abs_one]
        gcongr
        exact pronicNorm_dilate_le A hA0 (by norm_num) T
    _ = _ := by ring

/-- Pointwise square bound on `fermiCellResponse N c n` from a subpower bound on the centered
prefix of `horizonRow c N`. -/
theorem fermiCellResponse_sq_le_of_prefix_rpow {N : ℕ} {c : ℕ → ℝ} {B γ H : ℝ}
    (hB : 0 ≤ B) (hγ0 : 0 ≤ γ)
    (hpre : ∀ k : ℕ, 1 ≤ k →
      |weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) k| ≤ B * (k : ℝ) ^ γ)
    (hmean : |horizonRowMean c N| ≤ H) {n : ℕ} (hn : 1 ≤ n) :
    fermiCellResponse N c n ^ 2 ≤ 15 * B ^ 2 * (n : ℝ) ^ (2 * γ) + 3 * H ^ 2 := by
  set A := weightCenteredPrefix (horizonRow c N) (horizonRowMean c N)
  set m := horizonRowMean c N
  have h1 : fermiCellResponse N c n ^ 2 ≤
      3 * ((2 * A (n / 2)) ^ 2 + A n ^ 2 + (((n % 2 : ℕ) : ℝ) * m) ^ 2) := by
    rw [fermiCellResponse_eq_weightCenteredPrefix_horizonRow]
    set x := 2 * A (n / 2)
    set y := A n
    set z := ((n % 2 : ℕ) : ℝ) * m
    nlinarith [sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y - z)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hAn : A n ^ 2 ≤ B ^ 2 * (n : ℝ) ^ (2 * γ) := by
    have h := hpre n hn
    have hsq : A n ^ 2 ≤ (B * (n : ℝ) ^ γ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hpow : ((n : ℝ) ^ γ) ^ 2 = (n : ℝ) ^ (2 * γ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
    calc A n ^ 2 ≤ B ^ 2 * ((n : ℝ) ^ γ) ^ 2 := by linarith [mul_pow B ((n : ℝ) ^ γ) 2]
      _ = B ^ 2 * (n : ℝ) ^ (2 * γ) := by rw [hpow]
  have hAhalf : A (n / 2) ^ 2 ≤ B ^ 2 * (n : ℝ) ^ (2 * γ) := by
    rcases Nat.eq_zero_or_pos (n / 2) with h0 | hpos
    · have hA0 : A 0 = 0 := by simp [A, weightCenteredPrefix]
      rw [h0, hA0, sq, mul_zero]
      positivity
    · have h := hpre (n / 2) hpos
      have hle : ((n / 2 : ℕ) : ℝ) ^ γ ≤ (n : ℝ) ^ γ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n 2) hγ0
      have h' : |A (n / 2)| ≤ B * (n : ℝ) ^ γ :=
        h.trans (mul_le_mul_of_nonneg_left hle hB)
      have hsq : A (n / 2) ^ 2 ≤ (B * (n : ℝ) ^ γ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      have hpow : ((n : ℝ) ^ γ) ^ 2 = (n : ℝ) ^ (2 * γ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
      calc A (n / 2) ^ 2 ≤ B ^ 2 * ((n : ℝ) ^ γ) ^ 2 := by linarith [mul_pow B ((n : ℝ) ^ γ) 2]
        _ = B ^ 2 * (n : ℝ) ^ (2 * γ) := by rw [hpow]
  have hAm : (((n % 2 : ℕ) : ℝ) * m) ^ 2 ≤ H ^ 2 := by
    have hmod : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num))
    have habs : |((n % 2 : ℕ) : ℝ) * m| ≤ H := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_of_le_one_left (abs_nonneg m) hmod).trans hmean
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  nlinarith

/-- **Quantitative Origin–Bulk Tightness Criterion (`fermiBulk_and_originTail_tight_of_prefix_rpow`).**
If the horizon-`N` rows of `c` obey a uniform subpower centered-prefix bound
`|A_{row(c,N)}(k)| ≤ B k^γ` with `0 ≤ γ < 1/2` and a uniform harmonic-mean bound
`|m_c(N)| ≤ H`, then:
1. the bulk cell energies `fermiBulkCellEnergy N c T` are uniformly bounded across all `N, T`;
2. the origin-tail window energies `fermiOriginTailWindowEnergy N c M T` converge to `0` as
   `M → ∞` **uniformly in `N` and `T`**. -/
theorem fermiBulk_and_originTail_tight_of_prefix_rpow {c : ℕ → ℝ} {B γ H : ℝ}
    (hB : 0 ≤ B) (hγ0 : 0 ≤ γ) (hγ : γ < 1 / 2)
    (hpre : ∀ N k : ℕ, 1 ≤ k →
      |weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) k| ≤ B * (k : ℝ) ^ γ)
    (hmean : ∀ N : ℕ, |horizonRowMean c N| ≤ H) :
    (∃ E_bulk : ℝ, ∀ N T : ℕ, fermiBulkCellEnergy N c T ≤ E_bulk) ∧
    (∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N T : ℕ,
      fermiOriginTailWindowEnergy N c M T ≤ δ) := by
  have hsum : Summable (fun n : ℕ => 15 * B ^ 2 * (n : ℝ) ^ (2 * γ - 2) +
      3 * H ^ 2 * (n : ℝ) ^ (-2 : ℝ)) :=
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left (15 * B ^ 2)).add
      ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left (3 * H ^ 2))
  set g : ℕ → ℝ := fun n =>
    15 * B ^ 2 * (n : ℝ) ^ (2 * γ - 2) + 3 * H ^ 2 * (n : ℝ) ^ (-2 : ℝ)
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    dsimp [g]
    exact add_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hcell_le : ∀ N n : ℕ, 1 ≤ n →
      fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ g n := by
    intro N n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq := fermiCellResponse_sq_le_of_prefix_rpow hB hγ0 (hpre N) (hmean N) hn
    have hnn : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
      rw [Real.rpow_two]; nlinarith
    have hpow1 : (n : ℝ) ^ (2 * γ) / (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 * γ - 2) :=
      (Real.rpow_sub hn0 (2 * γ) 2).symm
    have hpow2 : 1 / (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (-2 : ℝ) := by
      rw [one_div, ← Real.rpow_neg hn0.le]
    calc fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ (15 * B ^ 2 * (n : ℝ) ^ (2 * γ) + 3 * H ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ (15 * B ^ 2 * (n : ℝ) ^ (2 * γ) + 3 * H ^ 2) / (n : ℝ) ^ (2 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hnn
      _ = 15 * B ^ 2 * ((n : ℝ) ^ (2 * γ) / (n : ℝ) ^ (2 : ℝ)) +
            3 * H ^ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by ring
      _ = g n := by dsimp [g]; rw [hpow1, hpow2]
  refine ⟨⟨∑' n : ℕ, g n, fun N T => ?_⟩, fun δ hδ => ?_⟩
  · unfold fermiBulkCellEnergy
    calc ∑ n ∈ Icc 1 T, fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc 1 T, g n := sum_le_sum fun n hn => hcell_le N n (mem_Icc.mp hn).1
      _ ≤ ∑' n : ℕ, g n := hsum.sum_le_tsum _ fun n _ => hg_nonneg n
  · -- Tail of a summable series tends to 0: `∑_{n ∉ range (M + 1)} g n → 0` as `M → ∞`
    have htail : Tendsto (fun M : ℕ => ∑' k : ℕ, g (k + (M + 1))) atTop (𝓝 0) := by
      have h := tendsto_sum_nat_add g
      exact h.comp (tendsto_add_atTop_nat 1)
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp htail δ hδ
    refine ⟨M₀, fun M hM N T => ?_⟩
    have hM_lt := hM₀ M hM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun k => hg_nonneg (k + (M + 1)))] at hM_lt
    unfold fermiOriginTailWindowEnergy
    by_cases hMT : M + 1 ≤ T
    · have hsub : ∑ n ∈ Icc (M + 1) T, g n ≤ ∑' k : ℕ, g (k + (M + 1)) := by
        have hreindex : ∀ R : ℕ, ∑ n ∈ Icc (M + 1) (M + R), g n =
            ∑ k ∈ range R, g (k + (M + 1)) := by
          intro R
          induction R with
          | zero => rw [Icc_eq_empty (by omega), sum_empty, range_zero, sum_empty]
          | succ R ih =>
            rw [show M + (R + 1) = (M + R) + 1 by omega,
              Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
            congr 2; omega
        rw [show T = M + (T - M) by omega, hreindex (T - M)]
        exact (hsum.comp_injective (add_left_injective (M + 1))).sum_le_tsum _
          fun k _ => hg_nonneg (k + (M + 1))
      calc ∑ n ∈ Icc (M + 1) T, fermiCellResponse N c n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
          ≤ ∑ n ∈ Icc (M + 1) T, g n :=
            sum_le_sum fun n hn => hcell_le N n (by have := (mem_Icc.mp hn).1; omega)
        _ ≤ ∑' k : ℕ, g (k + (M + 1)) := hsub
        _ ≤ δ := hM_lt.le
    · rw [Icc_eq_empty hMT, sum_empty]
      exact hδ.le

/-- **Uniform Bulk Boundedness and Uniform Origin-Tail Tightness Above Half Damping.**
For every `K ≥ 0`, `ε > 1/2`, and `c ∈ DampedClass K ε`, the Fermi–Nyman approximation sequence
`fermiCellResponse N c` is uniformly bulk-bounded and uniformly origin-tail tight across all
horizons `N` and cutoffs `T`. -/
theorem fermiBulk_and_originTail_tight_of_dampedClass_half_lt {K ε : ℝ} (hε : 1 / 2 < ε)
    {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    (∃ E_bulk : ℝ, ∀ N T : ℕ, fermiBulkCellEnergy N c T ≤ E_bulk) ∧
    (∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N T : ℕ,
      fermiOriginTailWindowEnergy N c M T ≤ δ) := by
  have hK : 0 ≤ K := nonneg_of_dampedClass hc
  set ε' : ℝ := min ε (3 / 4)
  have hε'half : 1 / 2 < ε' := lt_min hε (by norm_num)
  have hε'0 : 0 < ε' := by linarith
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h1ε' : 0 < 1 - ε' := by linarith
  have hc' : DampedClass K ε' c := dampedClass_mono hε'0 (min_le_left _ _) hc
  have hsum_abs : Summable (fun d : ℕ => |c d / d|) :=
    (summable_div_of_dampedClass hε'0 hc').abs
  refine fermiBulk_and_originTail_tight_of_prefix_rpow
    (B := K * (1 + 1 / (1 - ε') + 1 / ε')) (γ := 1 - ε') (H := ∑' d : ℕ, |c d / d|)
    (by positivity) (by linarith) (by linarith)
    ?_ (fun N => abs_horizonRowMean_le_tsum hsum_abs N)
  intro N k hk
  have hcN : DampedClass K ε' (horizonRow c N) := fun d =>
    (abs_horizonRow_le c N d).trans (hc' d)
  have h := abs_weightCenteredPrefix_le_of_dampedClass hε'0 hε'1 hcN hk
  rwa [tsum_horizonRow_div] at h

/-- **Uniform Bulk Boundedness and Uniform Origin-Tail Tightness for Damped Sign Rows (`ε > β / 2`).**
For any sign pattern `|s(d)| ≤ 1` with subpower partial sums `|∑_{e ≤ M} s(e)| ≤ C (M + 1)^β`
(`0 ≤ β < 1`) and any damping `ε > β / 2`, the Fermi–Nyman approximation sequence
`fermiCellResponse N (dampedSignWeight s ε)` is uniformly bulk-bounded and uniformly origin-tail
tight across all horizons `N` and cutoffs `T`. -/
theorem fermiBulk_and_originTail_tight_dampedSign_of_partialSum_rpow {s : ℕ → ℝ} {β C ε : ℝ}
    (hs1 : ∀ d, |s d| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hC0 : 0 ≤ C)
    (hS : ∀ M : ℕ, |∑ e ∈ Icc 1 M, s e| ≤ C * ((M : ℝ) + 1) ^ β)
    (hε : β / 2 < ε) :
    (∃ E_bulk : ℝ, ∀ N T : ℕ,
      fermiBulkCellEnergy N (dampedSignWeight s ε) T ≤ E_bulk) ∧
    (∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N T : ℕ,
      fermiOriginTailWindowEnergy N (dampedSignWeight s ε) M T ≤ δ) := by
  have hε0 : 0 < ε := by linarith
  rcases lt_or_ge (1 / 2) ε with hgt | hε2
  · refine fermiBulk_and_originTail_tight_of_dampedClass_half_lt (K := 1) hgt fun d => ?_
    rw [dampedSignWeight, one_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
  set β' : ℝ := min ((β + 2 * ε) / 2) 1
  have hβ_le : β ≤ β' := le_min (by linarith) hβ1.le
  have hβ'2ε : β' < 2 * ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hβ'1 : β' ≤ 1 := min_le_right _ _
  have hβ'0 : 0 ≤ β' := hβ0.trans hβ_le
  have h2β : 0 < 2 - β' := by linarith
  set a : ℝ := 1 / (2 - β')
  set γ : ℝ := a * (1 - ε)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; rw [div_le_one h2β]; linarith
  have hγ0 : 0 ≤ γ := mul_nonneg ha0.le (by linarith)
  have hγhalf : γ < 1 / 2 := by
    dsimp [γ, a]; rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2β]; linarith
  have hγeq : 1 + a * (β' - 1 - ε) = γ := by dsimp [γ, a]; field_simp; ring
  have hc_class : DampedClass 1 ε (dampedSignWeight s ε) := fun d => by
    rw [dampedSignWeight, one_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
  have hsum_abs : Summable (fun d : ℕ => |dampedSignWeight s ε d / d|) :=
    (summable_div_of_dampedClass hε0 hc_class).abs
  refine fermiBulk_and_originTail_tight_of_prefix_rpow
    (B := 3 + 52 / ε * C) (γ := γ) (H := ∑' d : ℕ, |dampedSignWeight s ε d / d|)
    (by positivity) hγ0 hγhalf ?_
    (fun N => abs_horizonRowMean_le_tsum hsum_abs N)
  intro N n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set y : ℝ := (n : ℝ) ^ a with hy
  have hy1 : 1 ≤ y := by
    rw [hy, ← Real.one_rpow a]
    exact Real.rpow_le_rpow zero_le_one hn1 ha0.le
  have hy0 : 0 < y := by linarith
  set D : ℕ := ⌊y⌋₊ with hD
  have hD1 : 1 ≤ D := Nat.floor_pos.mpr hy1
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyD : y / 2 ≤ D := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    rw [← hD] at h1
    linarith
  have hyn : y ≤ n := by
    rw [hy]
    calc (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 ha1
      _ = n := Real.rpow_one _
  have hDn : D ≤ n := by exact_mod_cast hDy.trans hyn
  set L : ℝ := 2 * C * (D : ℝ) ^ (β' - 1) with hL
  have hL0 : 0 ≤ L := by positivity
  have hSl : ∀ x : ℕ, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (hD1.trans hx)
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (hD1.trans hx)
    have hDx : (D : ℝ) ≤ x := by exact_mod_cast hx
    have hxβ : (x : ℝ) ^ β' = (x : ℝ) ^ (β' - 1) * x := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    have h2β' : (2 : ℝ) ^ β' ≤ 2 := by
      calc (2 : ℝ) ^ β' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ'1
        _ = 2 := Real.rpow_one 2
    have hmon_β : ((x : ℝ) + 1) ^ β ≤ ((x : ℝ) + 1) ^ β' :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hβ_le
    calc |∑ e ∈ Icc 1 x, s e| ≤ C * ((x : ℝ) + 1) ^ β := hS x
      _ ≤ C * ((x : ℝ) + 1) ^ β' := mul_le_mul_of_nonneg_left hmon_β hC0
      _ ≤ C * (2 * (x : ℝ)) ^ β' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hβ'0) hC0
      _ = C * (2 ^ β' * (x : ℝ) ^ β') := by rw [Real.mul_rpow (by norm_num) hx0.le]
      _ ≤ C * (2 * (x : ℝ) ^ β') :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2β' (Real.rpow_nonneg hx0.le _)) hC0
      _ = 2 * C * ((x : ℝ) ^ (β' - 1) * x) := by rw [hxβ]; ring
      _ ≤ 2 * C * ((D : ℝ) ^ (β' - 1) * x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (rpow_sub_one_le_of_le hβ'1 hD0 hDx) hx0.le)
          (by positivity)
      _ = L * x := by rw [hL]; ring
  have hA := abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos hL0 hε0 hε2 hs1 hD1
    hDn hSl N
  refine hA.trans ?_
  have hT1 : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ γ := by
    calc (D : ℝ) ^ (1 - ε) ≤ y ^ (1 - ε) := Real.rpow_le_rpow hD0.le hDy (by linarith)
      _ = (n : ℝ) ^ γ := by rw [hy, ← Real.rpow_mul hn0.le]
  have hpow : (D : ℝ) ^ (β' - 1 - ε) ≤ 2 * y ^ (β' - 1 - ε) := by
    have hexp0 : 0 ≤ 1 + ε - β' := by linarith
    have hexp1 : 1 + ε - β' ≤ 1 := by
      have : ε ≤ β' := le_min (by linarith) (by linarith)
      linarith
    have h2e : (2 : ℝ) ^ (1 + ε - β') ≤ 2 := by
      calc (2 : ℝ) ^ (1 + ε - β') ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
        _ = 2 := Real.rpow_one 2
    have hylow : y ^ (1 + ε - β') / 2 ≤ (D : ℝ) ^ (1 + ε - β') := by
      calc y ^ (1 + ε - β') / 2 ≤ y ^ (1 + ε - β') / 2 ^ (1 + ε - β') :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) (by positivity) h2e
        _ = (y / 2) ^ (1 + ε - β') := (Real.div_rpow hy0.le (by norm_num) _).symm
        _ ≤ (D : ℝ) ^ (1 + ε - β') := Real.rpow_le_rpow (by positivity) hyD hexp0
    rw [show β' - 1 - ε = -(1 + ε - β') by ring, Real.rpow_neg hD0.le, Real.rpow_neg hy0.le]
    calc ((D : ℝ) ^ (1 + ε - β'))⁻¹ ≤ (y ^ (1 + ε - β') / 2)⁻¹ :=
          inv_anti₀ (by positivity) hylow
      _ = 2 * (y ^ (1 + ε - β'))⁻¹ := by rw [inv_div]; ring
  have hT2 : 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε) ≤ 52 / ε * C * (n : ℝ) ^ γ := by
    have hcomb : (D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε) = (D : ℝ) ^ (β' - 1 - ε) := by
      rw [← Real.rpow_add hD0]; ring_nf
    have hyγ : (n : ℝ) * y ^ (β' - 1 - ε) = (n : ℝ) ^ γ := by
      rw [hy, ← Real.rpow_mul hn0.le, ← hγeq, Real.rpow_add hn0, Real.rpow_one]
    calc 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
        = (26 / ε * C * (n : ℝ)) * ((D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε)) := by rw [hL]; ring
      _ = (26 / ε * C * (n : ℝ)) * (D : ℝ) ^ (β' - 1 - ε) := by rw [hcomb]
      _ ≤ (26 / ε * C * (n : ℝ)) * (2 * y ^ (β' - 1 - ε)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 52 / ε * C * ((n : ℝ) * y ^ (β' - 1 - ε)) := by ring
      _ = 52 / ε * C * (n : ℝ) ^ γ := by rw [hyγ]
  calc 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
      ≤ 3 * (n : ℝ) ^ γ + 52 / ε * C * (n : ℝ) ^ γ :=
        add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num)) hT2
    _ = (3 + 52 / ε * C) * (n : ℝ) ^ γ := by ring

/-- **Uniform Bulk Boundedness and Uniform Origin-Tail Tightness for Damped Möbius (`ε > Θ / 2`).**
For every damping `ε > Θ / 2` (and hence for every `ε > 1/4` under `RiemannHypothesis`, and
unconditionally for `ε > 1/2`), the damped Möbius Fermi–Nyman approximation sequence
`fermiCellResponse N (pmPowerDampedRealWeight ε)` is uniformly bulk-bounded and uniformly
origin-tail tight across all horizons `N` and cutoffs `T`. -/
theorem fermiBulk_and_originTail_tight_moebius_of_half_zetaZeroAbscissa_lt {ε : ℝ}
    (hε : zetaZeroAbscissa / 2 < ε) :
    (∃ E_bulk : ℝ, ∀ N T : ℕ,
      fermiBulkCellEnergy N (pmPowerDampedRealWeight ε) T ≤ E_bulk) ∧
    (∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N T : ℕ,
      fermiOriginTailWindowEnergy N (pmPowerDampedRealWeight ε) M T ≤ δ) := by
  have hΘ := half_le_zetaZeroAbscissa
  have hε0 : 0 < ε := by linarith
  rcases lt_or_ge (1 / 2) ε with hgt | hε2
  · exact fermiBulk_and_originTail_tight_of_dampedClass_half_lt hgt
      (dampedClass_one_pmPowerDampedRealWeight ε)
  have hΘlt1 : zetaZeroAbscissa < 1 := by linarith
  set β : ℝ := (zetaZeroAbscissa + min (2 * ε) 1) / 2
  have hβΘ : zetaZeroAbscissa < β := by
    have : zetaZeroAbscissa < min (2 * ε) 1 := lt_min (by linarith) hΘlt1
    dsimp [β]; linarith
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β < 1 := by
    have : min (2 * ε) 1 ≤ 1 := min_le_right _ _
    dsimp [β]; linarith
  have hβ2ε : β / 2 < ε := by
    have : min (2 * ε) 1 ≤ 2 * ε := min_le_left _ _
    dsimp [β]; linarith
  obtain ⟨C, hC0, hC⟩ :=
    mobiusMertens_subpower_zetaZeroAbscissa (β - zetaZeroAbscissa) (by linarith)
  have hC' : ∀ M : ℕ, |∑ e ∈ Icc 1 M, moebiusReal e| ≤ C * ((M : ℝ) + 1) ^ β := by
    intro M
    have hnorm : ‖mobiusMertensPartialSum M‖ = |∑ e ∈ Icc 1 M, moebiusReal e| := by
      have hm : mobiusMertensPartialSum M =
          ((∑ n ∈ range (M + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
        simp only [mobiusMertensPartialSum, mobiusComplexCoefficient, Complex.ofReal_sum,
          Complex.ofReal_intCast]
      rw [hm, Complex.norm_real, Real.norm_eq_abs, sum_range_moebius_eq_sum_Icc_moebiusReal]
    have := hC M
    rwa [hnorm, add_sub_cancel] at this
  rw [pmPowerDampedRealWeight_eq_dampedSignWeight]
  exact fermiBulk_and_originTail_tight_dampedSign_of_partialSum_rpow abs_moebiusReal_le_one' hβ0
    hβ1 hC0 hC' hβ2ε

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
