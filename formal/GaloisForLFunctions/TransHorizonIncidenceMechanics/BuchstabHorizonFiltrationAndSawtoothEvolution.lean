import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar III: Buchstab Horizon Filtration, Sawtooth Evolution, and Arbitrary-Weight Octave Laws (`BuchstabHorizonFiltrationAndSawtoothEvolution`)

In `BezoutValuationIncidence`, the sieve cutoff `N` was held fixed while the prefix `M` was varied
within the sub-horizon regime `M ≤ N`. To analyze the **trans-horizon regime `M > N`**, this third
foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics** varies the
**sieve horizon `N` itself** (`N ↦ N + 1` and `N₁ ↦ N₂`) at any fixed trans-horizon target `M`:

## Core Main Theorems (100% Unconditional)

1. **Single-Step & Multi-Step Buchstab Horizon Filtration (`sieveSeq_succ_horizon_sub`,
   `sieveSeq_horizon_band_sub`, `sievedFractSum_succ_horizon_sub`,
   `sievePrefixDiscrepancy_succ_horizon_sub`, `sievePrefixDiscrepancy_horizon_band_sub`)**:
   - Stepping the sieve horizon from `N` to `N + 1` injects the exact divisibility spike
     `if N + 1 ∣ k then c (N + 1) else 0` into `sieveSeq` and shifts `sievePrefixDiscrepancy N M c`
     by `-c (N + 1) * fractDivSeq (N + 1) M`.
   - Across any horizon band `N₁ ≤ N₂`:
     $$\operatorname{sieveSeq}(N_2, c, k) - \operatorname{sieveSeq}(N_1, c, k) =
       \sum_{d \in (\operatorname{Ioc} N_1 N_2).\text{filter}(\cdot \mid k)} c(d),$$
     $$\operatorname{sievePrefixDiscrepancy}(N_2, M, c) -
       \operatorname{sievePrefixDiscrepancy}(N_1, M, c) =
       -\sum_{d \in \operatorname{Ioc} N_1 N_2} c(d)\,\operatorname{fractDivSeq}(d, M).$$

2. **Exact Trans-Horizon Closure at `N₂ = M` (`sieveSeq_eq_sum_divisors_of_le`,
   `sieveSeq_transHorizon_tail_decomp`, `sievePrefixDiscrepancy_transHorizon_tail_decomp`)**:
   - Whenever `1 ≤ k ≤ M`, `sieveSeq M c k = ∑ d ∈ k.divisors, c d` is sieve-complete.
   - Consequently, for every trans-horizon pair `N ≤ M` and `1 ≤ k ≤ M`:
     $$\operatorname{sieveSeq}(N, c, k) =
       \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) -
         \sum_{d \in (\operatorname{Ioc} N M).\text{filter}(\cdot \mid k)} c(d),$$
     and the trans-horizon prefix discrepancy decomposes into the **horizon-matched diagonal
     discrepancy** at level `M` plus the **trans-horizon sawtooth tail** over `d ∈ (N, M]`:
     $$\operatorname{sievePrefixDiscrepancy}(N, M, c) =
       \operatorname{sievePrefixDiscrepancy}(M, M, c) +
         \sum_{d \in \operatorname{Ioc} N M} c(d)\,\operatorname{fractDivSeq}(d, M).$$

3. **Universal First-Octave Trans-Horizon Law for Arbitrary Weights
   (`sieveSeq_first_octave_eq_sum_divisors_sub_self`,
   `sieveSeq_pmPowerDampedRealWeight_first_octave_eq`)**:
   For **every** weight `c : ℕ → ℝ` and every integer `k ∈ [N + 1, 2N]` in the first trans-horizon
   octave:
   $$\operatorname{sieveSeq}(N, c, k) = \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) - c(k).$$
   For `c = pmPowerDampedRealWeight ε`, this yields the exact identity
   $$\operatorname{sieveSeq}(N, c_\varepsilon, k) =
     \operatorname{pmPowerDampedDivisorCoeff}\,\varepsilon\,k -
       \operatorname{pmPowerDampedRealWeight}\,\varepsilon\,k \qquad \forall k \in [N + 1, 2N].$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Single-Step and Multi-Step Buchstab Horizon Filtration (`N₁ ↦ N₂`) -/

/-- Partition of `Finset.Icc 1 N₂` into `Finset.Icc 1 N₁` and `Finset.Ioc N₁ N₂` for `N₁ ≤ N₂`. -/
theorem Icc_one_union_Ioc_eq {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    Finset.Icc 1 N₁ ∪ Finset.Ioc N₁ N₂ = Finset.Icc 1 N₂ := by
  ext d
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem disjoint_Icc_one_Ioc (N₁ N₂ : ℕ) :
    Disjoint (Finset.Icc 1 N₁) (Finset.Ioc N₁ N₂) := by
  rw [Finset.disjoint_left]
  intro d hd1 hd2
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hd1 hd2
  omega

/-- **Multi-Step Buchstab Horizon Band Evolution of `sieveSeq` (`sieveSeq_horizon_band_sub`):**
For every `N₁ ≤ N₂`, weight `c : ℕ → ℝ`, and `k : ℕ`:
`sieveSeq N₂ c k - sieveSeq N₁ c k = ∑ d ∈ (Finset.Ioc N₁ N₂).filter (· ∣ k), c d`. -/
theorem sieveSeq_horizon_band_sub {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N₂ c k - sieveSeq N₁ c k =
      ∑ d ∈ (Finset.Ioc N₁ N₂).filter (fun d => d ∣ k), c d := by
  unfold sieveSeq
  rw [← Icc_one_union_Ioc_eq hN, Finset.filter_union,
    Finset.sum_union (Finset.disjoint_filter_filter (disjoint_Icc_one_Ioc N₁ N₂))]
  ring

/-- **Single-Step Buchstab Horizon Increment of `sieveSeq` (`sieveSeq_succ_horizon_sub`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `k : ℕ`:
`sieveSeq (N + 1) c k - sieveSeq N c k = if N + 1 ∣ k then c (N + 1) else 0`. -/
theorem sieveSeq_succ_horizon_sub (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq (N + 1) c k - sieveSeq N c k =
      if N + 1 ∣ k then c (N + 1) else 0 := by
  rw [sieveSeq_horizon_band_sub (Nat.le_succ N), Nat.Ioc_succ_singleton,
    Finset.filter_singleton]
  split_ifs <;> simp

/-- **Multi-Step Horizon Band Evolution of `sievedFractSum` (`sievedFractSum_horizon_band_sub`):**
For every `N₁ ≤ N₂`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`:
`sievedFractSum N₂ c M - sievedFractSum N₁ c M = ∑ d ∈ Finset.Ioc N₁ N₂, c d * fractDivSeq d M`. -/
theorem sievedFractSum_horizon_band_sub {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (M : ℕ) (c : ℕ → ℝ) :
    sievedFractSum N₂ c M - sievedFractSum N₁ c M =
      ∑ d ∈ Finset.Ioc N₁ N₂, c d * fractDivSeq d M := by
  unfold sievedFractSum
  rw [← Icc_one_union_Ioc_eq hN, Finset.sum_union (disjoint_Icc_one_Ioc N₁ N₂)]
  ring

/-- **Single-Step Horizon Increment of `sievedFractSum` (`sievedFractSum_succ_horizon_sub`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`:
`sievedFractSum (N + 1) c M - sievedFractSum N c M = c (N + 1) * fractDivSeq (N + 1) M`. -/
theorem sievedFractSum_succ_horizon_sub (N M : ℕ) (c : ℕ → ℝ) :
    sievedFractSum (N + 1) c M - sievedFractSum N c M =
      c (N + 1) * fractDivSeq (N + 1) M := by
  rw [sievedFractSum_horizon_band_sub (Nat.le_succ N), Nat.Ioc_succ_singleton,
    Finset.sum_singleton]

/-- **Multi-Step Horizon Band Evolution of `sievePrefixDiscrepancy`
(`sievePrefixDiscrepancy_horizon_band_sub`):**
For every `N₁ ≤ N₂`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`:
`sievePrefixDiscrepancy N₂ M c - sievePrefixDiscrepancy N₁ M c = -∑ d ∈ Finset.Ioc N₁ N₂, c d * fractDivSeq d M`. -/
theorem sievePrefixDiscrepancy_horizon_band_sub {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    (M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N₂ M c - sievePrefixDiscrepancy N₁ M c =
      -∑ d ∈ Finset.Ioc N₁ N₂, c d * fractDivSeq d M := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    ← sievedFractSum_horizon_band_sub hN M c]
  ring

/-- **Single-Step Horizon Increment of `sievePrefixDiscrepancy`
(`sievePrefixDiscrepancy_succ_horizon_sub`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`:
`sievePrefixDiscrepancy (N + 1) M c - sievePrefixDiscrepancy N M c = -c (N + 1) * fractDivSeq (N + 1) M`. -/
theorem sievePrefixDiscrepancy_succ_horizon_sub (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy (N + 1) M c - sievePrefixDiscrepancy N M c =
      -c (N + 1) * fractDivSeq (N + 1) M := by
  rw [sievePrefixDiscrepancy_horizon_band_sub (Nat.le_succ N),
    Nat.Ioc_succ_singleton, Finset.sum_singleton, neg_mul]

/-! ## §2. Exact Trans-Horizon Closure at `N₂ = M` -/

/-- **Complete Divisor-Sum Identity Below the Horizon (`sieveSeq_eq_sum_divisors_of_le`):**
For every `1 ≤ k ≤ M` and weight `c : ℕ → ℝ`:
`sieveSeq M c k = ∑ d ∈ k.divisors, c d`. -/
theorem sieveSeq_eq_sum_divisors_of_le {M k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M)
    (c : ℕ → ℝ) :
    sieveSeq M c k = ∑ d ∈ k.divisors, c d := by
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le M hk1]
  have hfilter : k.divisors.filter (fun d => d ≤ M) = k.divisors := by
    rw [Finset.filter_eq_self]
    intro d hd
    exact (Nat.le_of_dvd hk1 (Nat.mem_divisors.mp hd).1).trans hkM
  rw [hfilter]

/-- **Trans-Horizon Divisor-Tail Decomposition of `sieveSeq`
(`sieveSeq_transHorizon_tail_decomp`):**
For every trans-horizon pair `N ≤ M`, integer `1 ≤ k ≤ M`, and weight `c : ℕ → ℝ`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - ∑ d ∈ (Finset.Ioc N M).filter (· ∣ k), c d`. -/
theorem sieveSeq_transHorizon_tail_decomp {N M k : ℕ} (hNM : N ≤ M)
    (hk1 : 1 ≤ k) (hkM : k ≤ M) (c : ℕ → ℝ) :
    sieveSeq N c k =
      (∑ d ∈ k.divisors, c d) -
        ∑ d ∈ (Finset.Ioc N M).filter (fun d => d ∣ k), c d := by
  have hband := sieveSeq_horizon_band_sub hNM c k
  rw [sieveSeq_eq_sum_divisors_of_le hk1 hkM c] at hband
  linarith

/-- **Trans-Horizon Sawtooth-Tail Decomposition of `sievePrefixDiscrepancy`
(`sievePrefixDiscrepancy_transHorizon_tail_decomp`):**
For every trans-horizon pair `N ≤ M` and weight `c : ℕ → ℝ`, the prefix discrepancy at cutoff `N`
equals the horizon-matched diagonal discrepancy at level `M` plus the sawtooth tail over `(N, M]`:
`sievePrefixDiscrepancy N M c = sievePrefixDiscrepancy M M c + ∑ d ∈ Finset.Ioc N M, c d * fractDivSeq d M`. -/
theorem sievePrefixDiscrepancy_transHorizon_tail_decomp {N M : ℕ} (hNM : N ≤ M)
    (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c =
      sievePrefixDiscrepancy M M c +
        ∑ d ∈ Finset.Ioc N M, c d * fractDivSeq d M := by
  have hband := sievePrefixDiscrepancy_horizon_band_sub hNM M c
  linarith

/-! ## §3. Universal First-Octave Trans-Horizon Law for Arbitrary Weights -/

/-- **Universal First-Octave Trans-Horizon Identity (`sieveSeq_first_octave_eq_sum_divisors_sub_self`):**
For **every** weight `c : ℕ → ℝ` and every integer `k ∈ [N + 1, 2N]` in the first trans-horizon
octave, the only divisor of `k` exceeding `N` is `k` itself, so:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k`. -/
theorem sieveSeq_first_octave_eq_sum_divisors_sub_self {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k := by
  have hk_pos : 1 ≤ k := by omega
  have hNM : N ≤ k := by omega
  rw [sieveSeq_transHorizon_tail_decomp hNM hk_pos le_rfl c]
  have hset : (Finset.Ioc N k).filter (fun d => d ∣ k) = {k} := by
    rw [← divisors_filter_gt_eq_singleton_of_first_octave hk1 hk2]
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdN, _⟩, hdk⟩
      exact ⟨⟨hdk, by omega⟩, hdN⟩
    · rintro ⟨⟨hdk, _⟩, hdN⟩
      exact ⟨⟨hdN, Nat.le_of_dvd hk_pos hdk⟩, hdk⟩
  rw [hset, Finset.sum_singleton]

/-- **First-Octave Trans-Horizon Identity for `pmPowerDampedRealWeight ε`
(`sieveSeq_pmPowerDampedRealWeight_first_octave_eq`):**
For every `ε : ℝ` and every `k ∈ [N + 1, 2N]`:
`sieveSeq N (pmPowerDampedRealWeight ε) k = pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k`. -/
theorem sieveSeq_pmPowerDampedRealWeight_first_octave_eq (ε : ℝ) {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k := by
  have hk_pos : 1 ≤ k := by omega
  rw [sieveSeq_first_octave_eq_sum_divisors_sub_self hk1 hk2,
    ← sieveSeq_eq_sum_divisors_of_le hk_pos le_rfl (pmPowerDampedRealWeight ε),
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk_pos le_rfl]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
