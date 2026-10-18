import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar VI: Complementary Quotient Reciprocity, Multi-Band Buchstab Calculus, and Rough Octave Extension (`ComplementaryQuotientAndSecondOctaveLaw`)

In `BuchstabHorizonFiltrationAndSawtoothEvolution` (Pillar III), we established the trans-horizon
divisor-tail decomposition
$$\operatorname{sieveSeq}(N, c, k) = \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) -
  \sum_{d \in k.\text{divisors},\, N < d} c(d)$$
and evaluated the first trans-horizon octave `k ∈ [N + 1, 2N]`.

To make **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics** an autonomous mathematical
discipline across all trans-horizon octaves `k > N`, this sixth foundational pillar introduces the
**Complementary Quotient Tail Operator** `complementaryQuotientTail N c k` and proves the
**Fundamental Complementary Quotient Reciprocity Theorem**, the **Multi-Band Quotient Truncation
Theorem**, the **Universal `B`-Rough Octave Extension Theorem** up to `(B + 1)N`, and the exact
**Second-Band (`2N + 1 ≤ k ≤ 3N`) and Third-Band (`3N + 1 ≤ k ≤ 4N`) Laws** for arbitrary weights:

## Core Main Theorems (100% Unconditional)

1. **Fundamental Complementary Quotient Duality (`sum_divisors_filter_gt_eq_complementaryQuotientTail`,
   `sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail`)**:
   Under the multiplicative involution `d ↦ q = k / d` on `k.divisors`, every high divisor `d ∣ k`
   above the horizon (`d > N`) corresponds bijectively to a complementary quotient divisor `q ∣ k`
   satisfying `N < k / q`:
   $$\sum_{d \in k.\text{divisors},\, N < d} c(d) =
     \operatorname{complementaryQuotientTail}(N, c, k) :=
     \sum_{q \in k.\text{divisors},\, N < k / q} c(k / q).$$

2. **Multi-Band Quotient Compression (`complementaryQuotientTail_eq_sum_Icc_of_le_mul`)**:
   Whenever `1 ≤ k ≤ (B + 1) * N`, every complementary quotient `q ∣ k` with `N < k / q` satisfies
   `1 ≤ q ≤ B`, compressing the trans-horizon tail at scale `k` into the low window `[1, B]`:
   $$\operatorname{complementaryQuotientTail}(N, c, k) =
     \sum_{q \in (\operatorname{Icc} 1 B).\text{filter}(\text{fun } q \Rightarrow q \mid k \wedge N < k / q)} c(k / q).$$

3. **Universal `B`-Rough Octave Extension Theorem (`divisors_filter_gt_eq_singleton_of_isTransHorizonRough`,
   `sieveSeq_rough_band_eq_sum_divisors_sub_self`,
   `sieveSeq_odd_le_three_mul_eq_sum_divisors_sub_self`,
   `sieveSeq_coprime_six_le_four_mul_eq_sum_divisors_sub_self`)**:
   For **every** `B`-rough integer `k` (`IsTransHorizonRough B k`, meaning no `2 ≤ q ≤ B` divides `k`)
   in the extended trans-horizon range `N + 1 ≤ k ≤ (B + 1) * N` and **every** weight `c : ℕ → ℝ`,
   the only divisor of `k` exceeding `N` is `k` itself, so the first-octave law extends all the way
   to `(B + 1) * N`:
   $$\operatorname{sieveSeq}(N, c, k) = \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) - c(k).$$
   Specializing to `B = 2` extends the first-octave law to `k ≤ 3N` for all odd `k`, and specializing
   to `B = 3` extends it to `k ≤ 4N` for all `k` coprime to `6` (`¬ 2 ∣ k` and `¬ 3 ∣ k`).

4. **Universal Second-Band (`2N + 1 ≤ k ≤ 3N`) and Third-Band (`3N + 1 ≤ k ≤ 4N`) Closed Forms
   (`sieveSeq_second_octave_eq_sum_divisors_sub`,
   `sieveSeq_pmPowerDampedRealWeight_second_octave_eq`,
   `sieveSeq_third_band_eq_sum_divisors_sub`)**:
   - On `2N + 1 ≤ k ≤ 3N`:
     $$\operatorname{sieveSeq}(N, c, k) =
       \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) - c(k) -
         (\text{if } 2 \mid k \text{ then } c(k / 2) \text{ else } 0).$$
   - On `3N + 1 ≤ k ≤ 4N`:
     $$\operatorname{sieveSeq}(N, c, k) =
       \Bigl(\sum_{d \in k.\text{divisors}} c(d)\Bigr) - c(k) -
         (\text{if } 2 \mid k \text{ then } c(k / 2) \text{ else } 0) -
         (\text{if } 3 \mid k \text{ then } c(k / 3) \text{ else } 0).$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. The Complementary Quotient Tail Operator & Fundamental Duality -/

/-- **The Complementary Quotient Tail Operator (`complementaryQuotientTail`):**
For a sieve horizon `N : ℕ`, weight `c : ℕ → ℝ`, and target integer `k : ℕ`, sums `c (k / q)` over
all complementary quotient divisors `q ∈ k.divisors` such that `N < k / q`. -/
def complementaryQuotientTail (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors.filter (fun q => N < k / q), c (k / q)

/-- For every `k : ℕ`, the high-divisor filter `(Finset.Ioc N k).filter (· ∣ k)` coincides with
`k.divisors.filter (fun d => N < d)`. -/
theorem filter_dvd_Ioc_eq_divisors_filter_gt (N k : ℕ) :
    (Finset.Ioc N k).filter (fun d => d ∣ k) = k.divisors.filter (fun d => N < d) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdN, hdk_le⟩, hdk⟩
    exact ⟨⟨hdk, by omega⟩, hdN⟩
  · rintro ⟨⟨hdk, hk0⟩, hdN⟩
    exact ⟨⟨hdN, Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdk⟩, hdk⟩

/-- **Fundamental Complementary Quotient Duality (`sum_divisors_filter_gt_eq_complementaryQuotientTail`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `k : ℕ`, the sum of `c d` over high divisors `d ∣ k` with
`N < d` equals `complementaryQuotientTail N c k` via the divisor involution `d ↦ k / d`. -/
theorem sum_divisors_filter_gt_eq_complementaryQuotientTail (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    (∑ d ∈ k.divisors.filter (fun d => N < d), c d) =
      complementaryQuotientTail N c k := by
  unfold complementaryQuotientTail
  refine Finset.sum_bij (fun d _ => k / d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdk, hk0⟩, hdN⟩ := hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdk (Nat.pos_of_ne_zero hk0)
    have hdiv_div : k / (k / d) = d := Nat.div_div_self hdk hk0
    exact ⟨⟨Nat.div_dvd_of_dvd hdk, hk0⟩, by rw [hdiv_div]; exact hdN⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁ hd₂
    have h1 : k / (k / d₁) = d₁ := Nat.div_div_self hd₁.1.1 hd₁.1.2
    have h2 : k / (k / d₂) = d₂ := Nat.div_div_self hd₂.1.1 hd₂.1.2
    rw [← h1, ← h2, heq]
  · intro q hq
    simp only [Finset.mem_filter, Nat.mem_divisors] at hq
    obtain ⟨⟨hqk, hk0⟩, hqN⟩ := hq
    refine ⟨k / q, ?_, Nat.div_div_self hqk hk0⟩
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.div_dvd_of_dvd hqk, hk0⟩, hqN⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Nat.div_div_self hd.1.1 hd.1.2]

/-- **Universal Trans-Horizon Sieve Identity via Complementary Quotients
(`sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail`):**
For every `N : ℕ`, integer `k ≥ 1`, and weight `c : ℕ → ℝ`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - complementaryQuotientTail N c k`. -/
theorem sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail (N : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (c : ℕ → ℝ) :
    sieveSeq N c k =
      (∑ d ∈ k.divisors, c d) - complementaryQuotientTail N c k := by
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N hk,
    ← sum_divisors_filter_gt_eq_complementaryQuotientTail]
  have hsplit := (Finset.sum_filter_add_sum_filter_not k.divisors (fun d => d ≤ N) c).symm
  have hnot : k.divisors.filter (fun d => ¬ d ≤ N) = k.divisors.filter (fun d => N < d) := by
    ext d; simp only [Finset.mem_filter, not_le]
  rw [hnot] at hsplit
  linarith

/-! ## §2. Multi-Band Quotient Compression & Universal `B`-Rough Octave Extension -/

/-- Whenever `k ≤ (B + 1) * N`, every divisor `q ∈ k.divisors` satisfying `N < k / q` lies in
`Finset.Icc 1 B`. -/
theorem complementary_quotient_le_of_le_mul {N B k q : ℕ} (hk : k ≤ (B + 1) * N)
    (hq_dvd : q ∣ k) (hq_gt : N < k / q) :
    1 ≤ q ∧ q ≤ B := by
  have hk_pos : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp at hq_gt
  have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hq_dvd hk_pos
  refine ⟨hq_pos, ?_⟩
  have hmul : q * (k / q) = k := Nat.mul_div_cancel' hq_dvd
  have hlt : q * (N + 1) ≤ (B + 1) * N := by
    have : N + 1 ≤ k / q := hq_gt
    nlinarith
  nlinarith

/-- **Multi-Band Quotient Compression (`complementaryQuotientTail_eq_sum_Icc_of_le_mul`):**
Whenever `k ≤ (B + 1) * N`, the complementary quotient tail is supported entirely on low quotients
`q ∈ Finset.Icc 1 B`:
`complementaryQuotientTail N c k = ∑ q ∈ (Finset.Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q), c (k / q)`. -/
theorem complementaryQuotientTail_eq_sum_Icc_of_le_mul {N B k : ℕ} (hk : k ≤ (B + 1) * N)
    (c : ℕ → ℝ) :
    complementaryQuotientTail N c k =
      ∑ q ∈ (Finset.Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q), c (k / q) := by
  unfold complementaryQuotientTail
  congr 1
  ext q
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hqk, _⟩, hqN⟩
    obtain ⟨hq1, hqB⟩ := complementary_quotient_le_of_le_mul hk hqk hqN
    exact ⟨⟨hq1, hqB⟩, hqk, hqN⟩
  · rintro ⟨⟨hq1, _⟩, hqk, hqN⟩
    have hk0 : k ≠ 0 := by
      intro h0; subst h0; simp at hqN
    exact ⟨⟨hqk, hk0⟩, hqN⟩

/-- **Universal `B`-Rough High-Divisor Collapse (`divisors_filter_gt_eq_singleton_of_rough`):**
If `k` has no divisor `2 ≤ q ≤ B` (`∀ d, d ∣ k → d ≤ B → d = 1`) and lies in the extended
trans-horizon interval `N + 1 ≤ k ≤ (B + 1) * N`, then the only divisor of `k` exceeding `N` is
`k` itself! -/
theorem divisors_filter_gt_eq_singleton_of_rough {N B k : ℕ}
    (hrough : ∀ d : ℕ, d ∣ k → d ≤ B → d = 1) (hk1 : N + 1 ≤ k) (hk2 : k ≤ (B + 1) * N) :
    k.divisors.filter (fun d => N < d) = {k} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hdk, hk0⟩, hdN⟩
    obtain ⟨q, hkq⟩ := hdk
    have hq_pos : 0 < q := by
      by_contra hq0
      have : q = 0 := by omega
      subst this; omega
    have hq_dvd : q ∣ k := ⟨d, by linarith⟩
    have hq_le : q ≤ B := by
      have : d * q ≤ (B + 1) * N := by linarith
      nlinarith
    have hq1 : q = 1 := hrough q hq_dvd hq_le
    subst hq1
    omega
  · intro hdk
    subst hdk
    exact ⟨⟨dvd_refl d, by omega⟩, by omega⟩

/-- **Universal `B`-Rough Octave Extension Theorem (`sieveSeq_rough_band_eq_sum_divisors_sub_self`):**
For every `B`-rough integer `k` (`∀ d, d ∣ k → d ≤ B → d = 1`) satisfying `N + 1 ≤ k ≤ (B + 1) * N`
and every weight `c : ℕ → ℝ`, the first-octave formula holds all the way to `(B + 1) * N`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k`. -/
theorem sieveSeq_rough_band_eq_sum_divisors_sub_self {N B k : ℕ}
    (hrough : ∀ d : ℕ, d ∣ k → d ≤ B → d = 1) (hk1 : N + 1 ≤ k) (hk2 : k ≤ (B + 1) * N)
    (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k := by
  have hk_pos : 1 ≤ k := by omega
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk_pos c,
    ← sum_divisors_filter_gt_eq_complementaryQuotientTail,
    divisors_filter_gt_eq_singleton_of_rough hrough hk1 hk2,
    Finset.sum_singleton]

/-- Every odd integer `k` (`¬ 2 ∣ k`) has no divisor `2 ≤ d ≤ 2`. -/
theorem rough_two_of_not_two_dvd {k : ℕ} (hk1 : 1 ≤ k) (hodd : ¬ 2 ∣ k) :
    ∀ d : ℕ, d ∣ k → d ≤ 2 → d = 1 := by
  intro d hdk hd2
  have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk hk1
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · rfl
  · exact False.elim (hodd hdk)

/-- **Universal Odd-Number Extension Through `3N`
(`sieveSeq_odd_le_three_mul_eq_sum_divisors_sub_self`):**
For **every** weight `c : ℕ → ℝ` and every odd integer `k` (`¬ 2 ∣ k`) in `[N + 1, 3N]`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k`. -/
theorem sieveSeq_odd_le_three_mul_eq_sum_divisors_sub_self {N k : ℕ}
    (hodd : ¬ 2 ∣ k) (hk1 : N + 1 ≤ k) (hk2 : k ≤ 3 * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k := by
  have hk_pos : 1 ≤ k := by omega
  exact sieveSeq_rough_band_eq_sum_divisors_sub_self
    (rough_two_of_not_two_dvd hk_pos hodd) hk1 (by omega : k ≤ (2 + 1) * N) c

/-- Every integer `k ≥ 1` not divisible by `2` or `3` has no divisor `2 ≤ d ≤ 3`. -/
theorem rough_three_of_not_two_three_dvd {k : ℕ} (hk1 : 1 ≤ k)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) :
    ∀ d : ℕ, d ∣ k → d ≤ 3 → d = 1 := by
  intro d hdk hd3
  have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk hk1
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl
  · rfl
  · exact False.elim (h2 hdk)
  · exact False.elim (h3 hdk)

/-- **Universal `6`-Coprime Extension Through `4N`
(`sieveSeq_coprime_six_le_four_mul_eq_sum_divisors_sub_self`):**
For **every** weight `c : ℕ → ℝ` and every integer `k ∈ [N + 1, 4N]` with `¬ 2 ∣ k` and `¬ 3 ∣ k`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k`. -/
theorem sieveSeq_coprime_six_le_four_mul_eq_sum_divisors_sub_self {N k : ℕ}
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (hk1 : N + 1 ≤ k) (hk2 : k ≤ 4 * N) (c : ℕ → ℝ) :
    sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k := by
  have hk_pos : 1 ≤ k := by omega
  exact sieveSeq_rough_band_eq_sum_divisors_sub_self
    (rough_three_of_not_two_three_dvd hk_pos h2 h3) hk1
    (by omega : k ≤ (3 + 1) * N) c

/-! ## §3. Exact Second-Band (`2N + 1 ≤ k ≤ 3N`) and Third-Band (`3N + 1 ≤ k ≤ 4N`) Laws -/

/-- High-divisor characterization in the second trans-horizon band `2N + 1 ≤ k ≤ 3N` when `2 ∣ k`:
`k.divisors.filter (fun d => N < d) = {k, k / 2}`. -/
theorem divisors_filter_gt_eq_pair_of_second_octave_even {N k : ℕ}
    (hk1 : 2 * N + 1 ≤ k) (hk2 : k ≤ 3 * N) (h2 : 2 ∣ k) :
    k.divisors.filter (fun d => N < d) = {k, k / 2} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨m, hkm⟩, hk0⟩, hdN⟩
    rcases m with _ | _ | _ | m
    · omega
    · left; omega
    · right; omega
    · exfalso; nlinarith
  · rintro (rfl | rfl)
    · exact ⟨⟨dvd_refl d, by omega⟩, by omega⟩
    · exact ⟨⟨Nat.div_dvd_of_dvd h2, by omega⟩, by omega⟩

/-- **Universal Second-Band Law for Arbitrary Weights (`sieveSeq_second_octave_eq_sum_divisors_sub`):**
For **every** weight `c : ℕ → ℝ` and every integer `k ∈ [2N + 1, 3N]`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k - (if 2 ∣ k then c (k / 2) else 0)`. -/
theorem sieveSeq_second_octave_eq_sum_divisors_sub {N k : ℕ}
    (hk1 : 2 * N + 1 ≤ k) (hk2 : k ≤ 3 * N) (c : ℕ → ℝ) :
    sieveSeq N c k =
      (∑ d ∈ k.divisors, c d) - c k - (if 2 ∣ k then c (k / 2) else 0) := by
  by_cases h2 : 2 ∣ k
  · rw [if_pos h2]
    have hk_pos : 1 ≤ k := by omega
    rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk_pos c,
      ← sum_divisors_filter_gt_eq_complementaryQuotientTail,
      divisors_filter_gt_eq_pair_of_second_octave_even hk1 hk2 h2,
      Finset.sum_pair (by omega : k ≠ k / 2)]
    ring
  · rw [if_neg h2, sub_zero]
    exact sieveSeq_odd_le_three_mul_eq_sum_divisors_sub_self h2 (by omega) hk2 c

/-- **Second-Band Identity for `pmPowerDampedRealWeight ε`
(`sieveSeq_pmPowerDampedRealWeight_second_octave_eq`):**
For every `ε : ℝ` and every `k ∈ [2N + 1, 3N]`:
`sieveSeq N (pmPowerDampedRealWeight ε) k = pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k - (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0)`. -/
theorem sieveSeq_pmPowerDampedRealWeight_second_octave_eq (ε : ℝ) {N k : ℕ}
    (hk1 : 2 * N + 1 ≤ k) (hk2 : k ≤ 3 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - pmPowerDampedRealWeight ε k -
        (if 2 ∣ k then pmPowerDampedRealWeight ε (k / 2) else 0) := by
  have hk_pos : 1 ≤ k := by omega
  have hfull : (∑ d ∈ k.divisors, pmPowerDampedRealWeight ε d) = pmPowerDampedDivisorCoeff ε k := by
    have h0 : complementaryQuotientTail k (pmPowerDampedRealWeight ε) k = 0 := by
      unfold complementaryQuotientTail
      refine Finset.sum_eq_zero fun q hq => ?_
      simp only [Finset.mem_filter] at hq
      have : k / q ≤ k := Nat.div_le_self k q
      omega
    have h1 := sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail k hk_pos (pmPowerDampedRealWeight ε)
    have h2 := sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (ε := ε) hk_pos le_rfl
    linarith
  rw [sieveSeq_second_octave_eq_sum_divisors_sub hk1 hk2, hfull]

/-- In the third trans-horizon band `3N + 1 ≤ k ≤ 4N`, for every `q ∈ {1, 2, 3}`, `q ∣ k ∧ N < k / q`
holds if and only if `q ∣ k`. -/
theorem filter_Icc_three_third_band_eq {N k : ℕ} (hk1 : 3 * N + 1 ≤ k) :
    (Finset.Icc 1 3).filter (fun q => q ∣ k ∧ N < k / q) =
      (Finset.Icc 1 3).filter (fun q => q ∣ k) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hq, hqk, _⟩
    exact ⟨hq, hqk⟩
  · rintro ⟨⟨hq1, hq3⟩, hqk⟩
    refine ⟨⟨hq1, hq3⟩, hqk, ?_⟩
    obtain ⟨d, hkd⟩ := hqk
    have : k / q = d := by
      rw [hkd, Nat.mul_div_cancel_left d (by omega : 0 < q)]
    rw [this]
    nlinarith

/-- Explicit expansion of `Finset.Icc 1 3`: `Finset.Icc 1 3 = {1, 2, 3}`. -/
theorem Icc_one_three_eq : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by
  ext q
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **Universal Third-Band Law for Arbitrary Weights (`sieveSeq_third_band_eq_sum_divisors_sub`):**
For **every** weight `c : ℕ → ℝ` and every integer `k ∈ [3N + 1, 4N]`:
`sieveSeq N c k = (∑ d ∈ k.divisors, c d) - c k - (if 2 ∣ k then c (k / 2) else 0) - (if 3 ∣ k then c (k / 3) else 0)`. -/
theorem sieveSeq_third_band_eq_sum_divisors_sub {N k : ℕ}
    (hk1 : 3 * N + 1 ≤ k) (hk2 : k ≤ 4 * N) (c : ℕ → ℝ) :
    sieveSeq N c k =
      (∑ d ∈ k.divisors, c d) - c k -
        (if 2 ∣ k then c (k / 2) else 0) -
        (if 3 ∣ k then c (k / 3) else 0) := by
  have hk_pos : 1 ≤ k := by omega
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk_pos c,
    complementaryQuotientTail_eq_sum_Icc_of_le_mul (by omega : k ≤ (3 + 1) * N) c,
    filter_Icc_three_third_band_eq hk1, Finset.sum_filter, Icc_one_three_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat,
     Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
    one_dvd, ↓reduceIte, Nat.div_one]
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
