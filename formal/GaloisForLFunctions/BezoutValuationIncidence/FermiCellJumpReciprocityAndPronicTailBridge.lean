import GaloisForLFunctions.BezoutValuationIncidence.ChineseRemainderBezoutPeriodicityAndSawtoothDefect
import GaloisForLFunctions.BiScaleUncertainty.WitnessCellTransferAndTopOctaveTailInequality

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar VI: Fermi–Nyman Cellular Jump Reciprocity, First-Octave Tail Evaluation, and Pronic Tail Bridge

This module bridges **Bézout–Valuation Incidence Mechanics** (`GaloisForLFunctions.BezoutValuationIncidence`)
directly to the Fermi–Nyman cellular matrix `fermiCellMatrix`, the Möbius combinator
`dilatedMobiusFermiCombinator 1 N`, and the small-`t` origin-tail transfer laws of Route PM / PW-B
(`WitnessCellTransferAndTopOctaveTailInequality`):

* `sum_mul_nat_div_eq_sum_sieveSeq` & `fermiCellResponse_eq_two_prefix_half_sub_prefix`:
  For every weight `c : ℕ → ℝ`, the cellular Fermi–Nyman response
  `fermiCellResponse N c n = ∑_{d=1}^N c(d) * fermiCellMatrix d n` on the `n`-th reciprocal cell
  `I_n = (1 / (n + 1), 1 / n]` (which has exact Lebesgue measure `1 / pronicSeq n = 1 / (n(n + 1))`)
  equals twice the half-scale prefix sum of `sieveSeq N c` minus the full prefix sum:
  `fermiCellResponse N c n = 2 * ∑_{k=1}^{n/2} s_{N,c}(k) - ∑_{k=1}^n s_{N,c}(k)`.
* `fermiCellResponse_succ_sub_eq`, `fermiCellResponse_succ_sub_of_not_two_dvd`, &
  `not_two_dvd_self_and_succ`:
  Stepping across the cell boundary `t = 1 / (n + 1)` changes `fermiCellResponse N c` by
  `2 * 1_{2 ∣ (n + 1)} * s_{N,c}((n + 1) / 2) - s_{N,c}(n + 1)`. By pronic successor coprimality
  `gcd(k, k + 1) = 1`, no two consecutive cell boundaries can both activate the dyadic half-scale
  jump `2 ∣ m`.
* `fermiCellResponse_moebiusReal_first_octave`, `fermiCellResponse_moebiusReal_jump_first_octave`,
  `fermiCellResponse_moebiusReal_jump_mul_succ_first_octave`,
  `dilatedMobiusFermiCombinator_one_first_octave_on_cell`, &
  `setIntegral_cell_normSq_dilatedMobiusFermiCombinator_one_first_octave`:
  Across the entire first trans-horizon tail octave `N + 1 ≤ n ≤ 2N` (`t ∈ (1 / (2N + 1), 1 / (N + 1)]`),
  the dyadic half-scale prefix sum `∑_{k=1}^{n/2} s_{N,μ}(k) = 1` remains completely frozen, so:
  - `fermiCellResponse N moebiusReal n = 1 + ∑_{k=N+1}^n μ(k)`,
  - every inter-cell jump is purely `μ(m) = -s_{N,μ}(m)`,
  - every consecutive inter-cell jump product equals the Bézout successor correlation
    `s_{N,μ}(m) s_{N,μ}(m + 1) = μ(m) μ(m + 1)`,
  - on `I_n = (1 / (n + 1), 1 / n]`, `dilatedMobiusFermiCombinator 1 N t = -(1 + ∑_{k=N+1}^n μ(k))`,
  - and its cell `L²` energy equals `(1 + ∑_{k=N+1}^n μ(k))² / pronicSeq n`.
-/

/-! ## §1. Exact Floor-Sum / `sieveSeq` Reciprocity and Cellular Fermi–Nyman Prefix Decomposition -/

/-- For every `d, M : ℕ`, the number of multiples of `d` in `Finset.Icc 1 M` equals `M / d`. -/
theorem card_filter_dvd_Icc_eq_div (M d : ℕ) :
    ((Finset.Icc 1 M).filter (fun k => d ∣ k)).card = M / d := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.filter_insert]
    have hnot : M + 1 ∉ (Finset.Icc 1 M).filter (fun k => d ∣ k) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hstep := addDiff_floorDivSeq_eq_ite_dvd d M
    unfold addDiff floorDivSeq at hstep
    split_ifs with hdvd
    · rw [Finset.card_insert_of_notMem hnot, ih]
      rw [if_pos hdvd] at hstep
      have hnat : ((M + 1) / d : ℕ) = M / d + 1 := by
        exact_mod_cast (by linarith : (((M + 1) / d : ℕ) : ℝ) = ((M / d : ℕ) : ℝ) + 1)
      exact hnat.symm
    · rw [ih]
      rw [if_neg hdvd] at hstep
      have hnat : ((M + 1) / d : ℕ) = M / d := by
        exact_mod_cast (by linarith : (((M + 1) / d : ℕ) : ℝ) = ((M / d : ℕ) : ℝ))
      exact hnat.symm

/-- **Fundamental Floor-Sum / `sieveSeq` Reciprocity (`sum_mul_nat_div_eq_sum_sieveSeq`):**
For every sieve level `N : ℕ`, horizon `M : ℕ`, and weight `c : ℕ → ℝ`:
`∑_{d=1}^N c(d) * ⌊M / d⌋ = ∑_{k=1}^M s_{N,c}(k)`. -/
theorem sum_mul_nat_div_eq_sum_sieveSeq (N M : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 N, c d * ((M / d : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k := by
  classical
  have hrhs : (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k) =
      ∑ d ∈ Finset.Icc 1 N, c d * (((Finset.Icc 1 M).filter (fun k => d ∣ k)).card : ℝ) := by
    unfold sieveSeq
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hrhs]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [card_filter_dvd_Icc_eq_div M d]

/-- The discrete cellular Fermi–Nyman response of a weight `c : ℕ → ℝ` on the `n`-th reciprocal cell
`I_n = (1 / (n + 1), 1 / n]`:
`fermiCellResponse N c n = ∑_{d=1}^N c(d) * fermiCellMatrix d n`. -/
def fermiCellResponse (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, c d * fermiCellMatrix d n

/-- **Exact Dyadic Prefix Decomposition of `fermiCellResponse`
(`fermiCellResponse_eq_two_prefix_half_sub_prefix`):**
For every `N n : ℕ` and `c : ℕ → ℝ`, the cellular Fermi–Nyman response on `I_n` equals twice the
half-scale prefix sum of `sieveSeq N c` up to `n / 2` minus the full prefix sum up to `n`:
`fermiCellResponse N c n = 2 * ∑_{k=1}^{n/2} s_{N,c}(k) - ∑_{k=1}^n s_{N,c}(k)`. -/
theorem fermiCellResponse_eq_two_prefix_half_sub_prefix (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    fermiCellResponse N c n =
      2 * (∑ k ∈ Finset.Icc 1 (n / 2), sieveSeq N c k) -
        ∑ k ∈ Finset.Icc 1 n, sieveSeq N c k := by
  unfold fermiCellResponse fermiCellMatrix
  have hdiv2 : ∀ d : ℕ, n / (2 * d) = (n / 2) / d :=
    fun d => (Nat.div_div_eq_div_mul n 2 d).symm
  simp_rw [hdiv2, mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib, ← sum_mul_nat_div_eq_sum_sieveSeq N n c,
    ← sum_mul_nat_div_eq_sum_sieveSeq N (n / 2) c, Finset.mul_sum]
  refine congrArg (· - _) (Finset.sum_congr rfl fun d _ => by ring)

/-! ## §2. Inter-Cell Jump Reciprocity and Pronic Successor Parity Orthogonalization -/

/-- For any `n : ℕ`, `(n + 1) / 2 = n / 2 + (if 2 ∣ (n + 1) then 1 else 0)`. -/
theorem succ_div_two_eq (n : ℕ) :
    (n + 1) / 2 = n / 2 + if 2 ∣ (n + 1) then 1 else 0 := by
  by_cases h : 2 ∣ (n + 1)
  · rw [if_pos h]
    rcases h with ⟨k, hk⟩
    omega
  · rw [if_neg h]
    omega

/-- **Exact Inter-Cell Jump Law Across `t = 1 / (n + 1)` (`fermiCellResponse_succ_sub_eq`):**
Stepping from cell `I_n` to cell `I_{n+1}` changes `fermiCellResponse N c` by
`2 * 1_{2 ∣ (n + 1)} * s_{N,c}((n + 1) / 2) - s_{N,c}(n + 1)`. -/
theorem fermiCellResponse_succ_sub_eq (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    fermiCellResponse N c (n + 1) - fermiCellResponse N c n =
      (if 2 ∣ (n + 1) then 2 * sieveSeq N c ((n + 1) / 2) else 0) -
        sieveSeq N c (n + 1) := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix N c (n + 1),
    fermiCellResponse_eq_two_prefix_half_sub_prefix N c n]
  have hIcc_full : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot_full : n + 1 ∉ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
  rw [hIcc_full, Finset.sum_insert hnot_full]
  have hhalf := succ_div_two_eq n
  by_cases h2 : 2 ∣ (n + 1)
  · rw [if_pos h2] at hhalf ⊢
    have hIcc_half : Finset.Icc 1 ((n + 1) / 2) = insert ((n + 1) / 2) (Finset.Icc 1 (n / 2)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_half : (n + 1) / 2 ∉ Finset.Icc 1 (n / 2) := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc_half, Finset.sum_insert hnot_half]
    ring
  · rw [if_neg h2] at hhalf ⊢
    have hhalf0 : (n + 1) / 2 = n / 2 := by omega
    rw [hhalf0]
    ring

/-- At every odd cell index `n + 1` (`¬ (2 ∣ (n + 1))`), the inter-cell jump of
`fermiCellResponse N c` is purely `-s_{N,c}(n + 1)`. -/
theorem fermiCellResponse_succ_sub_of_not_two_dvd (N : ℕ) (c : ℕ → ℝ) {n : ℕ}
    (hodd : ¬ (2 ∣ (n + 1))) :
    fermiCellResponse N c (n + 1) - fermiCellResponse N c n = -sieveSeq N c (n + 1) := by
  rw [fermiCellResponse_succ_sub_eq, if_neg hodd, zero_sub]

/-- **Pronic Successor Parity Orthogonalization (`not_two_dvd_self_and_succ`):**
Because `gcd(k, k + 1) = 1`, no two consecutive cell boundaries `k` and `k + 1` can both activate
the dyadic half-scale jump `2 ∣ m`. -/
theorem not_two_dvd_self_and_succ (k : ℕ) : ¬ (2 ∣ k ∧ 2 ∣ (k + 1)) := by
  rintro ⟨h1, h2⟩
  have hcop : Nat.Coprime 2 2 := coprime_of_dvd_self_succ h1 h2
  revert hcop
  decide

/-! ## §3. First Trans-Horizon Octave Exact Evaluation of `dilatedMobiusFermiCombinator` -/

/-- For `1 ≤ m ≤ N`, `sieveSeq N moebiusReal m = if m = 1 then 1 else 0`. -/
theorem sieveSeq_moebiusReal_eq_ite_of_le {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    sieveSeq N moebiusReal m = if m = 1 then 1 else 0 := by
  have hdiv : (Finset.Icc 1 N).filter (fun d => d ∣ m) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm1, (Nat.le_of_dvd hm1 hd).trans hmN⟩, hd⟩
  unfold sieveSeq
  rw [hdiv, sum_divisors_moebiusReal_eq_ite_one hm1]

/-- For `1 ≤ M ≤ N`, the prefix sum `∑_{k=1}^M s_{N,μ}(k)` equals `1`. -/
theorem sum_sieveSeq_moebiusReal_eq_one_of_le {N M : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) = 1 := by
  have hcongr : ∀ k ∈ Finset.Icc 1 M,
      sieveSeq N moebiusReal k = if k = 1 then (1 : ℝ) else 0 := by
    intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_moebiusReal_eq_ite_of_le hk1 (hkM.trans hMN)
  rw [Finset.sum_congr rfl hcongr]
  simp [hM1]

/-- **Exact First Trans-Horizon Octave Formula for `fermiCellResponse N moebiusReal`
(`fermiCellResponse_moebiusReal_first_octave`):**
For every `N ≥ 1` and every cell index `n ∈ [N + 1, 2N]` in the first trans-horizon octave:
`fermiCellResponse N moebiusReal n = 1 + ∑_{k=N+1}^n μ(k)`. -/
theorem fermiCellResponse_moebiusReal_first_octave {N n : ℕ}
    (hN : 1 ≤ N) (hn_low : N + 1 ≤ n) (hn_high : n ≤ 2 * N) :
    fermiCellResponse N moebiusReal n =
      1 + ∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix]
  have hhalf_ge : 1 ≤ n / 2 := by omega
  have hhalf_le : n / 2 ≤ N := by omega
  rw [sum_sieveSeq_moebiusReal_eq_one_of_le hhalf_ge hhalf_le]
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 N ∪ Finset.Icc (N + 1) n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) n) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj, sum_sieveSeq_moebiusReal_eq_one_of_le hN le_rfl]
  have hoct : ∀ k ∈ Finset.Icc (N + 1) n,
      sieveSeq N moebiusReal k = -moebiusReal k := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_moebiusReal_first_octave hk1 (hkn.trans hn_high)
  rw [Finset.sum_congr rfl hoct, Finset.sum_neg_distrib]
  ring

/-- **Pure Möbius Jump Law in the First Trans-Horizon Octave
(`fermiCellResponse_moebiusReal_jump_first_octave`):**
For every `N ≥ 2` and every `m ∈ [N + 1, 2N]`, the inter-cell jump of `fermiCellResponse N moebiusReal`
at cell boundary `m` is purely `moebiusReal m = -sieveSeq N moebiusReal m` (the dyadic half-scale
term vanishes identically!). -/
theorem fermiCellResponse_moebiusReal_jump_first_octave {N m : ℕ}
    (hN : 2 ≤ N) (hm_low : N + 1 ≤ m) (hm_high : m ≤ 2 * N) :
    fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) =
      moebiusReal m := by
  have hm_eq : m - 1 + 1 = m := by omega
  have hstep := fermiCellResponse_succ_sub_eq N moebiusReal (m - 1)
  rw [hm_eq] at hstep
  rw [hstep, sieveSeq_moebiusReal_first_octave hm_low hm_high]
  by_cases h2 : 2 ∣ m
  · rw [if_pos h2]
    have hhalf1 : 1 ≤ m / 2 := by omega
    have hhalfN : m / 2 ≤ N := by omega
    have hhalf_ne1 : m / 2 ≠ 1 := by omega
    rw [sieveSeq_moebiusReal_eq_ite_of_le hhalf1 hhalfN, if_neg hhalf_ne1]
    ring
  · rw [if_neg h2]
    ring

/-- **Consecutive First-Octave Jump Correlation Equals the Bézout Successor Correlation
(`fermiCellResponse_moebiusReal_jump_mul_succ_first_octave`):**
For `N ≥ 2` and `N + 1 ≤ m` with `m + 1 ≤ 2N`, the product of two consecutive inter-cell jumps of
`fermiCellResponse N moebiusReal` equals `sieveSeq N moebiusReal m * sieveSeq N moebiusReal (m + 1) = μ(m) μ(m + 1)`. -/
theorem fermiCellResponse_moebiusReal_jump_mul_succ_first_octave {N m : ℕ}
    (hN : 2 ≤ N) (hm_low : N + 1 ≤ m) (hm_high : m + 1 ≤ 2 * N) :
    (fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1)) *
      (fermiCellResponse N moebiusReal (m + 1) - fermiCellResponse N moebiusReal m) =
      sieveSeq N moebiusReal m * sieveSeq N moebiusReal (m + 1) ∧
    (fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1)) *
      (fermiCellResponse N moebiusReal (m + 1) - fermiCellResponse N moebiusReal m) =
      moebiusReal m * moebiusReal (m + 1) := by
  have hj1 := fermiCellResponse_moebiusReal_jump_first_octave hN hm_low (by omega)
  have hj2 := fermiCellResponse_moebiusReal_jump_first_octave hN (by omega : N + 1 ≤ m + 1) hm_high
  simp only [Nat.add_sub_cancel] at hj2
  rw [hj1, hj2]
  exact ⟨(sieveSeq_moebiusReal_mul_succ_first_octave hm_low hm_high).symm, rfl⟩

/-- **Exact Continuous Evaluation of `dilatedMobiusFermiCombinator 1 N` on First-Octave Tail Cells
(`dilatedMobiusFermiCombinator_one_first_octave_on_cell`):**
For every `N ≥ 1`, every first-octave tail cell index `n ∈ [N + 1, 2N]`, and every
`t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`dilatedMobiusFermiCombinator 1 N t = -((1 + ∑_{k=N+1}^n μ(k) : ℝ) : ℂ)`. -/
theorem dilatedMobiusFermiCombinator_one_first_octave_on_cell {N n : ℕ}
    (hN : 1 ≤ N) (hn_low : N + 1 ≤ n) (hn_high : n ≤ 2 * N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dilatedMobiusFermiCombinator 1 N t =
      -(((1 + ∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k : ℝ)) : ℂ) := by
  have hn_pos : 0 < n := by omega
  unfold dilatedMobiusFermiCombinator
  rw [Nat.div_one]
  have hcell : ∀ m ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) * fermiNymanGen ((1 * m : ℕ) : ℝ) t =
        (((moebiusReal m * fermiCellMatrix m n : ℝ)) : ℂ) := by
    intro m _
    rw [one_mul, fermiNymanGen_eq_fermiCellMatrix_on_cell hn_pos ht]
    unfold moebiusReal
    push_cast
    rfl
  rw [Finset.sum_congr rfl hcell, ← Complex.ofReal_sum]
  change -((fermiCellResponse N moebiusReal n : ℝ) : ℂ) = _
  rw [fermiCellResponse_moebiusReal_first_octave hN hn_low hn_high]

/-- **Pronic-Weighted First-Octave Tail Cell Energy of `dilatedMobiusFermiCombinator 1 N`
(`setIntegral_cell_normSq_dilatedMobiusFermiCombinator_one_first_octave`):**
For every `N ≥ 1` and every `n ∈ [N + 1, 2N]`, the `L²` energy of `dilatedMobiusFermiCombinator 1 N`
on the reciprocal cell `I_n = (1 / (n + 1), 1 / n]` equals `(1 + ∑_{k=N+1}^n μ(k))² / pronicSeq n`. -/
theorem setIntegral_cell_normSq_dilatedMobiusFermiCombinator_one_first_octave {N n : ℕ}
    (hN : 1 ≤ N) (hn_low : N + 1 ≤ n) (hn_high : n ≤ 2 * N) :
    (∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      ‖dilatedMobiusFermiCombinator 1 N t‖ ^ (2 : ℕ)) =
      (1 + ∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k) ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
  have hn_pos : 0 < n := by omega
  have hcongr : EqOn
      (fun t => ‖dilatedMobiusFermiCombinator 1 N t‖ ^ (2 : ℕ))
      (fun _ => (1 + ∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k) ^ (2 : ℕ))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    intro t ht
    dsimp only
    rw [dilatedMobiusFermiCombinator_one_first_octave_on_cell hN hn_low hn_high ht,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    setIntegral_const_on_reciprocal_cell hn_pos, smul_eq_mul]
  unfold pronicSeq
  push_cast
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
