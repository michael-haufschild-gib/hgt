import GaloisForLFunctions.BezoutValuationIncidence.FermiCellJumpReciprocityAndPronicTailBridge

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar IX: Dilated Cell-Matrix Scaling, Second-Octave Jump Switching, and Two-Octave Tail Bridge

This module extends the Fermi–Nyman cellular jump reciprocity of Pillar VI across **all dilation
scales `k ≥ 1`** and into the **second trans-horizon octave `2N + 1 ≤ n ≤ 3N`**, connecting the
multi-octave step combinators `dilatedMobiusFermiCombinator k N` and `dyadicResolventCellThreshold k N`
of Route PM / PW-B (`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity`) to `2`-adic valuation
switching and the Bézout successor correlation form:

* `fermiCellMatrix_mul_left` & `dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell`:
  For all `k, d, n : ℕ`, `fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)`. Consequently, on
  every reciprocal cell `I_n = (1 / (n + 1), 1 / n]` (`n ≥ 1`), the dilated Möbius combinator
  `dilatedMobiusFermiCombinator k N` evaluates to `-fermiCellResponse (N / k) moebiusReal (n / k)`.
* `sum_sieveSeq_moebiusReal_half_eq_ite_of_le_two_mul`,
  `dilatedMobiusFermiCombinator_eq_sieveSeq_sub_two_ite_on_cell`, &
  `dyadicResolventCellThreshold_eq_threshold_add_discrepancy_of_le_two_mul`:
  Throughout both the sub-horizon bulk and the entire first trans-horizon octave `1 ≤ n ≤ 2N`, the
  dyadic half-scale sum `∑_{r=1}^{n/(2k)} s_{N/k,μ}(r)` equals the exact indicator `1_{2k ≤ n}` for
  every scale `k ≥ 1`. Thus the binary telescoping of `dyadicResolventCellThreshold k N` extends
  through `n ≤ 2N`, decomposing `dyadicResolventCellThreshold k N t` on `I_n` into the exact step
  threshold `1_{k ≤ n}` plus the dyadic sum of trans-horizon `sieveSeq` discrepancies.
* `fermiCellResponse_moebiusReal_jump_second_octave` & the Four-Way `2`-Adic Jump Table:
  In the second trans-horizon octave `2N + 1 ≤ m ≤ 3N`, the half-index `m / 2` lies in the first
  trans-horizon octave `[N + 1, 2N]` where `s_{N,μ}(m / 2) = -μ(m / 2)`. Combining this with
  second-octave reciprocity `s_{N,μ}(m) = -μ(m) - 1_{2 ∣ m} μ(m / 2)` flips the relative sign of
  the dyadic half-scale contribution:
  `fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) = μ(m) - 1_{2 ∣ m} μ(m / 2)`.
  Across the four `2`-adic valuation sectors on `m ∈ [2N + 1, 3N]`:
  - `v₂(m) = 0` (`2 ∤ m`): jump `= μ(m)`,
  - `v₂(m) = 1` (`m = 2u`, `u` odd, `log 6` sector): `s_{N,μ}(2u) = 0`, while the cell jump is
    amplified to `-2 μ(u)`,
  - `v₂(m) = 2` (`m = 4u`, `u` odd, `log 4` sector): `μ(4u) = 0`, while the cell jump equals `+μ(u)`,
  - `v₂(m) ≥ 3` (`8 ∣ m`): jump `= 0`.
* `fermiCellResponse_moebiusReal_first_and_second_octave`,
  `dilatedMobiusFermiCombinator_one_first_and_second_octave_on_cell`, &
  `sum_sieveSeq_moebiusReal_mul_succ_eq_sum_first_octave_jumps`:
  Across the combined first and second trans-horizon octaves `N + 1 ≤ n ≤ 3N`,
  `fermiCellResponse N moebiusReal n = 1 + ∑_{k=N+1}^n μ(k) - ∑_{j=N+1}^{n/2} μ(j)`. Moreover, for
  `N ≥ 2` and `N + 1 ≤ M ≤ 2N`, the sub-horizon and horizon-boundary successor correlations of
  `sieveSeq N moebiusReal` vanish identically, so the full prefix Bézout correlation
  `∑_{k=1}^{M-1} s_{N,μ}(k) s_{N,μ}(k + 1)` equals the trans-horizon cell-jump correlation
  `∑_{m=N+1}^{M-1} ΔfermiCellResponse(m) ΔfermiCellResponse(m + 1) = ∑_{m=N+1}^{M-1} μ(m) μ(m + 1)`.
-/

/-! ## §1. Exact Dilated Cell-Matrix Scaling and Multi-Scale Cell Evaluation -/

/-- **Exact Dilated Cell-Matrix Scaling Law (`fermiCellMatrix_mul_left`):**
For every dilation factor `k : ℕ`, generator index `d : ℕ`, and cell index `n : ℕ`:
`fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)`. -/
theorem fermiCellMatrix_mul_left (k d n : ℕ) :
    fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k) := by
  unfold fermiCellMatrix
  have h1 : n / (k * d) = (n / k) / d := (Nat.div_div_eq_div_mul n k d).symm
  have h2 : n / (2 * (k * d)) = (n / k) / (2 * d) := by
    rw [show 2 * (k * d) = k * (2 * d) by ring]
    exact (Nat.div_div_eq_div_mul n k (2 * d)).symm
  rw [h1, h2]

/-- At cell index `n = 0`, `fermiCellResponse N c 0 = 0`. -/
theorem fermiCellResponse_zero_right (N : ℕ) (c : ℕ → ℝ) :
    fermiCellResponse N c 0 = 0 := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix]
  simp

/-- At sieve cutoff `N = 0`, `fermiCellResponse 0 c n = 0`. -/
theorem fermiCellResponse_zero_left (c : ℕ → ℝ) (n : ℕ) :
    fermiCellResponse 0 c n = 0 := by
  unfold fermiCellResponse
  simp

/-- **Universal Cell Evaluation of `dilatedMobiusFermiCombinator` via `fermiCellResponse`
(`dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell`):**
For every dilation scale `k : ℕ`, cutoff `N : ℕ`, cell index `n ≥ 1`, and
`t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`dilatedMobiusFermiCombinator k N t = -((fermiCellResponse (N / k) moebiusReal (n / k) : ℝ) : ℂ)`. -/
theorem dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell {k N n : ℕ}
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dilatedMobiusFermiCombinator k N t =
      -((fermiCellResponse (N / k) moebiusReal (n / k) : ℝ) : ℂ) := by
  unfold dilatedMobiusFermiCombinator fermiCellResponse
  have hcell : ∀ m ∈ Finset.Icc 1 (N / k),
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) * fermiNymanGen ((k * m : ℕ) : ℝ) t =
        (((moebiusReal m * fermiCellMatrix m (n / k) : ℝ)) : ℂ) := by
    intro m _
    rw [fermiNymanGen_eq_fermiCellMatrix_on_cell hn ht, fermiCellMatrix_mul_left]
    unfold moebiusReal
    push_cast
    rfl
  rw [Finset.sum_congr rfl hcell, ← Complex.ofReal_sum]

/-- **Two-Octave Stability of the Dyadic Half-Scale Prefix Sum
(`sum_sieveSeq_moebiusReal_half_eq_ite_of_le_two_mul`):**
For every scale `k ≥ 1`, cutoff `N : ℕ`, and cell index `n ≤ 2N` (covering both the sub-horizon
bulk and the entire first trans-horizon octave), the half-scale prefix sum
`∑_{r=1}^{n/(2k)} s_{N/k,μ}(r)` equals `if 2 * k ≤ n then 1 else 0`. -/
theorem sum_sieveSeq_moebiusReal_half_eq_ite_of_le_two_mul {k N n : ℕ}
    (hk : 0 < k) (hn2N : n ≤ 2 * N) :
    (∑ r ∈ Finset.Icc 1 (n / (2 * k)), sieveSeq (N / k) moebiusReal r) =
      if 2 * k ≤ n then 1 else 0 := by
  have h2k : 0 < 2 * k := by omega
  by_cases hle : 2 * k ≤ n
  · rw [if_pos hle]
    have h1 : 1 ≤ n / (2 * k) := (Nat.le_div_iff_mul_le h2k).mpr (by omega)
    have hdiv : n / (2 * k) ≤ N / k := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right (by omega : n / 2 ≤ N)
    exact sum_sieveSeq_moebiusReal_eq_one_of_le h1 hdiv
  · rw [if_neg hle]
    have h0 : n / (2 * k) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]
    simp

/-- For every `k ≥ 1` and `n ≤ 2N`, `fermiCellResponse (N / k) moebiusReal (n / k)` equals
`2 * 1_{2k ≤ n} - ∑_{r=1}^{n/k} s_{N/k,μ}(r)`. -/
theorem fermiCellResponse_moebiusReal_dilated_eq_of_le_two_mul {k N n : ℕ}
    (hk : 0 < k) (hn2N : n ≤ 2 * N) :
    fermiCellResponse (N / k) moebiusReal (n / k) =
      2 * (if 2 * k ≤ n then (1 : ℝ) else 0) -
        ∑ r ∈ Finset.Icc 1 (n / k), sieveSeq (N / k) moebiusReal r := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix]
  have hdiv : (n / k) / 2 = n / (2 * k) := by
    rw [Nat.div_div_eq_div_mul, show k * 2 = 2 * k by ring]
  rw [hdiv, sum_sieveSeq_moebiusReal_half_eq_ite_of_le_two_mul hk hn2N]

/-- **Two-Octave Formula for `dilatedMobiusFermiCombinator`
(`dilatedMobiusFermiCombinator_eq_sieveSeq_sub_two_ite_on_cell`):**
For every `k ≥ 1`, `1 ≤ n ≤ 2N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`dilatedMobiusFermiCombinator k N t = (∑_{r=1}^{n/k} s_{N/k,μ}(r) - 2 * 1_{2k ≤ n} : ℂ)`. -/
theorem dilatedMobiusFermiCombinator_eq_sieveSeq_sub_two_ite_on_cell {k N n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hn2N : n ≤ 2 * N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dilatedMobiusFermiCombinator k N t =
      (((∑ r ∈ Finset.Icc 1 (n / k), sieveSeq (N / k) moebiusReal r) -
        2 * (if 2 * k ≤ n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  rw [dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell hn ht,
    fermiCellResponse_moebiusReal_dilated_eq_of_le_two_mul hk hn2N]
  push_cast
  ring

/-- **Two-Octave Threshold + Discrepancy Decomposition of `dyadicResolventCellThreshold`
(`dyadicResolventCellThreshold_eq_threshold_add_discrepancy_of_le_two_mul`):**
For every `k ≥ 1`, `1 ≤ n ≤ 2N` (including the entire first trans-horizon octave `N + 1 ≤ n ≤ 2N`),
and `t ∈ Ioc (1 / (n + 1)) (1 / n)`, `dyadicResolventCellThreshold k N t` decomposes into the
exact step threshold `1_{k ≤ n}` plus the dyadic sum of trans-horizon `sieveSeq` discrepancies:
`dyadicResolventCellThreshold k N t = 1_{k ≤ n} + ∑_{j=0}^N 2^j (∑_{r=1}^{n/(2^j k)} s_{N/(2^j k),μ}(r) - 1_{2^j k ≤ n})`. -/
theorem dyadicResolventCellThreshold_eq_threshold_add_discrepancy_of_le_two_mul
    {k N n : ℕ} (hk : 0 < k) (hn : 0 < n) (hn2N : n ≤ 2 * N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dyadicResolventCellThreshold k N t =
      (((if k ≤ n then (1 : ℝ) else 0) +
        ∑ j ∈ Finset.range (N + 1),
          (2 : ℝ) ^ j * ((∑ r ∈ Finset.Icc 1 (n / (2 ^ j * k)),
            sieveSeq (N / (2 ^ j * k)) moebiusReal r) -
              if 2 ^ j * k ≤ n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  unfold dyadicResolventCellThreshold
  have hterm : ∀ j ∈ Finset.range (N + 1),
      ((2 : ℂ) ^ j) * dilatedMobiusFermiCombinator (2 ^ j * k) N t =
        (((2 : ℝ) ^ j * ((if 2 ^ j * k ≤ n then (1 : ℝ) else 0) -
          2 * (if 2 ^ (j + 1) * k ≤ n then (1 : ℝ) else 0)) +
        (2 : ℝ) ^ j * ((∑ r ∈ Finset.Icc 1 (n / (2 ^ j * k)),
          sieveSeq (N / (2 ^ j * k)) moebiusReal r) -
            if 2 ^ j * k ≤ n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    intro j _
    have h2jk : 0 < 2 ^ j * k := Nat.mul_pos (pow_pos (by decide) j) hk
    rw [dilatedMobiusFermiCombinator_eq_sieveSeq_sub_two_ite_on_cell h2jk hn hn2N ht,
      show 2 * (2 ^ j * k) = 2 ^ (j + 1) * k by ring]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, Finset.sum_add_distrib,
    sum_pow_two_dyadic_step_telescope k n (N + 1)]
  have hgt : n < 2 ^ (N + 1) * k := by
    have hpow : N < 2 ^ N := Nat.lt_pow_self (by decide : 1 < 2)
    have h2pow : 2 * N < 2 ^ (N + 1) := by
      rw [Nat.pow_succ]
      omega
    exact lt_of_le_of_lt hn2N (lt_of_lt_of_le h2pow (Nat.le_mul_of_pos_right _ hk))
  rw [if_neg (not_le.mpr hgt)]
  push_cast
  ring

/-! ## §2. Second Trans-Horizon Octave (`2N + 1 ≤ m ≤ 3N`) Jump Law & Four-Way `2`-Adic Switching -/

/-- **Exact Inter-Cell Jump Law in the Second Trans-Horizon Octave
(`fermiCellResponse_moebiusReal_jump_second_octave`):**
For every `m ∈ [2N + 1, 3N]`, the half-index `m / 2` lies in the first trans-horizon octave
`[N + 1, 2N]` where `s_{N,μ}(m / 2) = -μ(m / 2)`. Combining this with second-octave reciprocity
`s_{N,μ}(m) = -μ(m) - 1_{2 ∣ m} μ(m / 2)` flips the sign of the dyadic half-scale contribution:
`fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) = μ(m) - 1_{2 ∣ m} μ(m / 2)`. -/
theorem fermiCellResponse_moebiusReal_jump_second_octave {N m : ℕ}
    (hm_low : 2 * N + 1 ≤ m) (hm_high : m ≤ 3 * N) :
    fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) =
      moebiusReal m - if 2 ∣ m then moebiusReal (m / 2) else 0 := by
  have hm_eq : m - 1 + 1 = m := by omega
  have hstep := fermiCellResponse_succ_sub_eq N moebiusReal (m - 1)
  rw [hm_eq] at hstep
  rw [hstep, sieveSeq_moebiusReal_second_octave hm_low hm_high]
  by_cases h2 : 2 ∣ m
  · simp only [if_pos h2]
    have hu_low : N + 1 ≤ m / 2 := by obtain ⟨u, rfl⟩ := h2; omega
    have hu_high : m / 2 ≤ 2 * N := by omega
    rw [sieveSeq_moebiusReal_first_octave hu_low hu_high]
    ring
  · simp only [if_neg h2]
    ring

/-- **Second-Octave Jump Sector 1 (`v₂(m) = 0`, Odd Indices):**
At every odd index `m ∈ [2N + 1, 3N]`, the inter-cell jump of `fermiCellResponse N moebiusReal`
is `moebiusReal m`. -/
theorem fermiCellResponse_moebiusReal_jump_second_octave_of_odd {N m : ℕ}
    (hodd : ¬ (2 ∣ m)) (hm_low : 2 * N + 1 ≤ m) (hm_high : m ≤ 3 * N) :
    fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) =
      moebiusReal m := by
  rw [fermiCellResponse_moebiusReal_jump_second_octave hm_low hm_high, if_neg hodd, sub_zero]

/-- **Second-Octave Jump Sector 2 (`v₂(m) = 1`, `m = 2u` with `u` Odd, `log 6` Sector):**
For every odd `u` (`Nat.Coprime 2 u`) with `2u ∈ [2N + 1, 3N]`, while `sieveSeq N moebiusReal (2u) = 0`
vanishes identically, the Fermi–Nyman cell jump at `2u` is amplified to `-2 * moebiusReal u`. -/
theorem fermiCellResponse_moebiusReal_jump_second_octave_two_mul_odd {N u : ℕ}
    (hodd : Nat.Coprime 2 u) (hm_low : 2 * N + 1 ≤ 2 * u) (hm_high : 2 * u ≤ 3 * N) :
    sieveSeq N moebiusReal (2 * u) = 0 ∧
      fermiCellResponse N moebiusReal (2 * u) - fermiCellResponse N moebiusReal (2 * u - 1) =
        -2 * moebiusReal u := by
  refine ⟨sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero hodd hm_low hm_high, ?_⟩
  rw [fermiCellResponse_moebiusReal_jump_second_octave hm_low hm_high,
    if_pos (dvd_mul_right 2 u), Nat.mul_div_cancel_left u (by decide : 0 < 2)]
  unfold moebiusReal
  have hmul : μ (2 * u) = μ 2 * μ u :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hodd
  rw [hmul, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

/-- **Second-Octave Jump Sector 3 (`v₂(m) = 2`, `m = 4u` with `u` Odd, `log 4` Sector):**
For every odd `u` (`Nat.Coprime 2 u`) with `4u ∈ [2N + 1, 3N]`, while `moebiusReal (4u) = 0`,
the Fermi–Nyman cell jump at `4u` equals `+moebiusReal u`. -/
theorem fermiCellResponse_moebiusReal_jump_second_octave_four_mul_odd {N u : ℕ}
    (hodd : Nat.Coprime 2 u) (hm_low : 2 * N + 1 ≤ 4 * u) (hm_high : 4 * u ≤ 3 * N) :
    moebiusReal (4 * u) = 0 ∧
      fermiCellResponse N moebiusReal (4 * u) - fermiCellResponse N moebiusReal (4 * u - 1) =
        moebiusReal u := by
  obtain ⟨hmu4u, _⟩ := sieveSeq_moebiusReal_second_octave_four_mul_odd hodd hm_low hm_high
  refine ⟨hmu4u, ?_⟩
  have h2dvd : 2 ∣ 4 * u := ⟨2 * u, by ring⟩
  have hdiv : 4 * u / 2 = 2 * u := by omega
  rw [fermiCellResponse_moebiusReal_jump_second_octave hm_low hm_high, hmu4u,
    if_pos h2dvd, hdiv]
  unfold moebiusReal
  have hmul : μ (2 * u) = μ 2 * μ u :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hodd
  rw [hmul, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

/-- **Second-Octave Jump Sector 4 (`v₂(m) ≥ 3`, `8 ∣ m`):**
At every multiple of `8` in `[2N + 1, 3N]`, both `m` and `m / 2` are divisible by `4`, so the
Fermi–Nyman cell jump vanishes identically. -/
theorem fermiCellResponse_moebiusReal_jump_second_octave_of_eight_dvd {N m : ℕ}
    (h8 : 8 ∣ m) (hm_low : 2 * N + 1 ≤ m) (hm_high : m ≤ 3 * N) :
    fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) = 0 := by
  rcases h8 with ⟨u, rfl⟩
  have h2 : 2 ∣ 8 * u := ⟨4 * u, by ring⟩
  have hdiv : 8 * u / 2 = 4 * u := by omega
  have hnot_sq8 : ¬ Squarefree (8 * u) := by
    intro hsq
    have h4 : Squarefree 4 := hsq.squarefree_of_dvd ⟨2 * u, by ring⟩
    exact absurd (h4 2 (by norm_num : 2 * 2 ∣ 4)) (by decide)
  have hnot_sq4 : ¬ Squarefree (4 * u) := by
    intro hsq
    have h4 : Squarefree 4 := hsq.squarefree_of_dvd (dvd_mul_right 4 u)
    exact absurd (h4 2 (by norm_num : 2 * 2 ∣ 4)) (by decide)
  rw [fermiCellResponse_moebiusReal_jump_second_octave hm_low hm_high, if_pos h2, hdiv]
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sq8,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sq4]
  norm_num

/-! ## §3. Unified Two-Octave Cumulative Formula & Trans-Horizon Jump-Correlation Bridge -/

/-- **Unified First-and-Second Trans-Horizon Octave Formula for `fermiCellResponse N moebiusReal`
(`fermiCellResponse_moebiusReal_first_and_second_octave`):**
For every `N ≥ 1` and every cell index `n ∈ [N + 1, 3N]` across both the first and second
trans-horizon octaves:
`fermiCellResponse N moebiusReal n = 1 + ∑_{k=N+1}^n μ(k) - ∑_{j=N+1}^{n/2} μ(j)`. -/
theorem fermiCellResponse_moebiusReal_first_and_second_octave {N n : ℕ}
    (hN : 1 ≤ N) (hn_low : N + 1 ≤ n) (hn_high : n ≤ 3 * N) :
    fermiCellResponse N moebiusReal n =
      1 + (∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k) -
        ∑ j ∈ Finset.Icc (N + 1) (n / 2), moebiusReal j := by
  by_cases hn2N : n ≤ 2 * N
  · rw [fermiCellResponse_moebiusReal_first_octave hN hn_low hn2N]
    have hhalf : n / 2 ≤ N := by omega
    have hemp : Finset.Icc (N + 1) (n / 2) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty, sub_zero]
  · have hgt : 2 * N < n := lt_of_not_ge hn2N
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = 2 * N + d := ⟨n - 2 * N, by omega⟩
    clear hn_low hn2N hgt
    induction d with
    | zero =>
      simp only [add_zero]
      rw [fermiCellResponse_moebiusReal_first_octave hN (by omega) le_rfl]
      have hdiv : 2 * N / 2 = N := by omega
      rw [hdiv, Finset.Icc_eq_empty (by omega : ¬ (N + 1 ≤ N)), Finset.sum_empty, sub_zero]
    | succ d ih =>
      have hd_high : 2 * N + d ≤ 3 * N := by omega
      have hih := ih hd_high
      have hm_low : 2 * N + 1 ≤ 2 * N + (d + 1) := by omega
      have hjump := fermiCellResponse_moebiusReal_jump_second_octave hm_low hn_high
      have hsub : 2 * N + (d + 1) - 1 = 2 * N + d := by omega
      rw [hsub] at hjump
      have hfull_split :
          Finset.Icc (N + 1) (2 * N + (d + 1)) =
            insert (2 * N + (d + 1)) (Finset.Icc (N + 1) (2 * N + d)) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hfull_not : 2 * N + (d + 1) ∉ Finset.Icc (N + 1) (2 * N + d) := by
        simp only [Finset.mem_Icc]; omega
      rw [hfull_split, Finset.sum_insert hfull_not]
      have hhalf_step := succ_div_two_eq (2 * N + d)
      rw [show 2 * N + d + 1 = 2 * N + (d + 1) by omega] at hhalf_step
      by_cases h2 : 2 ∣ (2 * N + (d + 1))
      · rw [if_pos h2] at hjump hhalf_step
        have hhalf_split :
            Finset.Icc (N + 1) ((2 * N + (d + 1)) / 2) =
              insert ((2 * N + (d + 1)) / 2) (Finset.Icc (N + 1) ((2 * N + d) / 2)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hhalf_not : (2 * N + (d + 1)) / 2 ∉ Finset.Icc (N + 1) ((2 * N + d) / 2) := by
          simp only [Finset.mem_Icc]; omega
        rw [hhalf_split, Finset.sum_insert hhalf_not]
        linarith
      · rw [if_neg h2] at hjump hhalf_step
        have hhalf_eq : (2 * N + (d + 1)) / 2 = (2 * N + d) / 2 := by omega
        rw [hhalf_eq]
        linarith

/-- **Continuous Evaluation of `dilatedMobiusFermiCombinator 1 N` Across Both Trans-Horizon Octaves
(`dilatedMobiusFermiCombinator_one_first_and_second_octave_on_cell`):**
For every `N ≥ 1`, every cell index `n ∈ [N + 1, 3N]`, and every `t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`dilatedMobiusFermiCombinator 1 N t = -((1 + ∑_{k=N+1}^n μ(k) - ∑_{j=N+1}^{n/2} μ(j) : ℝ) : ℂ)`. -/
theorem dilatedMobiusFermiCombinator_one_first_and_second_octave_on_cell {N n : ℕ}
    (hN : 1 ≤ N) (hn_low : N + 1 ≤ n) (hn_high : n ≤ 3 * N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dilatedMobiusFermiCombinator 1 N t =
      -(((1 + (∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k) -
        ∑ j ∈ Finset.Icc (N + 1) (n / 2), moebiusReal j : ℝ)) : ℂ) := by
  have hn_pos : 0 < n := by omega
  rw [dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell hn_pos ht,
    Nat.div_one, Nat.div_one,
    fermiCellResponse_moebiusReal_first_and_second_octave hN hn_low hn_high]

/-- **Sub-Horizon & Boundary Vanishing of `sieveSeq N moebiusReal` Successor Products (`N ≥ 2`):**
For every `N ≥ 2` and `1 ≤ k ≤ N`, `sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1) = 0`. -/
theorem sieveSeq_moebiusReal_mul_succ_eq_zero_of_le {N k : ℕ}
    (hN : 2 ≤ N) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1) = 0 := by
  by_cases hk : k = 1
  · subst hk
    rw [sieveSeq_moebiusReal_eq_ite_of_le (by decide : 1 ≤ 2) hN]
    simp
  · rw [sieveSeq_moebiusReal_eq_ite_of_le hk1 hkN, if_neg hk, zero_mul]

/-- **Exact Concentration of the Prefix Bézout Correlation in Trans-Horizon Fermi–Nyman Jumps
(`sum_sieveSeq_moebiusReal_mul_succ_eq_sum_first_octave_jumps`):**
For every `N ≥ 2` and `N + 1 ≤ M ≤ 2N`, the complete prefix Bézout correlation
`∑_{k=1}^{M-1} s_{N,μ}(k) s_{N,μ}(k + 1)` is concentrated 100% in the trans-horizon cell jumps
`m ∈ [N + 1, M - 1]` and equals both the Möbius successor sum `∑_{m=N+1}^{M-1} μ(m) μ(m + 1)`
and the consecutive Fermi–Nyman cell-jump correlation:
`∑_{m=N+1}^{M-1} (fermiCellResponse N μ m - fermiCellResponse N μ (m - 1)) * (fermiCellResponse N μ (m + 1) - fermiCellResponse N μ m)`. -/
theorem sum_sieveSeq_moebiusReal_mul_succ_eq_sum_first_octave_jumps {N M : ℕ}
    (hN : 2 ≤ N) (hM_low : N + 1 ≤ M) (hM_high : M ≤ 2 * N) :
    (∑ k ∈ Finset.Icc 1 (M - 1),
      sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1)) =
      ∑ m ∈ Finset.Icc (N + 1) (M - 1),
        (fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1)) *
          (fermiCellResponse N moebiusReal (m + 1) - fermiCellResponse N moebiusReal m) ∧
    (∑ k ∈ Finset.Icc 1 (M - 1),
      sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1)) =
      ∑ m ∈ Finset.Icc (N + 1) (M - 1), moebiusReal m * moebiusReal (m + 1) := by
  have hsplit : Finset.Icc 1 (M - 1) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (M - 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (M - 1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have hzero : (∑ k ∈ Finset.Icc 1 N,
      sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_moebiusReal_mul_succ_eq_zero_of_le hN hk1 hkN
  rw [hsplit, Finset.sum_union hdisj, hzero, zero_add]
  constructor
  · refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact (fermiCellResponse_moebiusReal_jump_mul_succ_first_octave hN hm1 (by omega)).1.symm
  · refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact sieveSeq_moebiusReal_mul_succ_first_octave hm1 (by omega)

end
end GaloisForLFunctions.BezoutValuationIncidence
