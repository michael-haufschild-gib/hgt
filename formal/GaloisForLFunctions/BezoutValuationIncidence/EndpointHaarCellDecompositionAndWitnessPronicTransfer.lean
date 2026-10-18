import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar XI: Endpoint Haar Cell Decomposition, Dyadic Resolvent Recursion, and First-Tail-Cell Möbius Evaluation

This module completes the cellular bridge between **Bézout–Valuation Incidence Mechanics**
(`GaloisForLFunctions.BezoutValuationIncidence`), the endpoint-repaired Haar prefixes of Route PM
(`PMPowerDampedMobiusEndpointHaar`, `PMPowerDampedMobiusHaarCutoffTrace`), and the single-cell
Fermi–Nyman combinator `singleCellFermiCombinator 1 N` of Route PW-B / PM
(`WitnessCellTransferAndTopOctaveTailInequality`):

* `pmPowerDampedEndpointHaarPrefix_eq_neg_fermiCellResponse_on_cell`,
  `pmPowerDampedRepairedHaarPrefix_eq_neg_fermiCellResponse_on_cell`, &
  `setIntegral_cell_normSq_pmPowerDampedEndpointHaarPrefix`:
  On every sub-cutoff reciprocal cell `I_n = (1 / (n + 1), 1 / n]` (`1 ≤ n < N`), both
  `pmPowerDampedEndpointHaarPrefix ε N t` and `pmPowerDampedRepairedHaarPrefix ε N t` coincide with
  `pmPowerDampedFermiSource ε t = -fermiCellResponse N (pmPowerDampedRealWeight ε) n`, and have
  exact cell `L²` energy `(fermiCellResponse N (pmPowerDampedRealWeight ε) n)² / pronicSeq n`.
* `dyadicResolventCellThreshold_eq_self_add_two_mul` &
  `singleCellFermiCombinator_one_eq_add_dyadicResolvent_two`:
  For every `k ≥ 1`, `N : ℕ`, and `t : ℝ`, the top term `j = N` of `dyadicResolventCellThreshold (2 * k) N t`
  vanishes identically (`N / (2 ^ N * (2 * k)) = 0`), yielding the exact pointwise recursion
  `dyadicResolventCellThreshold k N t = dilatedMobiusFermiCombinator k N t + 2 * dyadicResolventCellThreshold (2 * k) N t`
  and, at `k = 1`, the global decomposition
  `singleCellFermiCombinator 1 N t = dilatedMobiusFermiCombinator 1 N t + dyadicResolventCellThreshold 2 N t`.
* `dyadicResolventCellThreshold_two_even_first_tail_cell_eq_one`,
  `singleCellFermiCombinator_one_even_first_tail_cell`, &
  `setIntegral_first_tail_cell_normSq_singleCellFermiCombinator_one_even`:
  At any even cutoff `N = 2M` (`M ≥ 1`), on the very first trans-horizon tail cell
  `I_{2M+1} = (1 / (2M + 2), 1 / (2M + 1)]`, every even scale `2 * 2^j` satisfies
  `(2M + 1) / (2^j * 2) = M / 2^j = (2M) / (2^j * 2)`, so `dyadicResolventCellThreshold 2 (2M) t = 1`
  cancels the constant `1` in `dilatedMobiusFermiCombinator 1 (2M) t = -(1 + μ(2M + 1))`, leaving
  `singleCellFermiCombinator 1 (2M) t = -μ(2M + 1)` with exact cell `L²` energy
  `μ(2M + 1)² / pronicSeq (2M + 1)`.
-/

/-! ## §1. Cellular Evaluation & Pronic Cell Energy of `pmPowerDampedEndpointHaarPrefix` -/

/-- On every reciprocal cell `I_n = (1 / (n + 1), 1 / n]` with `1 ≤ n < N`, `1 / t < N`. -/
theorem one_div_lt_of_mem_reciprocal_cell_of_lt {N n : ℕ} (hn : 0 < n) (hnN : n < N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    1 / t < (N : ℝ) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  have hlt1 : 1 / t < (n : ℝ) + 1 := (div_lt_iff₀ ht_pos).mpr
    (by linarith [(div_lt_iff₀ hn1_pos).mp ht.1])
  have hleN : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hnN
  exact lt_of_lt_of_le hlt1 hleN

/-- **Exact Cellular Evaluation of `pmPowerDampedEndpointHaarPrefix`
(`pmPowerDampedEndpointHaarPrefix_eq_neg_fermiCellResponse_on_cell`):**
For every `ε : ℝ`, cutoff `N : ℕ`, cell index `1 ≤ n < N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`pmPowerDampedEndpointHaarPrefix ε N t = -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ)`. -/
theorem pmPowerDampedEndpointHaarPrefix_eq_neg_fermiCellResponse_on_cell {ε : ℝ} {N n : ℕ}
    (hn : 0 < n) (hnN : n < N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    pmPowerDampedEndpointHaarPrefix ε N t =
      -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ) := by
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  have hlt : 1 / t < (N : ℝ) := one_div_lt_of_mem_reciprocal_cell_of_lt hn hnN ht
  rw [pmPowerDampedEndpointHaarPrefix_eq_source ε N ht_pos hlt,
    pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell hn hnN.le ht]

/-- **Exact Cellular Evaluation of `pmPowerDampedRepairedHaarPrefix`
(`pmPowerDampedRepairedHaarPrefix_eq_neg_fermiCellResponse_on_cell`):**
For every `ε : ℝ`, cutoff `N : ℕ`, cell index `1 ≤ n < N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`pmPowerDampedRepairedHaarPrefix ε N t = -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ)`. -/
theorem pmPowerDampedRepairedHaarPrefix_eq_neg_fermiCellResponse_on_cell {ε : ℝ} {N n : ℕ}
    (hn : 0 < n) (hnN : n < N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    pmPowerDampedRepairedHaarPrefix ε N t =
      -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ) := by
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  have hlt : 1 / t < (N : ℝ) := one_div_lt_of_mem_reciprocal_cell_of_lt hn hnN ht
  rw [pmPowerDampedRepairedHaarPrefix_eq_source ε N ht_pos hlt.le,
    pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell hn hnN.le ht]

/-- **Pronic-Weighted Cell Energy of `pmPowerDampedFermiSource`
(`setIntegral_cell_normSq_pmPowerDampedFermiSource`):**
For every `ε : ℝ` and `1 ≤ n ≤ N`, the `L²` energy of `pmPowerDampedFermiSource ε` on the
reciprocal cell `I_n = (1 / (n + 1), 1 / n]` equals
`(fermiCellResponse N (pmPowerDampedRealWeight ε) n)² / pronicSeq n`. -/
theorem setIntegral_cell_normSq_pmPowerDampedFermiSource {ε : ℝ} {N n : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    (∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      ‖pmPowerDampedFermiSource ε t‖ ^ (2 : ℕ)) =
      fermiCellResponse N (pmPowerDampedRealWeight ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
  have hcongr : EqOn
      (fun t => ‖pmPowerDampedFermiSource ε t‖ ^ (2 : ℕ))
      (fun _ => fermiCellResponse N (pmPowerDampedRealWeight ε) n ^ (2 : ℕ))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    intro t ht
    dsimp only
    rw [pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell hn hnN ht,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    setIntegral_const_on_reciprocal_cell hn, smul_eq_mul]
  unfold pronicSeq
  push_cast
  ring

/-- **Pronic-Weighted Cell Energy of `pmPowerDampedEndpointHaarPrefix`
(`setIntegral_cell_normSq_pmPowerDampedEndpointHaarPrefix`):**
For every `ε : ℝ` and `1 ≤ n < N`, the `L²` energy of `pmPowerDampedEndpointHaarPrefix ε N` on the
reciprocal cell `I_n = (1 / (n + 1), 1 / n]` equals
`(fermiCellResponse N (pmPowerDampedRealWeight ε) n)² / pronicSeq n`. -/
theorem setIntegral_cell_normSq_pmPowerDampedEndpointHaarPrefix {ε : ℝ} {N n : ℕ}
    (hn : 0 < n) (hnN : n < N) :
    (∫ t in Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ (2 : ℕ)) =
      fermiCellResponse N (pmPowerDampedRealWeight ε) n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
  have hcongr : EqOn
      (fun t => ‖pmPowerDampedEndpointHaarPrefix ε N t‖ ^ (2 : ℕ))
      (fun _ => fermiCellResponse N (pmPowerDampedRealWeight ε) n ^ (2 : ℕ))
      (Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := by
    intro t ht
    dsimp only
    rw [pmPowerDampedEndpointHaarPrefix_eq_neg_fermiCellResponse_on_cell hn hnN ht,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    setIntegral_const_on_reciprocal_cell hn, smul_eq_mul]
  unfold pronicSeq
  push_cast
  ring

/-! ## §2. Pointwise Dyadic Resolvent Recursion & Global Decomposition of `singleCellFermiCombinator 1 N` -/

/-- Whenever `N < k`, `dilatedMobiusFermiCombinator k N t = 0` identically for all `t : ℝ`. -/
theorem dilatedMobiusFermiCombinator_eq_zero_of_gt {k N : ℕ} (hgt : N < k) (t : ℝ) :
    dilatedMobiusFermiCombinator k N t = 0 := by
  unfold dilatedMobiusFermiCombinator
  rw [Nat.div_eq_of_lt hgt]
  simp

/-- **Pointwise Dyadic Resolvent Recursion (`dyadicResolventCellThreshold_eq_self_add_two_mul`):**
For every `k ≥ 1`, `N : ℕ`, and `t : ℝ`:
`dyadicResolventCellThreshold k N t = dilatedMobiusFermiCombinator k N t + 2 * dyadicResolventCellThreshold (2 * k) N t`. -/
theorem dyadicResolventCellThreshold_eq_self_add_two_mul {k : ℕ} (hk : 0 < k) (N : ℕ) (t : ℝ) :
    dyadicResolventCellThreshold k N t =
      dilatedMobiusFermiCombinator k N t +
        2 * dyadicResolventCellThreshold (2 * k) N t := by
  unfold dyadicResolventCellThreshold
  rw [Finset.sum_range_succ' _ N, Finset.sum_range_succ _ N]
  have htop : dilatedMobiusFermiCombinator (2 ^ N * (2 * k)) N t = 0 := by
    apply dilatedMobiusFermiCombinator_eq_zero_of_gt
    have hpow : N < 2 ^ N := Nat.lt_pow_self (by decide : 1 < 2)
    have h2k : 1 ≤ 2 * k := by omega
    exact lt_of_lt_of_le hpow (Nat.le_mul_of_pos_right _ (by omega))
  rw [htop, mul_zero, add_zero, pow_zero, one_mul, pow_zero, one_mul, add_comm, Finset.mul_sum]
  refine congrArg (dilatedMobiusFermiCombinator k N t + ·) (Finset.sum_congr rfl fun j _ => ?_)
  rw [show 2 ^ (j + 1) * k = 2 ^ j * (2 * k) by rw [pow_succ]; ring, pow_succ]
  ring

/-- **Global Pointwise Decomposition of `singleCellFermiCombinator 1 N`
(`singleCellFermiCombinator_one_eq_add_dyadicResolvent_two`):**
For every `N : ℕ` and `t : ℝ`, the top-octave single-cell combinator decomposes globally as
`singleCellFermiCombinator 1 N t = dilatedMobiusFermiCombinator 1 N t + dyadicResolventCellThreshold 2 N t`. -/
theorem singleCellFermiCombinator_one_eq_add_dyadicResolvent_two (N : ℕ) (t : ℝ) :
    singleCellFermiCombinator 1 N t =
      dilatedMobiusFermiCombinator 1 N t + dyadicResolventCellThreshold 2 N t := by
  unfold singleCellFermiCombinator
  rw [dyadicResolventCellThreshold_eq_self_add_two_mul zero_lt_one N t]
  ring

/-! ## §3. Exact First-Tail-Cell Möbius Evaluation (`n = 2M + 1`) of `singleCellFermiCombinator 1 (2M)` -/

/-- For every `M : ℕ` and every positive `d : ℕ`, `(2 * M + 1) / (2 * d) = M / d`. -/
theorem two_mul_add_one_div_two_mul (M d : ℕ) :
    (2 * M + 1) / (2 * d) = M / d := by
  rw [← Nat.div_div_eq_div_mul]
  have h : (2 * M + 1) / 2 = M := by omega
  rw [h]

/-- On the first trans-horizon tail cell `I_{2M+1} = (1 / (2M + 2), 1 / (2M + 1)]` beyond an even
cutoff `N = 2M`, every even-dilated combinator `dilatedMobiusFermiCombinator (2 * k) (2 * M) t`
(`k ≥ 1`) evaluates to the exact bulk dyadic step `(1_{k ≤ M} - 2 * 1_{2k ≤ M} : ℂ)`. -/
theorem dilatedMobiusFermiCombinator_two_mul_even_first_tail_cell
    {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    {t : ℝ} (ht : t ∈ Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ))) :
    dilatedMobiusFermiCombinator (2 * k) (2 * M) t =
      (((if k ≤ M then (1 : ℝ) else 0) -
        2 * (if 2 * k ≤ M then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  have hn_pos : 0 < 2 * M + 1 := by omega
  rw [dilatedMobiusFermiCombinator_eq_neg_fermiCellResponse_on_cell hn_pos ht]
  have hdivN : (2 * M) / (2 * k) = M / k := Nat.mul_div_mul_left M k (by decide : 0 < 2)
  have hdivn : (2 * M + 1) / (2 * k) = M / k := two_mul_add_one_div_two_mul M k
  rw [hdivN, hdivn, fermiCellResponse_moebiusReal_dilated_eq_of_le_two_mul hk (by omega : M ≤ 2 * M)]
  by_cases hle : k ≤ M
  · have h1 : 1 ≤ M / k := (Nat.le_div_iff_mul_le hk).mpr (by omega)
    rw [if_pos hle, sum_sieveSeq_moebiusReal_eq_one_of_le h1 le_rfl]
    push_cast
    ring
  · have hle2 : ¬ (2 * k ≤ M) := by omega
    have h0 : M / k = 0 := Nat.div_eq_of_lt (by omega)
    rw [if_neg hle, if_neg hle2, h0]
    simp

/-- **Exact Unit Evaluation of `dyadicResolventCellThreshold 2 (2M)` on the First Tail Cell `I_{2M+1}`
(`dyadicResolventCellThreshold_two_even_first_tail_cell_eq_one`):**
For every `M ≥ 1` and `t ∈ Ioc (1 / (2M + 2)) (1 / (2M + 1))`,
`dyadicResolventCellThreshold 2 (2 * M) t = 1`. -/
theorem dyadicResolventCellThreshold_two_even_first_tail_cell_eq_one
    {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t ∈ Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ))) :
    dyadicResolventCellThreshold 2 (2 * M) t = 1 := by
  unfold dyadicResolventCellThreshold
  have hterm : ∀ j ∈ Finset.range (2 * M + 1),
      ((2 : ℂ) ^ j) * dilatedMobiusFermiCombinator (2 ^ j * 2) (2 * M) t =
        (((2 : ℝ) ^ j * ((if 2 ^ j * 1 ≤ M then (1 : ℝ) else 0) -
          2 * (if 2 ^ (j + 1) * 1 ≤ M then (1 : ℝ) else 0)) : ℝ) : ℂ) := by
    intro j _
    have hj_pos : 0 < 2 ^ j := pow_pos (by decide) j
    have hstep := dilatedMobiusFermiCombinator_two_mul_even_first_tail_cell hj_pos hM ht
    rw [show 2 ^ j * 2 = 2 * 2 ^ j by ring, hstep]
    have hc1 : (2 ^ j ≤ M) ↔ (2 ^ j * 1 ≤ M) := by rw [mul_one]
    have hc2 : (2 * 2 ^ j ≤ M) ↔ (2 ^ (j + 1) * 1 ≤ M) := by
      rw [show 2 ^ (j + 1) * 1 = 2 * 2 ^ j by rw [pow_succ]; ring]
    simp only [hc1, hc2]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum,
    sum_pow_two_dyadic_step_telescope 1 M (2 * M + 1)]
  have hgt : M < 2 ^ (2 * M + 1) * 1 := by
    rw [mul_one]
    exact lt_of_le_of_lt (by omega : M ≤ 2 * M + 1) (Nat.lt_pow_self (by decide : 1 < 2))
  rw [if_pos hM, if_neg (not_le.mpr hgt)]
  simp

/-- **Pure Möbius Evaluation of `singleCellFermiCombinator 1 (2M)` on the First Tail Cell `I_{2M+1}`
(`singleCellFermiCombinator_one_even_first_tail_cell`):**
For every `M ≥ 1` and `t ∈ Ioc (1 / (2M + 2)) (1 / (2M + 1))`, the constant `1` in
`dilatedMobiusFermiCombinator 1 (2M) t = -(1 + μ(2M + 1))` is cancelled by
`dyadicResolventCellThreshold 2 (2M) t = 1`, leaving:
`singleCellFermiCombinator 1 (2 * M) t = -((moebiusReal (2 * M + 1) : ℝ) : ℂ)`. -/
theorem singleCellFermiCombinator_one_even_first_tail_cell
    {M : ℕ} (hM : 1 ≤ M)
    {t : ℝ} (ht : t ∈ Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ))) :
    singleCellFermiCombinator 1 (2 * M) t = -((moebiusReal (2 * M + 1) : ℝ) : ℂ) := by
  rw [singleCellFermiCombinator_one_eq_add_dyadicResolvent_two,
    dilatedMobiusFermiCombinator_one_first_octave_on_cell (by omega : 1 ≤ 2 * M)
      (by omega : 2 * M + 1 ≤ 2 * M + 1) (by omega : 2 * M + 1 ≤ 2 * (2 * M)) ht,
    dyadicResolventCellThreshold_two_even_first_tail_cell_eq_one hM ht,
    Finset.Icc_self, Finset.sum_singleton]
  push_cast
  ring

/-- **Exact Pronic-Weighted First-Tail-Cell Energy of `singleCellFermiCombinator 1 (2M)`
(`setIntegral_first_tail_cell_normSq_singleCellFermiCombinator_one_even`):**
For every `M ≥ 1`, the `L²` energy of `singleCellFermiCombinator 1 (2 * M)` on the first
trans-horizon tail cell `I_{2M+1} = (1 / (2M + 2), 1 / (2M + 1)]` equals
`moebiusReal (2 * M + 1) ^ 2 / pronicSeq (2 * M + 1)`. -/
theorem setIntegral_first_tail_cell_normSq_singleCellFermiCombinator_one_even
    {M : ℕ} (hM : 1 ≤ M) :
    (∫ t in Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ)),
      ‖singleCellFermiCombinator 1 (2 * M) t‖ ^ (2 : ℕ)) =
      moebiusReal (2 * M + 1) ^ (2 : ℕ) / (pronicSeq (2 * M + 1) : ℝ) := by
  have hn_pos : 0 < 2 * M + 1 := by omega
  have hcongr : EqOn
      (fun t => ‖singleCellFermiCombinator 1 (2 * M) t‖ ^ (2 : ℕ))
      (fun _ => moebiusReal (2 * M + 1) ^ (2 : ℕ))
      (Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ))) := by
    intro t ht
    dsimp only
    rw [singleCellFermiCombinator_one_even_first_tail_cell hM ht,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    setIntegral_const_on_reciprocal_cell hn_pos, smul_eq_mul]
  unfold pronicSeq
  push_cast
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
