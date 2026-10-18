import GaloisForLFunctions.BezoutValuationIncidence.ShortHorizonPronicDiscrepancyAndVonMangoldtDuality

/-!
# Truncated Non-Periodic Pronic Gram Matrix and Finite-Horizon Von Mangoldt Approximation

A foundational structural obstacle in analytic number theory ("Wall 1") is that exact orthogonality
of divisor-summed sieve modes `d ∣ n` for `d ≤ N` classically requires averaging over the common
period `L_N = lcm(1, ..., N) = e^{(1+o(1))N}`, which is exponentially larger than any polynomial
observation window `H = N^A`.

In `ShortHorizonPronicDiscrepancyAndVonMangoldtDuality.lean`, we showed that replacing uniform
period averaging by the non-periodic Bézout pronic measure `1 / pronicSeq M = 1 / (M * (M + 1))`
over `M ≥ 1` transforms the Selberg multiples coordinates `selbergMultiplesCoord N c e` into the
von Mangoldt prime-power functional `-∑_{e=2}^N Λ(e) Y_{N,c}(e)` and evaluates the squared
discrepancy series as the quadratic form of the non-periodic Ramanujan Gram matrix
`pmRamanujanPrimitiveGram p q`.

This module establishes the **finite-horizon truncation calculus** at any finite cutoff `H : ℕ`
(for example, polynomial horizons `H = N^2` or the sub-period horizon `H = N - 1`), proving explicit
`O(1 / (H + 1))` remainder bounds with **no reference to `L_N = lcm(1, ..., N)` or `N!`**:

1. **Master Pronic Tail & Finite-Horizon Remainder Theorem
   (`hasSum_one_div_pronicSeq_shift`, `tsum_one_div_pronicSeq_shift`,
   `abs_tsum_div_pronicSeq_sub_sum_Icc_le`):**
   - For every horizon `H : ℕ`, the shifted pronic tail satisfies the exact telescoping identity
     $$\sum_{k=0}^\infty \frac{1}{\operatorname{pronicSeq}(H + 1 + k)} = \frac{1}{H + 1}.$$
   - For every sequence `g : ℕ → ℝ` bounded uniformly by `|g M| ≤ B`, the finite-horizon pronic
     partial sum over `1 ≤ M ≤ H` approximates the infinite pronic series within `B / (H + 1)`:
     $$\left|\sum_{M=1}^\infty \frac{g(M)}{\operatorname{pronicSeq}(M)}
       - \sum_{M=1}^H \frac{g(M)}{\operatorname{pronicSeq}(M)}\right| \le \frac{B}{H + 1}.$$

2. **Finite-Horizon Von Mangoldt Approximation
   (`abs_sum_Icc_pmRamanujanPrimitive_div_pronicSeq_add_vonMangoldt_le`,
   `abs_sum_Icc_sievePrefixDiscrepancy_div_pronicSeq_add_vonMangoldt_sum_le`,
   `abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_add_vonMangoldt_le`):**
   - For every modulus `q > 1` and horizon `H : ℕ`:
     $$\left|\sum_{M=1}^H \frac{\operatorname{Re}(\operatorname{pmRamanujanPrimitive}(q, M))}{\operatorname{pronicSeq}(M)}
       + \Lambda(q)\right| \le \frac{\operatorname{pmRamanujanPrimitiveBound}(q)}{H + 1}.$$
   - For every sieve cutoff `N`, weight `c`, and finite horizon `H : ℕ`:
     $$\left|\sum_{M=1}^H \frac{\operatorname{sievePrefixDiscrepancy}(N, M, c)}{\operatorname{pronicSeq}(M)}
       + \sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)\right|
       \le \frac{\sqrt{\operatorname{sieveVariance}(N, c)\cdot \operatorname{sievePeriodFreeDualCeiling}(N)}}{H + 1}.$$

3. **Truncated Non-Periodic Pronic Gram Matrix & Quadratic Form Remainder Bounds
   (`truncatedPronicGram`, `truncatedSievePronicDiscrepancyGramForm`,
   `abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le`,
   `sievePronicDiscrepancyGramForm_sub_truncated_le`,
   `abs_truncatedPronicGram_prime_pair_defect_le`):**
   - The truncated Gram matrix `truncatedPronicGram H p q = ∑_{M=1}^H pmRamanujanPrimitiveGramTerm p q M`
     approximates `pmRamanujanPrimitiveGram p q` within
     `(pmRamanujanPrimitiveBound p * pmRamanujanPrimitiveBound q) / (H + 1)`.
   - The truncated quadratic form `truncatedSievePronicDiscrepancyGramForm N H c` is monotonically
     non-decreasing in `H`, positive semi-definite (`≥ 0`), and approximates
     `sievePronicDiscrepancyGramForm N c` within
     `(sieveVariance N c * sievePeriodFreeDualCeiling N) / (H + 1)`.
   - At any finite horizon `H`, the prime-dilated Gram recurrence defect on `{q, p * q}` and
     `{r, p * r}` (`¬ p ∣ q`, `¬ p ∣ r`) decays explicitly as `O(1 / (H + 1))`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Master Pronic Tail & Finite-Horizon Remainder Calculus -/

/-- At `M = 0`, `pronicSeq 0 = 0`, so division by `(pronicSeq 0 : ℝ)` vanishes identically. -/
theorem div_cast_pronicSeq_zero (x : ℝ) :
    x / (pronicSeq 0 : ℝ) = 0 := by
  simp [pronicSeq]

/-- Converting a finite sum over `Finset.Icc 1 H` into `Finset.range (H + 1)` when the `0`-th term
vanishes. -/
theorem sum_Icc_one_eq_sum_range_succ_of_zero {f : ℕ → ℝ} (hf0 : f 0 = 0) (H : ℕ) :
    (∑ M ∈ Finset.Icc 1 H, f M) = ∑ M ∈ Finset.range (H + 1), f M := by
  induction H with
  | zero =>
    simp [hf0]
  | succ H ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1),
      Finset.sum_range_succ (f := f) (n := H + 1), ih]

/-- **Exact Shifted Pronic Tail Series (`hasSum_one_div_pronicSeq_shift`):**
For every finite horizon `H : ℕ`, the shifted pronic reciprocal series starting at `H + 1` has
exact sum `1 / (H + 1)`. -/
theorem hasSum_one_div_pronicSeq_shift (H : ℕ) :
    HasSum (fun k : ℕ => 1 / (pronicSeq (H + 1 + k) : ℝ)) (1 / ((H : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have htel := GaloisForLFunctions.hasSum_one_div_shift_mul_succ hpos
  refine htel.congr_fun fun k => ?_
  rw [cast_pronicSeq_eq (H + 1 + k)]
  push_cast
  ring

/-- **Shifted Pronic Tail Evaluation (`tsum_one_div_pronicSeq_shift`):**
For every `H : ℕ`, `∑' k : ℕ, 1 / pronicSeq (H + 1 + k) = 1 / (H + 1)`. -/
theorem tsum_one_div_pronicSeq_shift (H : ℕ) :
    (∑' k : ℕ, 1 / (pronicSeq (H + 1 + k) : ℝ)) = 1 / ((H : ℝ) + 1) :=
  (hasSum_one_div_pronicSeq_shift H).tsum_eq

/-- Summability of `g M / pronicSeq M` for any uniformly bounded sequence `g : ℕ → ℝ`. -/
theorem summable_div_pronicSeq_of_bounded {g : ℕ → ℝ} {B : ℝ}
    (hB : ∀ M : ℕ, |g M| ≤ B) :
    Summable (fun M : ℕ => g M / (pronicSeq M : ℝ)) := by
  have hB0 : 0 ≤ B := (abs_nonneg (g 0)).trans (hB 0)
  have hmajor : Summable (fun M : ℕ => B * (1 / ((M : ℝ) * ((M : ℝ) + 1)))) :=
    hasSum_pm_reciprocal_weight.summable.mul_left B
  refine Summable.of_norm_bounded hmajor fun M => ?_
  rw [cast_pronicSeq_eq M, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ (M : ℝ) * ((M : ℝ) + 1))]
  calc
    |g M| / ((M : ℝ) * ((M : ℝ) + 1))
      ≤ B / ((M : ℝ) * ((M : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (hB M) (by positivity)
    _ = B * (1 / ((M : ℝ) * ((M : ℝ) + 1))) := by ring

/-- **Exact Tail Decomposition of Pronic-Weighted Series (`tsum_div_pronicSeq_sub_sum_Icc_eq`):**
For every uniformly bounded sequence `g : ℕ → ℝ` and every finite horizon `H : ℕ`, the remainder
between the infinite pronic series and the finite partial sum over `1 ≤ M ≤ H` equals the shifted
tail series starting at `H + 1`. -/
theorem tsum_div_pronicSeq_sub_sum_Icc_eq {g : ℕ → ℝ} {B : ℝ}
    (hB : ∀ M : ℕ, |g M| ≤ B) (H : ℕ) :
    (∑' M : ℕ, g M / (pronicSeq M : ℝ)) -
      (∑ M ∈ Finset.Icc 1 H, g M / (pronicSeq M : ℝ)) =
      ∑' k : ℕ, g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ) := by
  have hs : Summable (fun M : ℕ => g M / (pronicSeq M : ℝ)) :=
    summable_div_pronicSeq_of_bounded hB
  have hsplit := (hs.sum_add_tsum_nat_add (H + 1)).symm
  have hIcc :
      (∑ M ∈ Finset.Icc 1 H, g M / (pronicSeq M : ℝ)) =
        ∑ M ∈ Finset.range (H + 1), g M / (pronicSeq M : ℝ) :=
    sum_Icc_one_eq_sum_range_succ_of_zero (div_cast_pronicSeq_zero (g 0)) H
  rw [hIcc, hsplit]
  have hcomm :
      (∑' k : ℕ, g (k + (H + 1)) / (pronicSeq (k + (H + 1)) : ℝ)) =
        ∑' k : ℕ, g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ) := by
    congr 1
    ext k
    rw [Nat.add_comm k (H + 1)]
  linarith

/-- **Master Finite-Horizon Pronic Remainder Bound (`abs_tsum_div_pronicSeq_sub_sum_Icc_le`):**
For every sequence `g : ℕ → ℝ` with `|g M| ≤ B` for all `M : ℕ` and every finite horizon `H : ℕ`:
`|(∑' M, g M / pronicSeq M) - (∑_{M=1}^H g M / pronicSeq M)| ≤ B / (H + 1)`. -/
theorem abs_tsum_div_pronicSeq_sub_sum_Icc_le {g : ℕ → ℝ} {B : ℝ}
    (hB : ∀ M : ℕ, |g M| ≤ B) (H : ℕ) :
    |(∑' M : ℕ, g M / (pronicSeq M : ℝ)) -
      (∑ M ∈ Finset.Icc 1 H, g M / (pronicSeq M : ℝ))| ≤
      B / ((H : ℝ) + 1) := by
  rw [tsum_div_pronicSeq_sub_sum_Icc_eq hB H]
  have htail_tel := hasSum_one_div_pronicSeq_shift H
  have hmajor : Summable (fun k : ℕ => B * (1 / (pronicSeq (H + 1 + k) : ℝ))) :=
    htail_tel.summable.mul_left B
  have hs : Summable (fun k : ℕ => g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)) :=
    (summable_div_pronicSeq_of_bounded hB).comp_injective
      (fun a b hab => Nat.add_left_cancel hab)
  have hterm (k : ℕ) :
      ‖g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)‖ ≤
        B * (1 / (pronicSeq (H + 1 + k) : ℝ)) := by
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (a := (pronicSeq (H + 1 + k) : ℝ)) (Nat.cast_nonneg _)]
    calc
      |g (H + 1 + k)| / (pronicSeq (H + 1 + k) : ℝ)
        ≤ B / (pronicSeq (H + 1 + k) : ℝ) :=
          div_le_div_of_nonneg_right (hB (H + 1 + k)) (Nat.cast_nonneg _)
      _ = B * (1 / (pronicSeq (H + 1 + k) : ℝ)) := by ring
  calc
    |∑' k : ℕ, g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)|
      = ‖∑' k : ℕ, g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖g (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, B * (1 / (pronicSeq (H + 1 + k) : ℝ)) :=
      Summable.tsum_le_tsum hterm hs.norm hmajor
    _ = B / ((H : ℝ) + 1) := by
      rw [tsum_mul_left, htail_tel.tsum_eq]
      ring

/-! ## §2. Finite-Horizon Von Mangoldt Approximation -/

/-- **Single-Mode Finite-Horizon Von Mangoldt Approximation
(`abs_sum_Icc_pmRamanujanPrimitive_div_pronicSeq_add_vonMangoldt_le`):**
For every modulus `q > 1` and every finite horizon `H : ℕ`, the finite pronic sum of
`(pmRamanujanPrimitive q M).re` over `1 ≤ M ≤ H` approximates `-vonMangoldt q` with explicit error
at most `pmRamanujanPrimitiveBound q / (H + 1)`. -/
theorem abs_sum_Icc_pmRamanujanPrimitive_div_pronicSeq_add_vonMangoldt_le
    {q : ℕ} (hq : 1 < q) (H : ℕ) :
    |(∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) +
      vonMangoldt q| ≤
      pmRamanujanPrimitiveBound q / ((H : ℝ) + 1) := by
  have hB : ∀ M : ℕ, |(pmRamanujanPrimitive q M).re| ≤ pmRamanujanPrimitiveBound q :=
    fun M => (Complex.abs_re_le_norm (pmRamanujanPrimitive q M)).trans
      (norm_pmRamanujanPrimitive_le hq M)
  have htsum :
      (∑' M : ℕ, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) = -vonMangoldt q := by
    have hs :
        HasSum (fun M : ℕ => (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ))
          (-vonMangoldt q) :=
      (hasSum_pmRamanujanPrimitive_reciprocal hq).congr_fun
        (fun M => by rw [cast_pronicSeq_eq M])
    exact hs.tsum_eq
  have hrem := abs_tsum_div_pronicSeq_sub_sum_Icc_le hB H
  rw [htsum] at hrem
  have heq :
      |(∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) +
        vonMangoldt q| =
      |-vonMangoldt q -
        (∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ))| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [heq]
  exact hrem

/-- **Period-Free Pointwise Absolute Discrepancy Bound (`abs_sievePrefixDiscrepancy_le_periodFree`):**
For every cutoff `N : ℕ`, horizon `M : ℕ`, and sieve weight `c : ℕ → ℝ`,
`|sievePrefixDiscrepancy N M c| ≤ √(sieveVariance N c * sievePeriodFreeDualCeiling N)`. -/
theorem abs_sievePrefixDiscrepancy_le_periodFree (N M : ℕ) (c : ℕ → ℝ) :
    |sievePrefixDiscrepancy N M c| ≤
      Real.sqrt (sieveVariance N c * sievePeriodFreeDualCeiling N) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sievePrefixDiscrepancy_sq_le_periodFree N M c)

/-- **Finite-Horizon Sieve Discrepancy Von Mangoldt Approximation
(`abs_sum_Icc_sievePrefixDiscrepancy_div_pronicSeq_add_vonMangoldt_sum_le`):**
For every cutoff `N : ℕ`, sieve weight `c : ℕ → ℝ`, and finite horizon `H : ℕ`, the finite-horizon
pronic discrepancy sum over `1 ≤ M ≤ H` approximates the von Mangoldt functional
`-∑_{e=2}^N Λ(e) Y_{N,c}(e)` within `√(sieveVariance N c * sievePeriodFreeDualCeiling N) / (H + 1)`. -/
theorem abs_sum_Icc_sievePrefixDiscrepancy_div_pronicSeq_add_vonMangoldt_sum_le
    (N H : ℕ) (c : ℕ → ℝ) :
    |(∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) +
      (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e)| ≤
      Real.sqrt (sieveVariance N c * sievePeriodFreeDualCeiling N) / ((H : ℝ) + 1) := by
  have hB : ∀ M : ℕ,
      |sievePrefixDiscrepancy N M c| ≤
        Real.sqrt (sieveVariance N c * sievePeriodFreeDualCeiling N) :=
    fun M => abs_sievePrefixDiscrepancy_le_periodFree N M c
  have hrem := abs_tsum_div_pronicSeq_sub_sum_Icc_le hB H
  rw [tsum_sievePrefixDiscrepancy_div_pronicSeq N c] at hrem
  have heq :
      |(∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) +
        (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e)| =
      |(-∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) -
        (∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ))| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [heq]
  exact hrem

/-- The sieve variance of a pure mode probe `sieveModeWeight N q` (`q ∈ Icc 2 N`) equals `φ(q)`. -/
theorem sieveVariance_sieveModeWeight {N q : ℕ} (hq : q ∈ Finset.Icc 2 N) :
    sieveVariance N (sieveModeWeight N q) = (Nat.totient q : ℝ) := by
  unfold sieveVariance
  calc
    (∑ e ∈ Finset.Icc 2 N,
      (Nat.totient e : ℝ) * (selbergMultiplesCoord N (sieveModeWeight N q) e) ^ (2 : ℕ))
      = ∑ e ∈ Finset.Icc 2 N, if e = q then (Nat.totient e : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun e he => ?_
        have heI : e ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp he).1; omega, (Finset.mem_Icc.mp he).2⟩
        rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos heI]
        split_ifs <;> ring
    _ = (Nat.totient q : ℝ) := by simp [hq]

/-- **Pure-Mode Finite-Horizon Von Mangoldt Extraction Bound
(`abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_add_vonMangoldt_le`):**
For every mode `q ∈ Icc 2 N` and every finite horizon `H : ℕ`, probing the finite-horizon pronic
discrepancy sum over `1 ≤ M ≤ H` with `sieveModeWeight N q` extracts `-vonMangoldt q` with error at
most `√(φ(q) * sievePeriodFreeDualCeiling N) / (H + 1)`. -/
theorem abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_add_vonMangoldt_le
    {N q : ℕ} (hq : q ∈ Finset.Icc 2 N) (H : ℕ) :
    |(∑ M ∈ Finset.Icc 1 H,
      sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ)) +
      vonMangoldt q| ≤
      Real.sqrt ((Nat.totient q : ℝ) * sievePeriodFreeDualCeiling N) / ((H : ℝ) + 1) := by
  have hB : ∀ M : ℕ,
      |sievePrefixDiscrepancy N M (sieveModeWeight N q)| ≤
        Real.sqrt ((Nat.totient q : ℝ) * sievePeriodFreeDualCeiling N) := by
    intro M
    simpa [sieveVariance_sieveModeWeight hq] using
      abs_sievePrefixDiscrepancy_le_periodFree N M (sieveModeWeight N q)
  have hrem := abs_tsum_div_pronicSeq_sub_sum_Icc_le hB H
  rw [tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq hq] at hrem
  have heq :
      |(∑ M ∈ Finset.Icc 1 H,
        sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ)) +
        vonMangoldt q| =
      |-vonMangoldt q -
        (∑ M ∈ Finset.Icc 1 H,
          sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ))| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [heq]
  exact hrem

/-- **Composite Non-Prime-Power Finite-Horizon Decay Bound
(`abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_le_of_not_isPrimePow`):**
For every composite non-prime-power mode `q ∈ Icc 2 N` (`¬ IsPrimePow q`, such as `q = 6`) and
every finite horizon `H : ℕ`, the finite-horizon pronic discrepancy sum of `sieveModeWeight N q`
over `1 ≤ M ≤ H` is bounded in absolute value by
`√(φ(q) * sievePeriodFreeDualCeiling N) / (H + 1)`. -/
theorem abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_le_of_not_isPrimePow
    {N q : ℕ} (hq : q ∈ Finset.Icc 2 N) (hnp : ¬ IsPrimePow q) (H : ℕ) :
    |∑ M ∈ Finset.Icc 1 H,
      sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ)| ≤
      Real.sqrt ((Nat.totient q : ℝ) * sievePeriodFreeDualCeiling N) / ((H : ℝ) + 1) := by
  have h := abs_sum_Icc_sievePrefixDiscrepancy_mode_probe_div_pronicSeq_add_vonMangoldt_le hq H
  rwa [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, add_zero] at h

/-! ## §3. Truncated Non-Periodic Pronic Gram Matrix & Quadratic Form Remainder Bounds -/

/-- **The Finite-Horizon Truncated Non-Periodic Pronic Gram Matrix (`truncatedPronicGram`):**
The partial sum of `pmRamanujanPrimitiveGramTerm p q M` over `M ∈ [1, H]`. -/
def truncatedPronicGram (H p q : ℕ) : ℝ :=
  ∑ M ∈ Finset.Icc 1 H, pmRamanujanPrimitiveGramTerm p q M

/-- **The Finite-Horizon Truncated Pronic Discrepancy Quadratic Form
(`truncatedSievePronicDiscrepancyGramForm`):**
The quadratic form on Selberg multiples coordinates `selbergMultiplesCoord N c` induced by the
finite-horizon Gram matrix `truncatedPronicGram H p q`. -/
def truncatedSievePronicDiscrepancyGramForm (N H : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
      truncatedPronicGram H p q

/-- Symmetry of the truncated pronic Gram matrix `truncatedPronicGram H`. -/
theorem truncatedPronicGram_symm (H p q : ℕ) :
    truncatedPronicGram H p q = truncatedPronicGram H q p := by
  unfold truncatedPronicGram pmRamanujanPrimitiveGramTerm
  refine Finset.sum_congr rfl fun M _ => ?_
  ring

/-- `pmRamanujanPrimitiveGramTerm p q M` rewritten explicitly with denominator `(pronicSeq M : ℝ)`. -/
theorem pmRamanujanPrimitiveGramTerm_eq_div_pronicSeq (p q M : ℕ) :
    pmRamanujanPrimitiveGramTerm p q M =
      ((pmRamanujanPrimitive p M).re * (pmRamanujanPrimitive q M).re) / (pronicSeq M : ℝ) := by
  unfold pmRamanujanPrimitiveGramTerm
  rw [cast_pronicSeq_eq M]

/-- **Entrywise Truncation Error Bound for the Non-Periodic Pronic Gram Matrix
(`abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le`):**
For all moduli `p, q > 1` and every finite horizon `H : ℕ`:
`|pmRamanujanPrimitiveGram p q - truncatedPronicGram H p q| ≤ (pmRamanujanPrimitiveBound p * pmRamanujanPrimitiveBound q) / (H + 1)`. -/
theorem abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (H : ℕ) :
    |pmRamanujanPrimitiveGram p q - truncatedPronicGram H p q| ≤
      (pmRamanujanPrimitiveBound p * pmRamanujanPrimitiveBound q) / ((H : ℝ) + 1) := by
  have hB : ∀ M : ℕ,
      |(pmRamanujanPrimitive p M).re * (pmRamanujanPrimitive q M).re| ≤
        pmRamanujanPrimitiveBound p * pmRamanujanPrimitiveBound q := by
    intro M
    rw [abs_mul]
    exact mul_le_mul
      ((Complex.abs_re_le_norm (pmRamanujanPrimitive p M)).trans (norm_pmRamanujanPrimitive_le hp M))
      ((Complex.abs_re_le_norm (pmRamanujanPrimitive q M)).trans (norm_pmRamanujanPrimitive_le hq M))
      (abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hrem := abs_tsum_div_pronicSeq_sub_sum_Icc_le hB H
  simpa only [pmRamanujanPrimitiveGram, truncatedPronicGram,
    ← pmRamanujanPrimitiveGramTerm_eq_div_pronicSeq] using hrem

/-- **Exact Identity Between the Truncated Gram Quadratic Form and Finite-Horizon Discrepancy Energy
(`truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc`):**
For every cutoff `N : ℕ`, horizon `H : ℕ`, and sieve weight `c : ℕ → ℝ`, the quadratic form of
`truncatedPronicGram H` on `selbergMultiplesCoord N c` equals the finite-horizon pronic-weighted
squared discrepancy sum over `1 ≤ M ≤ H`. -/
theorem truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc
    (N H : ℕ) (c : ℕ → ℝ) :
    truncatedSievePronicDiscrepancyGramForm N H c =
      ∑ M ∈ Finset.Icc 1 H,
        (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ) := by
  unfold truncatedSievePronicDiscrepancyGramForm truncatedPronicGram
  calc
    (∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
      selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
        ∑ M ∈ Finset.Icc 1 H, pmRamanujanPrimitiveGramTerm p q M)
      = ∑ p ∈ Finset.Icc 2 N, ∑ M ∈ Finset.Icc 1 H, ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            pmRamanujanPrimitiveGramTerm p q M := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ M ∈ Finset.Icc 1 H, ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            pmRamanujanPrimitiveGramTerm p q M := Finset.sum_comm
    _ = ∑ M ∈ Finset.Icc 1 H,
          (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ) :=
        Finset.sum_congr rfl fun M _ =>
          (sievePrefixDiscrepancy_sq_div_pronicSeq_eq_gramTerm N M c).symm

/-- **Positive Semi-Definiteness of the Truncated Pronic Gram Quadratic Form
(`truncatedSievePronicDiscrepancyGramForm_nonneg`):**
For every `N, H : ℕ` and `c : ℕ → ℝ`, `0 ≤ truncatedSievePronicDiscrepancyGramForm N H c`. -/
theorem truncatedSievePronicDiscrepancyGramForm_nonneg
    (N H : ℕ) (c : ℕ → ℝ) :
    0 ≤ truncatedSievePronicDiscrepancyGramForm N H c := by
  rw [truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc]
  exact Finset.sum_nonneg fun M _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Monotonicity of the Truncated Pronic Gram Quadratic Form in the Horizon `H`
(`truncatedSievePronicDiscrepancyGramForm_mono`):**
If `H₁ ≤ H₂`, then
`truncatedSievePronicDiscrepancyGramForm N H₁ c ≤ truncatedSievePronicDiscrepancyGramForm N H₂ c`. -/
theorem truncatedSievePronicDiscrepancyGramForm_mono
    (N : ℕ) {H₁ H₂ : ℕ} (hH : H₁ ≤ H₂) (c : ℕ → ℝ) :
    truncatedSievePronicDiscrepancyGramForm N H₁ c ≤
      truncatedSievePronicDiscrepancyGramForm N H₂ c := by
  rw [truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc,
    truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hH) fun M _ _ => ?_
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Lower Bound: Truncated Gram Quadratic Form is Bounded Above by Infinite-Horizon Gram Form
(`truncatedSievePronicDiscrepancyGramForm_le_sievePronicDiscrepancyGramForm`):**
For every `N, H : ℕ` and `c : ℕ → ℝ`,
`truncatedSievePronicDiscrepancyGramForm N H c ≤ sievePronicDiscrepancyGramForm N c`. -/
theorem truncatedSievePronicDiscrepancyGramForm_le_sievePronicDiscrepancyGramForm
    (N H : ℕ) (c : ℕ → ℝ) :
    truncatedSievePronicDiscrepancyGramForm N H c ≤
      sievePronicDiscrepancyGramForm N c := by
  rw [truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc,
    ← tsum_sievePrefixDiscrepancy_sq_div_pronicSeq N c]
  exact (hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq N c).summable.sum_le_tsum
    (Finset.Icc 1 H) (fun M _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- **Quadratic Form Truncation Remainder Bound
(`sievePronicDiscrepancyGramForm_sub_truncated_le`):**
For every cutoff `N : ℕ`, finite horizon `H : ℕ`, and sieve weight `c : ℕ → ℝ`:
`0 ≤ sievePronicDiscrepancyGramForm N c - truncatedSievePronicDiscrepancyGramForm N H c ≤ (sieveVariance N c * sievePeriodFreeDualCeiling N) / (H + 1)`. -/
theorem sievePronicDiscrepancyGramForm_sub_truncated_le
    (N H : ℕ) (c : ℕ → ℝ) :
    sievePronicDiscrepancyGramForm N c -
      truncatedSievePronicDiscrepancyGramForm N H c ≤
      (sieveVariance N c * sievePeriodFreeDualCeiling N) / ((H : ℝ) + 1) := by
  have hB : ∀ M : ℕ,
      |(sievePrefixDiscrepancy N M c) ^ (2 : ℕ)| ≤
        sieveVariance N c * sievePeriodFreeDualCeiling N := by
    intro M
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sievePrefixDiscrepancy_sq_le_periodFree N M c
  have hrem := abs_tsum_div_pronicSeq_sub_sum_Icc_le hB H
  rw [tsum_sievePrefixDiscrepancy_sq_div_pronicSeq N c,
    ← truncatedSievePronicDiscrepancyGramForm_eq_sum_Icc N H c] at hrem
  exact (le_abs_self _).trans hrem

/-- **Two-Sided Absolute Remainder Bound for the Truncated Gram Quadratic Form
(`abs_sievePronicDiscrepancyGramForm_sub_truncated_le`):**
For every `N, H : ℕ` and `c : ℕ → ℝ`:
`|sievePronicDiscrepancyGramForm N c - truncatedSievePronicDiscrepancyGramForm N H c| ≤ (sieveVariance N c * sievePeriodFreeDualCeiling N) / (H + 1)`. -/
theorem abs_sievePronicDiscrepancyGramForm_sub_truncated_le
    (N H : ℕ) (c : ℕ → ℝ) :
    |sievePronicDiscrepancyGramForm N c -
      truncatedSievePronicDiscrepancyGramForm N H c| ≤
      (sieveVariance N c * sievePeriodFreeDualCeiling N) / ((H : ℝ) + 1) := by
  have hnonneg :
      0 ≤ sievePronicDiscrepancyGramForm N c -
        truncatedSievePronicDiscrepancyGramForm N H c :=
    sub_nonneg.mpr (truncatedSievePronicDiscrepancyGramForm_le_sievePronicDiscrepancyGramForm N H c)
  rw [abs_of_nonneg hnonneg]
  exact sievePronicDiscrepancyGramForm_sub_truncated_le N H c

/-- **Finite-Horizon Prime-Dilated Gram Recurrence Defect Bound
(`abs_truncatedPronicGram_prime_pair_defect_le`):**
For every prime `p`, moduli `q > 1` and `r > 1` with `¬ p ∣ q` and `¬ p ∣ r`, and every finite
horizon `H : ℕ`, the finite-horizon prime-dilation recurrence defect on `truncatedPronicGram H`
decays explicitly as `O(1 / (H + 1))`. -/
theorem abs_truncatedPronicGram_prime_pair_defect_le
    {p q r : ℕ} (hp : p.Prime) (hq : 1 < q) (hr : 1 < r)
    (hpq : ¬ p ∣ q) (hpr : ¬ p ∣ r) (H : ℕ) :
    |(truncatedPronicGram H (p * q) (p * r) +
        truncatedPronicGram H (p * q) r +
        truncatedPronicGram H q (p * r)) -
      ((p : ℝ) - 1) * truncatedPronicGram H q r| ≤
      (pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound (p * r) +
        pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound r +
        pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound (p * r) +
        ((p : ℝ) - 1) * (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r)) /
        ((H : ℝ) + 1) := by
  have hpq1 : 1 < p * q := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hp.pos)
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  have hrec := pmRamanujanPrimitiveGram_prime_pair hp hq hr hpq hpr
  have h1 := abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le hpq1 hpr1 H
  have h2 := abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le hpq1 hr H
  have h3 := abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le hq hpr1 H
  have h4 := abs_pmRamanujanPrimitiveGram_sub_truncatedPronicGram_le hq hr H
  have hp1_nonneg : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    linarith
  set E1 := pmRamanujanPrimitiveGram (p * q) (p * r) - truncatedPronicGram H (p * q) (p * r)
  set E2 := pmRamanujanPrimitiveGram (p * q) r - truncatedPronicGram H (p * q) r
  set E3 := pmRamanujanPrimitiveGram q (p * r) - truncatedPronicGram H q (p * r)
  set E4 := pmRamanujanPrimitiveGram q r - truncatedPronicGram H q r
  have hid :
      (truncatedPronicGram H (p * q) (p * r) +
        truncatedPronicGram H (p * q) r +
        truncatedPronicGram H q (p * r)) -
        ((p : ℝ) - 1) * truncatedPronicGram H q r =
      -(E1 + E2 + E3 - ((p : ℝ) - 1) * E4) := by
    dsimp only [E1, E2, E3, E4]
    linarith
  rw [hid, abs_neg]
  have htri1 : |E1 + E2 + E3 - ((p : ℝ) - 1) * E4| ≤
      |E1| + |E2| + |E3| + ((p : ℝ) - 1) * |E4| := by
    have ha : |E1 + E2 + E3 - ((p : ℝ) - 1) * E4| ≤ |E1 + E2 + E3| + |((p : ℝ) - 1) * E4| :=
      abs_sub _ _
    have hb : |E1 + E2 + E3| ≤ |E1 + E2| + |E3| := abs_add_le _ _
    have hc : |E1 + E2| ≤ |E1| + |E2| := abs_add_le _ _
    have hd : |((p : ℝ) - 1) * E4| = ((p : ℝ) - 1) * |E4| := by
      rw [abs_mul, abs_of_nonneg hp1_nonneg]
    linarith
  have h4' : ((p : ℝ) - 1) * |E4| ≤
      (((p : ℝ) - 1) * (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r)) /
        ((H : ℝ) + 1) := by
    calc
      ((p : ℝ) - 1) * |E4|
        ≤ ((p : ℝ) - 1) *
            ((pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r) / ((H : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h4 hp1_nonneg
      _ = (((p : ℝ) - 1) * (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r)) /
            ((H : ℝ) + 1) := by ring
  calc
    |E1 + E2 + E3 - ((p : ℝ) - 1) * E4|
      ≤ |E1| + |E2| + |E3| + ((p : ℝ) - 1) * |E4| := htri1
    _ ≤ (pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound (p * r)) / ((H : ℝ) + 1) +
        (pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound r) / ((H : ℝ) + 1) +
        (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound (p * r)) / ((H : ℝ) + 1) +
        (((p : ℝ) - 1) * (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r)) /
          ((H : ℝ) + 1) := by linarith
    _ = (pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound (p * r) +
        pmRamanujanPrimitiveBound (p * q) * pmRamanujanPrimitiveBound r +
        pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound (p * r) +
        ((p : ℝ) - 1) * (pmRamanujanPrimitiveBound q * pmRamanujanPrimitiveBound r)) /
        ((H : ℝ) + 1) := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
