import GaloisForLFunctions.BezoutValuationIncidence.PredictableMartingaleDecompositionAndCovarianceCancellationBridge

/-!
# Pillar XIV: All-Octave Fermi Sibling Polarization, Centered-Prefix Wavelet Bridge, & Dyadic Resolvent Reconstruction

In this fourteenth pillar of **Bézout–Valuation Incidence Mechanics**, we establish three universal
structural mechanisms connecting the physical Fermi–Nyman cell response `fermiCellResponse N c n`,
the BVI additive forward difference `addDiff (sieveSeq N c)`, and the centered divisor prefix
`pmPowerDampedCenteredDivisorPrefix ε` of Route PM:

## Core Main Theorems (100% Unconditional)

1. **Universal All-Octave Dyadic Sibling Step, Second-Order BVI Gradient, & Polarization Identities
   (`fermiCellResponse_two_mul_add_one_sub_two_mul`,
   `fermiCellResponse_two_mul_add_two_sub_two_mul_add_one`,
   `fermiCellResponse_second_diff_across_odd_eq_two_half_sub_addDiff`,
   `two_mul_add_sq_fermiCellResponse_siblings`)**:
   For **every** cutoff `N : ℕ`, **every** weight `c : ℕ → ℝ`, and **every** `m : ℕ` (valid across
   all octaves without restriction):
   - Stepping from an even cell `2m` to its odd sibling `2m + 1` cancels the half-scale prefix
     `2 ∑_{k=1}^m s_{N,c}(k)` identically, leaving purely `-s_{N,c}(2m + 1)`.
   - The second-order difference across the odd cell `2m + 1` isolates the BVI forward gradient
     `addDiff (sieveSeq N c) (2m + 1) = s_{N,c}(2m + 2) - s_{N,c}(2m + 1)` coupled to the half-scale
     parent `2 s_{N,c}(m + 1)`:
     $$\bigl(F(2m + 2) - F(2m + 1)\bigr) - \bigl(F(2m + 1) - F(2m)\bigr) =
       2\,s_{N,c}(m + 1) - \operatorname{addDiff}(\operatorname{sieveSeq}\,N\,c)\,(2m + 1).$$
   - The sibling pair `(2m, 2m + 1)` satisfies the exact polarization identity:
     $$2\bigl(F(2m)^2 + F(2m + 1)^2\bigr) = \bigl(F(2m) + F(2m + 1)\bigr)^2 + s_{N,c}(2m + 1)^2.$$

2. **Exact Sub-Horizon Centered-Prefix Wavelet Formula & Even-Cell Drift Cancellation
   (`fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet`,
   `fermiCellResponse_pmPowerDampedRealWeight_two_mul_eq_centeredPrefix_diff`,
   `fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_eq`)**:
   For `c_ε = pmPowerDampedRealWeight ε` and every sub-horizon cell `n ≤ N`:
   $$\operatorname{fermiCellResponse}(N, c_\varepsilon, n) =
     2\,A_\varepsilon(\lfloor n / 2 \rfloor) - A_\varepsilon(n) - (n \bmod 2)\,\alpha_\varepsilon,$$
   where $A_\varepsilon(m) = \operatorname{pmPowerDampedCenteredDivisorPrefix}\,\varepsilon\,m$ and
   $\alpha_\varepsilon = (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}$.
   In particular, on every sub-horizon **even** cell `2m ≤ N`, the density drift $\alpha_\varepsilon$
   cancels **100% identically**:
   $$\operatorname{fermiCellResponse}(N, c_\varepsilon, 2m) = 2\,A_\varepsilon(m) - A_\varepsilon(2m).$$

3. **Telescoping Dyadic Wavelet Resolvent Reconstruction
   (`sum_pow_two_mul_dyadicPrefixWavelet`,
   `eq_neg_sum_pow_two_mul_dyadicPrefixWavelet_of_lt`,
   `pmPowerDampedCenteredDivisorPrefix_eq_neg_sum_dyadicPrefixWavelet`)**:
   Defining the dyadic prefix wavelet operator `dyadicPrefixWavelet A n = 2 * A (n / 2) - A n`,
   every prefix sequence `A : ℕ → ℝ` satisfies the exact multi-scale telescoping identity
   $$\sum_{j=0}^{K-1} 2^j \operatorname{dyadicPrefixWavelet}\,A\,\lfloor n / 2^j \rfloor =
     2^K A(\lfloor n / 2^K \rfloor) - A(n),$$
   which reconstructs `pmPowerDampedCenteredDivisorPrefix ε n` at finite depth `K ≥ n` (`2^K > n`)
   via `A_ε(0) = 0`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal All-Octave Dyadic Sibling Step, Second-Order Gradient, & Polarization -/

/-- **Universal All-Octave Even-to-Odd Sibling Step (`fermiCellResponse_two_mul_add_one_sub_two_mul`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ` (across all octaves), stepping from the even cell `2m`
to its odd sibling `2m + 1` cancels the half-scale prefix sum identically, leaving
`-sieveSeq N c (2 * m + 1)`. -/
theorem fermiCellResponse_two_mul_add_one_sub_two_mul (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiCellResponse N c (2 * m + 1) - fermiCellResponse N c (2 * m) =
      -sieveSeq N c (2 * m + 1) := by
  have hodd : ¬ (2 ∣ (2 * m + 1)) := by omega
  exact fermiCellResponse_succ_sub_of_not_two_dvd N c hodd

/-- **Universal All-Octave Odd-to-Even Boundary Step
(`fermiCellResponse_two_mul_add_two_sub_two_mul_add_one`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ` (across all octaves), stepping from the odd cell `2m + 1`
to the next even cell `2m + 2 = 2(m + 1)` activates the half-scale parent `2 * sieveSeq N c (m + 1)`:
`fermiCellResponse N c (2 * m + 2) - fermiCellResponse N c (2 * m + 1) = 2 * sieveSeq N c (m + 1) - sieveSeq N c (2 * m + 2)`. -/
theorem fermiCellResponse_two_mul_add_two_sub_two_mul_add_one (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiCellResponse N c (2 * m + 2) - fermiCellResponse N c (2 * m + 1) =
      2 * sieveSeq N c (m + 1) - sieveSeq N c (2 * m + 2) := by
  have hstep := fermiCellResponse_succ_sub_eq N c (2 * m + 1)
  have heq : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [heq] at hstep ⊢
  rw [hstep, if_pos (dvd_mul_right 2 (m + 1)),
    Nat.mul_div_cancel_left (m + 1) (by decide : 0 < 2)]

/-- **Universal All-Octave Two-Step Even-to-Even Jump
(`fermiCellResponse_two_mul_add_two_sub_two_mul`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ`:
`fermiCellResponse N c (2 * m + 2) - fermiCellResponse N c (2 * m) = 2 * sieveSeq N c (m + 1) - sieveSeq N c (2 * m + 1) - sieveSeq N c (2 * m + 2)`. -/
theorem fermiCellResponse_two_mul_add_two_sub_two_mul (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiCellResponse N c (2 * m + 2) - fermiCellResponse N c (2 * m) =
      2 * sieveSeq N c (m + 1) - sieveSeq N c (2 * m + 1) - sieveSeq N c (2 * m + 2) := by
  have h1 := fermiCellResponse_two_mul_add_one_sub_two_mul N c m
  have h2 := fermiCellResponse_two_mul_add_two_sub_two_mul_add_one N c m
  linarith

/-- **Second-Order Difference Across Odd Cells & BVI Forward Gradient
(`fermiCellResponse_second_diff_across_odd_eq_two_half_sub_addDiff`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ`, the second-order difference of `fermiCellResponse N c`
centered at the odd cell `2m + 1` isolates the BVI forward gradient
`addDiff (sieveSeq N c) (2 * m + 1) = sieveSeq N c (2 * m + 2) - sieveSeq N c (2 * m + 1)`
coupled to the half-scale parent `2 * sieveSeq N c (m + 1)`. -/
theorem fermiCellResponse_second_diff_across_odd_eq_two_half_sub_addDiff
    (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    (fermiCellResponse N c (2 * m + 2) - fermiCellResponse N c (2 * m + 1)) -
      (fermiCellResponse N c (2 * m + 1) - fermiCellResponse N c (2 * m)) =
      2 * sieveSeq N c (m + 1) - addDiff (sieveSeq N c) (2 * m + 1) := by
  rw [fermiCellResponse_two_mul_add_two_sub_two_mul_add_one,
    fermiCellResponse_two_mul_add_one_sub_two_mul]
  unfold addDiff
  ring

/-- **Dyadic Sibling Polarization Identity (`two_mul_add_sq_fermiCellResponse_siblings`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ`, twice the sum of squared responses on the dyadic
sibling pair `(2m, 2m + 1)` equals the squared sibling sum plus `sieveSeq N c (2 * m + 1)²`. -/
theorem two_mul_add_sq_fermiCellResponse_siblings (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    2 * (fermiCellResponse N c (2 * m) ^ (2 : ℕ) +
      fermiCellResponse N c (2 * m + 1) ^ (2 : ℕ)) =
      (fermiCellResponse N c (2 * m) + fermiCellResponse N c (2 * m + 1)) ^ (2 : ℕ) +
        sieveSeq N c (2 * m + 1) ^ (2 : ℕ) := by
  have hdiff := fermiCellResponse_two_mul_add_one_sub_two_mul N c m
  have hpol :
      2 * (fermiCellResponse N c (2 * m) ^ (2 : ℕ) +
        fermiCellResponse N c (2 * m + 1) ^ (2 : ℕ)) =
      (fermiCellResponse N c (2 * m) + fermiCellResponse N c (2 * m + 1)) ^ (2 : ℕ) +
        (fermiCellResponse N c (2 * m + 1) - fermiCellResponse N c (2 * m)) ^ (2 : ℕ) := by
    ring
  rw [hpol, hdiff]
  ring

/-- **Dyadic Sibling Square-Difference Martingale Identity
(`fermiCellResponse_two_mul_add_one_sq_sub_two_mul_sq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ`:
`fermiCellResponse N c (2 * m + 1)² - fermiCellResponse N c (2 * m)² = sieveSeq N c (2 * m + 1)² - 2 * sieveSeq N c (2 * m + 1) * fermiCellResponse N c (2 * m)`. -/
theorem fermiCellResponse_two_mul_add_one_sq_sub_two_mul_sq (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiCellResponse N c (2 * m + 1) ^ (2 : ℕ) -
      fermiCellResponse N c (2 * m) ^ (2 : ℕ) =
      sieveSeq N c (2 * m + 1) ^ (2 : ℕ) -
        2 * sieveSeq N c (2 * m + 1) * fermiCellResponse N c (2 * m) := by
  have hstep := sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff
    (fermiCellResponse N c) (2 * m)
  have hadd : addDiff (fermiCellResponse N c) (2 * m) = -sieveSeq N c (2 * m + 1) := by
    unfold addDiff
    exact fermiCellResponse_two_mul_add_one_sub_two_mul N c m
  rw [hadd] at hstep
  linarith

/-! ## §2. Exact Sub-Horizon Centered-Prefix Wavelet Formula & Even-Cell Drift Cancellation -/

/-- For every `ε : ℝ` and `m ≤ N`, the sub-horizon prefix sum of
`sieveSeq N (pmPowerDampedRealWeight ε)` decomposes into the centered prefix
`pmPowerDampedCenteredDivisorPrefix ε m` plus the linear density drift
`(pmPowerDampedDivisorDensity ε).re * m`. -/
theorem sum_sieveSeq_pmPowerDampedRealWeight_eq_centeredPrefix_add_density
    (ε : ℝ) {N m : ℕ} (hmN : m ≤ N) :
    (∑ k ∈ Finset.Icc 1 m, sieveSeq N (pmPowerDampedRealWeight ε) k) =
      pmPowerDampedCenteredDivisorPrefix ε m +
        (pmPowerDampedDivisorDensity ε).re * (m : ℝ) := by
  have hcongr : ∀ k ∈ Finset.Icc 1 m,
      sieveSeq N (pmPowerDampedRealWeight ε) k = pmPowerDampedDivisorCoeff ε k := by
    intro k hk
    obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1 (hkm.trans hmN)
  rw [Finset.sum_congr rfl hcongr, pmPowerDampedCenteredDivisorPrefix_eq]
  ring

/-- **Sub-Horizon Centered-Prefix Wavelet Formula
(`fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet`):**
For every `ε : ℝ` and every sub-horizon cell `n ≤ N`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) n = 2 * pmPowerDampedCenteredDivisorPrefix ε (n / 2) - pmPowerDampedCenteredDivisorPrefix ε n - (n % 2) * (pmPowerDampedDivisorDensity ε).re`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet
    (ε : ℝ) {N n : ℕ} (hnN : n ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) n =
      2 * pmPowerDampedCenteredDivisorPrefix ε (n / 2) -
        pmPowerDampedCenteredDivisorPrefix ε n -
        ((n % 2 : ℕ) : ℝ) * (pmPowerDampedDivisorDensity ε).re := by
  rw [fermiCellResponse_eq_two_prefix_half_sub_prefix,
    sum_sieveSeq_pmPowerDampedRealWeight_eq_centeredPrefix_add_density ε (by omega : n / 2 ≤ N),
    sum_sieveSeq_pmPowerDampedRealWeight_eq_centeredPrefix_add_density ε hnN]
  have hdivmod : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hdivmodR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hdivmod
  rw [← hdivmodR]
  ring

/-- **Exact Density-Drift Cancellation on Sub-Horizon Even Cells
(`fermiCellResponse_pmPowerDampedRealWeight_two_mul_eq_centeredPrefix_diff`):**
For every `ε : ℝ` and every sub-horizon even cell `2 * m ≤ N`, the linear density drift
`(pmPowerDampedDivisorDensity ε).re` cancels **100% identically**, so the physical Fermi–Nyman
cell response is purely the dyadic wavelet difference of `pmPowerDampedCenteredDivisorPrefix ε`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) = 2 * pmPowerDampedCenteredDivisorPrefix ε m - pmPowerDampedCenteredDivisorPrefix ε (2 * m)`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_two_mul_eq_centeredPrefix_diff
    (ε : ℝ) {N m : ℕ} (hmN : 2 * m ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m) =
      2 * pmPowerDampedCenteredDivisorPrefix ε m -
        pmPowerDampedCenteredDivisorPrefix ε (2 * m) := by
  rw [fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet ε hmN,
    Nat.mul_div_cancel_left m (by decide : 0 < 2), Nat.mul_mod_right]
  simp

/-- **Exact Parity-Shifted Wavelet Formula on Sub-Horizon Odd Cells
(`fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_eq`):**
For every `ε : ℝ` and every sub-horizon odd cell `2 * m + 1 ≤ N`:
`fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) = 2 * pmPowerDampedCenteredDivisorPrefix ε m - pmPowerDampedCenteredDivisorPrefix ε (2 * m + 1) - (pmPowerDampedDivisorDensity ε).re`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_two_mul_add_one_eq
    (ε : ℝ) {N m : ℕ} (hmN : 2 * m + 1 ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) (2 * m + 1) =
      2 * pmPowerDampedCenteredDivisorPrefix ε m -
        pmPowerDampedCenteredDivisorPrefix ε (2 * m + 1) -
        (pmPowerDampedDivisorDensity ε).re := by
  rw [fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet ε hmN]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  rw [hdiv, hmod]
  simp

/-! ## §3. Dyadic Wavelet Resolvent Reconstruction of Prefix Sequences -/

/-- **Dyadic Prefix Wavelet Operator (`dyadicPrefixWavelet`):**
Maps any sequence `A : ℕ → ℝ` to its dyadic half-scale wavelet difference
`dyadicPrefixWavelet A n = 2 * A (n / 2) - A n`. -/
def dyadicPrefixWavelet (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * A (n / 2) - A n

/-- On every sub-horizon cell `n ≤ N`, `fermiCellResponse N (pmPowerDampedRealWeight ε) n`
equals `dyadicPrefixWavelet (pmPowerDampedCenteredDivisorPrefix ε) n` minus the parity shift
`(n % 2) * (pmPowerDampedDivisorDensity ε).re`. -/
theorem fermiCellResponse_pmPowerDampedRealWeight_eq_dyadicPrefixWavelet_sub_parity
    (ε : ℝ) {N n : ℕ} (hnN : n ≤ N) :
    fermiCellResponse N (pmPowerDampedRealWeight ε) n =
      dyadicPrefixWavelet (pmPowerDampedCenteredDivisorPrefix ε) n -
        ((n % 2 : ℕ) : ℝ) * (pmPowerDampedDivisorDensity ε).re :=
  fermiCellResponse_pmPowerDampedRealWeight_eq_centeredPrefix_wavelet ε hnN

/-- **Telescoping Dyadic Wavelet Resolvent Identity (`sum_pow_two_mul_dyadicPrefixWavelet`):**
For every sequence `A : ℕ → ℝ`, index `n : ℕ`, and octave depth `K : ℕ`:
`∑_{j=0}^{K-1} 2^j * dyadicPrefixWavelet A (n / 2^j) = 2^K * A (n / 2^K) - A n`. -/
theorem sum_pow_two_mul_dyadicPrefixWavelet (A : ℕ → ℝ) (n K : ℕ) :
    (∑ j ∈ Finset.range K, (2 : ℝ) ^ j * dyadicPrefixWavelet A (n / 2 ^ j)) =
      (2 : ℝ) ^ K * A (n / 2 ^ K) - A n := by
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dyadicPrefixWavelet
    have hdiv : (n / 2 ^ K) / 2 = n / 2 ^ (K + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [hdiv, pow_succ]
    ring

/-- **Finite-Depth Dyadic Wavelet Reconstruction (`eq_neg_sum_pow_two_mul_dyadicPrefixWavelet_of_lt`):**
For every sequence `A : ℕ → ℝ` with `A 0 = 0` and every `n, K : ℕ` with `n < 2 ^ K`:
`A n = -∑_{j=0}^{K-1} 2^j * dyadicPrefixWavelet A (n / 2^j)`. -/
theorem eq_neg_sum_pow_two_mul_dyadicPrefixWavelet_of_lt {A : ℕ → ℝ} (hA0 : A 0 = 0)
    {n K : ℕ} (hlt : n < 2 ^ K) :
    A n = -∑ j ∈ Finset.range K, (2 : ℝ) ^ j * dyadicPrefixWavelet A (n / 2 ^ j) := by
  have htel := sum_pow_two_mul_dyadicPrefixWavelet A n K
  have hdiv0 : n / 2 ^ K = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv0, hA0, mul_zero, zero_sub] at htel
  linarith

/-- **Exact Dyadic Wavelet Reconstruction of `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_eq_neg_sum_dyadicPrefixWavelet`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorPrefix ε n = -∑_{j=0}^{n-1} 2^j * dyadicPrefixWavelet (pmPowerDampedCenteredDivisorPrefix ε) (n / 2^j)`. -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_neg_sum_dyadicPrefixWavelet (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      -∑ j ∈ Finset.range n,
        (2 : ℝ) ^ j * dyadicPrefixWavelet (pmPowerDampedCenteredDivisorPrefix ε) (n / 2 ^ j) :=
  eq_neg_sum_pow_two_mul_dyadicPrefixWavelet_of_lt
    (pmPowerDampedCenteredDivisorPrefix_zero ε)
    (Nat.lt_pow_self (by decide : 1 < 2))

end
end GaloisForLFunctions.BezoutValuationIncidence
