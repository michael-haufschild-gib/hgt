import GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation
import GaloisForLFunctions.BezoutValuationIncidence.JordanUpperBoundAndGcdOrbitPrimitiveEnergy
import GaloisForLFunctions.BezoutValuationIncidence.SawtoothBezoutSuccessorGradientAndRouteFZZPBridge

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar XV: Power-Damped Pronic `2`-Adic Ceiling, Renormalized Defect Non-Positivity, and BVI Frontier Synthesis

This module unites the renormalized prefix-defect calculus
(`RenormalizedMobiusDefectAndFirstOctaveCancellation`), the Jordan–totient and GCD-orbit primitive
energy bounds (`JordanUpperBoundAndGcdOrbitPrimitiveEnergy`), and the power-damped Route PM / FZZ-P
bridge (`PowerDampedPronicMultiplicativityAndRoutePMBridge`,
`SawtoothBezoutSuccessorGradientAndRouteFZZPBridge`):

1. **Universal `2`-Adic Factorization and Ceiling on Pronic Bézout Nodes
   (`two_mem_primeFactors_pronicSeq`, `pmPowerDampedDivisorCoeff_pronicSeq_eq_mul_erase_two`,
   `pmPowerDampedDivisorCoeff_pronicSeq_le_one_sub_two_rpow`,
   `pmPowerDampedDivisorCoeff_mul_succ_le_one_sub_two_rpow`):**
   For every `k ≥ 1`, the pronic Bézout product `pronicSeq k = k * (k + 1)` is positive and even,
   so `2 ∈ (pronicSeq k).primeFactors`. Splitting off the `2`-adic Euler factor yields the exact
   factorization
   $$\text{pmPowerDampedDivisorCoeff}(\varepsilon, \text{pronicSeq}(k))
     = (1 - 2^{-\varepsilon}) \prod_{p \in \text{primeFactors}(k(k+1)) \setminus \{2\}} (1 - p^{-\varepsilon}).$$
   Consequently, for every $\varepsilon \ge 0$ and every $k \ge 1$, even though individual prime
   responses $\text{pmPowerDampedDivisorCoeff}(\varepsilon, p) = 1 - p^{-\varepsilon} \to 1$ as
   $p \to \infty$, every consecutive product is uniformly bounded away from $1$ by the $2$-adic
   Bézout ceiling:
   $$0 \le \text{pmPowerDampedDivisorCoeff}(\varepsilon, k) \cdot
     \text{pmPowerDampedDivisorCoeff}(\varepsilon, k + 1)
     = \text{pmPowerDampedDivisorCoeff}(\varepsilon, \text{pronicSeq}(k))
     \le 1 - 2^{-\varepsilon}.$$

2. **Exact Sub-Horizon Pronic Formula & Unconditional Non-Positivity of the Power-Damped
   Renormalized Defect (`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq_pronic_sub_sq`,
   `two_mul_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq`,
   `sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`,
   `sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve`):**
   For every $\varepsilon \in \mathbb{R}$ and $1 \le M$ with $M + 1 \le N$:
   $$\text{sieveRenormalizedPrefixDefect}(N, M, \text{pmPowerDampedRealWeight}(\varepsilon))
     = \sum_{k=1}^M g_\varepsilon(\text{pronicSeq}(k)) - \sum_{k=1}^M g_\varepsilon(k)^2$$
   and
   $$2 \cdot \text{sieveRenormalizedPrefixDefect}(N, M, \text{pmPowerDampedRealWeight}(\varepsilon))
     = -\sum_{k=1}^M \big(g_\varepsilon(k + 1) - g_\varepsilon(k)\big)^2
       + \big(g_\varepsilon(M + 1)^2 - 1\big).$$
   For every $\varepsilon \ge 0$, since $0 \le g_\varepsilon(M + 1) \le 1$, both terms on the
   right-hand side are non-positive, so $\text{sieveRenormalizedPrefixDefect}(N, M, c_\varepsilon) \le 0$
   and $\text{sieveCombinedPrefixDefect}(N, M, c_\varepsilon) \le M \cdot \text{sieveSuccessorReserve}(N, c_\varepsilon)$
   unconditionally for all $\varepsilon \ge 0$.

3. **Master Synthesis of the Renormalized Defect, Jordan Upper Bound, and GCD-Orbit Energy Filtering
   (`bezoutValuationIncidence_renormalized_defect_and_jordan_gcd_synthesis`).**
-/

/-! ## §1. Universal `2`-Adic Factorization and Ceiling on Pronic Bézout Nodes -/

/-- Every pronic integer `pronicSeq k = k * (k + 1)` is divisible by `2`. -/
theorem two_dvd_pronicSeq (k : ℕ) : 2 ∣ pronicSeq k := by
  unfold pronicSeq
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨m * (m + m + 1), ?_⟩
    ring
  · refine ⟨(2 * m + 1) * (m + 1), ?_⟩
    ring

/-- For every `k ≥ 1`, `pronicSeq k = k * (k + 1) ≠ 0`. -/
theorem pronicSeq_ne_zero {k : ℕ} (hk : 1 ≤ k) : pronicSeq k ≠ 0 := by
  unfold pronicSeq
  positivity

/-- For every `k ≥ 1`, `2` is a prime factor of `pronicSeq k = k * (k + 1)`. -/
theorem two_mem_primeFactors_pronicSeq {k : ℕ} (hk : 1 ≤ k) :
    2 ∈ (pronicSeq k).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_pronicSeq k, pronicSeq_ne_zero hk⟩

/-- **Exact `2`-Adic Euler Factorization of `pmPowerDampedDivisorCoeff` on Pronic Nodes
(`pmPowerDampedDivisorCoeff_pronicSeq_eq_mul_erase_two`):**
For every `ε : ℝ` and `k ≥ 1`, splitting off `p = 2` from `(pronicSeq k).primeFactors` yields
`pmPowerDampedDivisorCoeff ε (pronicSeq k) = (1 - 2^{-ε}) * ∏ p ∈ (pronicSeq k).primeFactors.erase 2, (1 - p^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_pronicSeq_eq_mul_erase_two (ε : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    pmPowerDampedDivisorCoeff ε (pronicSeq k) =
      (1 - ((2 : ℕ) : ℝ) ^ (-ε)) *
        ∏ p ∈ (pronicSeq k).primeFactors.erase 2, (1 - (p : ℝ) ^ (-ε)) := by
  rw [pmPowerDampedDivisorCoeff_eq_prod ε (pronicSeq_ne_zero hk),
    ← Finset.mul_prod_erase (pronicSeq k).primeFactors
      (fun p : ℕ => 1 - (p : ℝ) ^ (-ε)) (two_mem_primeFactors_pronicSeq hk)]

/-- **Universal Pronic `2`-Adic Ceiling (`pmPowerDampedDivisorCoeff_pronicSeq_le_one_sub_two_rpow`):**
For every `ε ≥ 0` and every `k ≥ 1`:
`0 ≤ pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤ 1 - 2^{-ε}`. -/
theorem pmPowerDampedDivisorCoeff_pronicSeq_le_one_sub_two_rpow {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ pmPowerDampedDivisorCoeff ε (pronicSeq k) ∧
      pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤ 1 - (2 : ℝ) ^ (-ε) := by
  refine ⟨pmPowerDampedDivisorCoeff_nonneg hε (pronicSeq k), ?_⟩
  have hfact := pmPowerDampedDivisorCoeff_pronicSeq_eq_mul_erase_two ε hk
  simp only [Nat.cast_ofNat] at hfact
  rw [hfact]
  have h2_nonneg : 0 ≤ 1 - (2 : ℝ) ^ (-ε) := by
    apply sub_nonneg.mpr
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hprod_le_one :
      (∏ p ∈ (pronicSeq k).primeFactors.erase 2, (1 - (p : ℝ) ^ (-ε))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have hp_prime : Nat.Prime p :=
        Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      apply sub_nonneg.mpr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp_prime.one_le) (by linarith)
    · intro p _
      linarith [Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)]
  calc
    (1 - (2 : ℝ) ^ (-ε)) *
        ∏ p ∈ (pronicSeq k).primeFactors.erase 2, (1 - (p : ℝ) ^ (-ε))
      ≤ (1 - (2 : ℝ) ^ (-ε)) * 1 := mul_le_mul_of_nonneg_left hprod_le_one h2_nonneg
    _ = 1 - (2 : ℝ) ^ (-ε) := mul_one _

/-- **Consecutive Bézout Product Ceiling (`pmPowerDampedDivisorCoeff_mul_succ_le_one_sub_two_rpow`):**
For every `ε ≥ 0` and `k ≥ 1`, the consecutive product of power-damped divisor coefficients obeys
`pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) ≤ 1 - 2^{-ε}`. -/
theorem pmPowerDampedDivisorCoeff_mul_succ_le_one_sub_two_rpow {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℕ} (hk : 1 ≤ k) :
    pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) ≤
      1 - (2 : ℝ) ^ (-ε) := by
  rw [pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq]
  exact (pmPowerDampedDivisorCoeff_pronicSeq_le_one_sub_two_rpow hε hk).2

/-! ## §2. Exact Sub-Horizon Pronic Formula & Universal Non-Positivity of the Power-Damped Defect -/

/-- **Exact Sub-Horizon Pronic Formula for `sieveRenormalizedPrefixDefect` of `pmPowerDampedRealWeight`
(`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq_pronic_sub_sq`):**
For every `ε : ℝ` and `N, M : ℕ` with `M + 1 ≤ N`:
`sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) = (∑ k ∈ Icc 1 M, pmPowerDampedDivisorCoeff ε (pronicSeq k)) - ∑ k ∈ Icc 1 M, pmPowerDampedDivisorCoeff ε k ^ 2`. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq_pronic_sub_sq
    (ε : ℝ) {N M : ℕ} (hMN : M + 1 ≤ N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) =
      (∑ k ∈ Finset.Icc 1 M, pmPowerDampedDivisorCoeff ε (pronicSeq k)) -
        ∑ k ∈ Finset.Icc 1 M, pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ) := by
  rw [sieveRenormalizedPrefixDefect_eq_succ_sub_sq]
  have h1 : (∑ k ∈ Finset.Icc 1 M,
      sieveSeq N (pmPowerDampedRealWeight ε) k *
        sieveSeq N (pmPowerDampedRealWeight ε) (k + 1)) =
      ∑ k ∈ Finset.Icc 1 M, pmPowerDampedDivisorCoeff ε (pronicSeq k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1 (by omega),
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) (by omega),
      pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq]
  have h2 : (∑ k ∈ Finset.Icc 1 M,
      sieveSeq N (pmPowerDampedRealWeight ε) k ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc 1 M, pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1 (by omega)]
  rw [h1, h2]

/-- **Dirichlet Polarization of `sieveRenormalizedPrefixDefect` for `pmPowerDampedRealWeight`
(`two_mul_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq`):**
For every `ε : ℝ` and `1 ≤ M` with `M + 1 ≤ N`:
`2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) = -(∑ k ∈ Icc 1 M, (pmPowerDampedDivisorCoeff ε (k + 1) - pmPowerDampedDivisorCoeff ε k) ^ 2) + (pmPowerDampedDivisorCoeff ε (M + 1) ^ 2 - 1)`. -/
theorem two_mul_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq
    (ε : ℝ) {N M : ℕ} (hM : 1 ≤ M) (hMN : M + 1 ≤ N) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) =
      -(∑ k ∈ Finset.Icc 1 M,
          (pmPowerDampedDivisorCoeff ε (k + 1) - pmPowerDampedDivisorCoeff ε k) ^ (2 : ℕ)) +
        (pmPowerDampedDivisorCoeff ε (M + 1) ^ (2 : ℕ) - 1) := by
  rw [two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM (pmPowerDampedRealWeight ε)]
  have hdir : (∑ k ∈ Finset.Icc 1 M,
      (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc 1 M,
        (pmPowerDampedDivisorCoeff ε (k + 1) - pmPowerDampedDivisorCoeff ε k) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1 (by omega),
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) (by omega)]
  have hb1 : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) =
      pmPowerDampedDivisorCoeff ε (M + 1) :=
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) hMN
  have hb0 : sieveSeq N (pmPowerDampedRealWeight ε) 1 = 1 := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega),
      pmPowerDampedDivisorCoeff_one]
  rw [hdir, hb1, hb0]
  ring

/-- **Unconditional Non-Positivity of `sieveRenormalizedPrefixDefect` for `pmPowerDampedRealWeight`
(`sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos`):**
For every `ε ≥ 0` and `1 ≤ M` with `M + 1 ≤ N`:
`sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 - pmPowerDampedDivisorCoeff ε (M + 1) ^ 2) / 2 ≤ 0`. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M) (hMN : M + 1 ≤ N) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(1 - pmPowerDampedDivisorCoeff ε (M + 1) ^ (2 : ℕ)) / 2 ∧
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hpol := two_mul_sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_eq ε hM hMN
  have hdir_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M,
      (pmPowerDampedDivisorCoeff ε (k + 1) - pmPowerDampedDivisorCoeff ε k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg0 : 0 ≤ pmPowerDampedDivisorCoeff ε (M + 1) :=
    pmPowerDampedDivisorCoeff_nonneg hε (M + 1)
  have hg1 : pmPowerDampedDivisorCoeff ε (M + 1) ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one hε (M + 1)
  have hsq_le : pmPowerDampedDivisorCoeff ε (M + 1) ^ (2 : ℕ) ≤ 1 := by nlinarith
  constructor <;> linarith

/-- **Universal Sub-Horizon Reserve Bound for `sieveCombinedPrefixDefect` of `pmPowerDampedRealWeight`
(`sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve`):**
For every `ε ≥ 0` and `1 ≤ M` with `M + 1 ≤ N`, the combined signed LCM and Bézout defect of
`pmPowerDampedRealWeight ε` never exceeds `M * sieveSuccessorReserve N (pmPowerDampedRealWeight ε)`. -/
theorem sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hM : 1 ≤ M) (hMN : M + 1 ≤ N) :
    sieveCombinedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
      (M : ℝ) * sieveSuccessorReserve N (pmPowerDampedRealWeight ε) := by
  have hnonpos := (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos hε hM hMN).2
  unfold sieveRenormalizedPrefixDefect at hnonpos
  linarith

/-! ## §3. Master BVI Frontier Synthesis -/

/-- **Master Synthesis of the Renormalized Defect, Jordan Upper Bound, and GCD-Orbit Primitive Energy
(`bezoutValuationIncidence_renormalized_defect_and_jordan_gcd_synthesis`):**
Packages the four new unconditional pillars of `BezoutValuationIncidence`:
1. **First-Octave Renormalized Möbius Defect Law & Global Two-Octave Upper Bound
   (`moebiusCombinedPrefixDefect_first_octave_eq`,
   `moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one`):**
   Exact formula and global upper bound `moebiusCombinedPrefixDefect N M ≤ M * sieveSuccessorReserve N moebiusReal - 1`
   across the entire two-octave range `1 ≤ M ≤ 2N - 1`.
2. **Sharp `3/4` Multiplicative Jordan Upper Bound (`four_mul_jordanTotient2_le_three_mul_sq_mul_totient`)
   & Sharp Finite-Level Primitive Energy Bound (`sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance`):**
   `4 * jordanTotient2 n ≤ 3 * n² * φ(n)` for all `n ≥ 2` and
   `16 * sievePrimitiveEnergy N c ≤ N² * sieveVariance N c` for all `N, c`.
3. **Cutoff-Independent GCD-Orbit Stride Bound (`sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq`):**
   `16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤ h² * sieveVariance N c` for all `h ≥ 1`.
4. **Power-Damped Pronic `2`-Adic Ceiling & Renormalized Defect Non-Positivity
   (`pmPowerDampedDivisorCoeff_mul_succ_le_one_sub_two_rpow`,
   `sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve`).** -/
theorem bezoutValuationIncidence_renormalized_defect_and_jordan_gcd_synthesis :
    (∀ {N M : ℕ}, 2 ≤ N → 1 ≤ M → M + 1 ≤ 2 * N →
      moebiusCombinedPrefixDefect N M ≤
        (M : ℝ) * sieveSuccessorReserve N moebiusReal - 1) ∧
    (∀ {n : ℕ}, 2 ≤ n →
      4 * jordanTotient2 n ≤ 3 * (n : ℝ) ^ (2 : ℕ) * (Nat.totient n : ℝ)) ∧
    (∀ (N : ℕ) (c : ℕ → ℝ),
      16 * sievePrimitiveEnergy N c ≤ (N : ℝ) ^ (2 : ℕ) * sieveVariance N c) ∧
    (∀ (N : ℕ) {h : ℕ}, 1 ≤ h → ∀ (c : ℕ → ℝ),
      16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤
        (h : ℝ) ^ (2 : ℕ) * sieveVariance N c) ∧
    (∀ {ε : ℝ}, 0 ≤ ε → ∀ {k : ℕ}, 1 ≤ k →
      pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) ≤
        1 - (2 : ℝ) ^ (-ε)) ∧
    (∀ {ε : ℝ}, 0 ≤ ε → ∀ {N M : ℕ}, 1 ≤ M → M + 1 ≤ N →
      sieveCombinedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        (M : ℝ) * sieveSuccessorReserve N (pmPowerDampedRealWeight ε)) :=
  ⟨fun hN hM1 hM2 => moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one hN hM1 hM2,
    fun hn => four_mul_jordanTotient2_le_three_mul_sq_mul_totient hn,
    fun N c => (sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance N c).1,
    fun N _ hh c =>
      (sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq N hh c).1.trans
        (sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq N hh c).2,
    fun hε _ hk => pmPowerDampedDivisorCoeff_mul_succ_le_one_sub_two_rpow hε hk,
    fun hε _ _ hM hMN => sieveCombinedPrefixDefect_pmPowerDampedRealWeight_le_linear_reserve hε hM hMN⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
