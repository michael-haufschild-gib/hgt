import GaloisForLFunctions.BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpointHaar

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar X: Power-Damped Pronic Multiplicativity, Cellular Source Identity, and Route PM Bridge

This module bridges **Bézout–Valuation Incidence Mechanics** (`GaloisForLFunctions.BezoutValuationIncidence`)
directly to the power-damped Möbius tower of Route PM / FZZ-P
(`PMPowerDampedMobiusDivisorHaar`, `PMPowerDampedMobiusDiscreteEnergy`, `PMPowerDampedMobiusEndpointHaar`):

* `sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff`,
  `sieveSeq_pmPowerDampedRealWeight_first_octave`, &
  `sieveSeq_pmPowerDampedRealWeight_prime_first_octave`:
  For the power-damped Möbius weight `pmPowerDampedRealWeight ε d = μ(d) d^{-ε}`, the BVI sieve
  response `sieveSeq N (pmPowerDampedRealWeight ε) n` equals `pmPowerDampedDivisorCoeff ε n`
  throughout the bulk `1 ≤ n ≤ N`, and satisfies the exact first-octave reciprocity law
  `sieveSeq N (pmPowerDampedRealWeight ε) k = pmPowerDampedDivisorCoeff ε k - μ(k) k^{-ε}` on
  `N + 1 ≤ k ≤ 2N`. In particular, on every prime `p ∈ [N + 1, 2N]`, the truncated response
  `sieveSeq N (pmPowerDampedRealWeight ε) p = 1` is identically `1` (independent of `ε` and `p`).
* `pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell`:
  On every reciprocal cell `I_n = (1 / (n + 1), 1 / n]` (`1 ≤ n ≤ N`), the infinite power-damped
  Fermi–Nyman source `pmPowerDampedFermiSource ε t` is piecewise constant and equals
  `-fermiCellResponse N (pmPowerDampedRealWeight ε) n`.
* `pmPowerDampedDivisorCoeff_mul_of_coprime`,
  `pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq`, &
  `pmPowerDampedDivisorCoeff_four_sub_six_pos`:
  Because `gcd(k, k + 1) = 1`, the consecutive product of `pmPowerDampedDivisorCoeff ε` obeys the
  exact **Pronic Bézout Multiplicativity Law**:
  `pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k)`.
  For `k ≥ 2`, `pronicSeq k = k(k + 1)` has `Λ(pronicSeq k) = 0`, and at the Wall 11 transition
  (`4 = 2²` vs. `6 = 2 · 3`), `pmPowerDampedDivisorCoeff ε 4 - pmPowerDampedDivisorCoeff ε 6 = (1 - 2^{-ε}) 3^{-ε} > 0`
  for all `ε > 0`.
* `pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq`,
  `sum_sq_div_pronicSeq_add_terminal_eq_abel`, &
  `riemannHypothesis_of_pmPowerDamped_pronic_abel_budget`:
  Identifies `pmPowerDampedDivisorDiscreteEnergy ε T` as the pronic-weighted sum
  `∑_{n=1}^T (pmPowerDampedCenteredDivisorPrefix ε n)² / pronicSeq n`, establishes the exact
  Pronic Abel Summation / Discrete Dirichlet-to-Pronic Energy Identity, and connects uniform
  Pronic Abel budgets directly to `RiemannHypothesis`.
-/

/-! ## §1. Power-Damped BVI Sieve Reciprocity and Cellular Evaluation of `pmPowerDampedFermiSource` -/

/-- The real power-damped Möbius sieve weight `pmPowerDampedRealWeight ε d = μ(d) * d^{-ε}`. -/
def pmPowerDampedRealWeight (ε : ℝ) (d : ℕ) : ℝ :=
  moebiusReal d * (d : ℝ) ^ (-ε)

/-- For `1 ≤ n ≤ N`, the BVI sieve sequence `sieveSeq N (pmPowerDampedRealWeight ε) n` equals
`pmPowerDampedDivisorCoeff ε n`. -/
theorem sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff {ε : ℝ} {N n : ℕ}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    sieveSeq N (pmPowerDampedRealWeight ε) n = pmPowerDampedDivisorCoeff ε n := by
  have hdiv : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn1, (Nat.le_of_dvd hn1 hd).trans hnN⟩, hd⟩
  unfold sieveSeq pmPowerDampedDivisorCoeff pmPowerDampedRealWeight moebiusReal
  rw [hdiv]

/-- **First Trans-Horizon Octave Reciprocity for `pmPowerDampedRealWeight`
(`sieveSeq_pmPowerDampedRealWeight_first_octave`):**
For every `ε : ℝ` and every `k ∈ [N + 1, 2N]`, the only divisor of `k` exceeding `N` is `k` itself,
so `sieveSeq N (pmPowerDampedRealWeight ε) k = pmPowerDampedDivisorCoeff ε k - μ(k) * k^{-ε}`. -/
theorem sieveSeq_pmPowerDampedRealWeight_first_octave {ε : ℝ} {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) k =
      pmPowerDampedDivisorCoeff ε k - moebiusReal k * (k : ℝ) ^ (-ε) := by
  have hk_pos : 0 < k := by omega
  unfold sieveSeq pmPowerDampedDivisorCoeff
  rw [filter_dvd_Icc_eq_divisors_filter_le N hk_pos]
  have hsplit := (Finset.sum_filter_add_sum_filter_not k.divisors (fun d => d ≤ N)
    (pmPowerDampedRealWeight ε)).symm
  have hnot : k.divisors.filter (fun d => ¬ d ≤ N) = k.divisors.filter (fun d => N < d) := by
    ext d; simp only [Finset.mem_filter, not_le]
  rw [hnot, divisors_filter_gt_eq_singleton_of_first_octave hk1 hk2, Finset.sum_singleton] at hsplit
  unfold pmPowerDampedRealWeight moebiusReal at hsplit ⊢
  linarith

/-- **Scale-Invariant Unit Response on First-Octave Primes
(`sieveSeq_pmPowerDampedRealWeight_prime_first_octave`):**
For every `ε : ℝ`, `N : ℕ`, and prime `p ∈ [N + 1, 2N]`,
`sieveSeq N (pmPowerDampedRealWeight ε) p = 1` (independent of both `ε` and `p`). -/
theorem sieveSeq_pmPowerDampedRealWeight_prime_first_octave {ε : ℝ} {N p : ℕ}
    (hp : Nat.Prime p) (hp1 : N + 1 ≤ p) (hp2 : p ≤ 2 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) p = 1 := by
  rw [sieveSeq_pmPowerDampedRealWeight_first_octave hp1 hp2,
    pmPowerDampedDivisorCoeff_eq_prod ε hp.ne_zero, hp.primeFactors, Finset.prod_singleton]
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- **Exact Cellular Identification of `pmPowerDampedFermiSource` with `fermiCellResponse`
(`pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell`):**
For every `ε : ℝ`, cutoff `N : ℕ`, cell index `1 ≤ n ≤ N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`:
`pmPowerDampedFermiSource ε t = -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ)`. -/
theorem pmPowerDampedFermiSource_eq_neg_fermiCellResponse_on_cell {ε : ℝ} {N n : ℕ}
    (hn : 0 < n) (hnN : n ≤ N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    pmPowerDampedFermiSource ε t =
      -((fermiCellResponse N (pmPowerDampedRealWeight ε) n : ℝ) : ℂ) := by
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  rw [pmPowerDampedFermiSource_eq_divisor_counts ε ht_pos]
  unfold pmPowerDampedDivisorSum
  have hfloor1 : ⌊1 / t⌋₊ = n := nat_floor_inv_eq_on_reciprocal_cell hn ht
  have hfloor2 : ⌊1 / (2 * t)⌋₊ = n / 2 := by
    have heq : 1 / (2 * t) = (1 / t) / ((2 : ℕ) : ℝ) := by norm_num; ring
    rw [heq]
    have h := real_floor_div_eq_nat_div 2 (by positivity : 0 ≤ 1 / t)
    rw [hfloor1, ← Int.natCast_floor_eq_floor (by positivity)] at h
    exact Nat.cast_injective (by simpa only [Int.cast_natCast] using h)
  rw [hfloor1, hfloor2, fermiCellResponse_eq_two_prefix_half_sub_prefix]
  have hcongr_full :
      (∑ k ∈ Finset.Icc 1 n, sieveSeq N (pmPowerDampedRealWeight ε) k) =
        ∑ k ∈ Finset.Icc 1 n, pmPowerDampedDivisorCoeff ε k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1 (hkn.trans hnN)
  have hcongr_half :
      (∑ k ∈ Finset.Icc 1 (n / 2), sieveSeq N (pmPowerDampedRealWeight ε) k) =
        ∑ k ∈ Finset.Icc 1 (n / 2), pmPowerDampedDivisorCoeff ε k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkn2⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk1
      (hkn2.trans ((Nat.div_le_self n 2).trans hnN))
  rw [hcongr_full, hcongr_half]
  push_cast
  ring

/-! ## §2. Pronic Bézout Multiplicativity Law & Wall 11 Separation for `pmPowerDampedDivisorCoeff` -/

/-- **Coprime Multiplicativity of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_mul_of_coprime`):**
For every `ε : ℝ` and coprime `a, b : ℕ`,
`pmPowerDampedDivisorCoeff ε (a * b) = pmPowerDampedDivisorCoeff ε a * pmPowerDampedDivisorCoeff ε b`. -/
theorem pmPowerDampedDivisorCoeff_mul_of_coprime (ε : ℝ) {a b : ℕ} (hcop : Nat.Coprime a b) :
    pmPowerDampedDivisorCoeff ε (a * b) =
      pmPowerDampedDivisorCoeff ε a * pmPowerDampedDivisorCoeff ε b := by
  by_cases ha : a = 0
  · subst ha; simp [pmPowerDampedDivisorCoeff_zero]
  by_cases hb : b = 0
  · subst hb; simp [pmPowerDampedDivisorCoeff_zero]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hab,
    pmPowerDampedDivisorCoeff_eq_prod ε ha,
    pmPowerDampedDivisorCoeff_eq_prod ε hb,
    hcop.primeFactors_mul,
    Finset.prod_union hcop.disjoint_primeFactors]

/-- **Pronic Bézout Successor Multiplicativity Law for `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq`):**
For every `ε : ℝ` and every `k : ℕ`, because `gcd(k, k + 1) = 1`, the product of consecutive
power-damped divisor coefficients equals the single coefficient at the pronic product
`pronicSeq k = k * (k + 1)`:
`pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k)`. -/
theorem pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq (ε : ℝ) (k : ℕ) :
    pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) =
      pmPowerDampedDivisorCoeff ε (pronicSeq k) := by
  unfold pronicSeq
  have hcop : Nat.Coprime k (k + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)
  exact (pmPowerDampedDivisorCoeff_mul_of_coprime ε hcop).symm

/-- For every `ε : ℝ` and every prime power `p ^ m` (`p` prime, `m ≥ 1`),
`pmPowerDampedDivisorCoeff ε (p ^ m) = 1 - p^{-ε}` (independent of the exponent `m ≥ 1`). -/
theorem pmPowerDampedDivisorCoeff_prime_pow (ε : ℝ) {p m : ℕ}
    (hp : Nat.Prime p) (hm : m ≠ 0) :
    pmPowerDampedDivisorCoeff ε (p ^ m) = 1 - (p : ℝ) ^ (-ε) := by
  have hpm : p ^ m ≠ 0 := pow_ne_zero m hp.ne_zero
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hpm, Nat.primeFactors_pow p hm,
    hp.primeFactors, Finset.prod_singleton]

/-- **Wall 11 Separation for `pmPowerDampedDivisorCoeff` (`4 = 2²` vs. `6 = pronicSeq 2 = 2 · 3`):**
For every `ε : ℝ`:
1. At the pure prime power `4 = 2²` (`log 4`), `pmPowerDampedDivisorCoeff ε 4 = 1 - 2^{-ε}`.
2. At the first composite pronic Bézout node `6 = pronicSeq 2 = 2 * 3` (`log 6`),
   `pmPowerDampedDivisorCoeff ε 6 = (1 - 2^{-ε}) * (1 - 3^{-ε})`.
3. For every `ε > 0`, the Wall 11 defect is strictly positive:
   `pmPowerDampedDivisorCoeff ε 4 - pmPowerDampedDivisorCoeff ε 6 = (1 - 2^{-ε}) * 3^{-ε} > 0`. -/
theorem pmPowerDampedDivisorCoeff_four_and_six (ε : ℝ) :
    pmPowerDampedDivisorCoeff ε 4 = 1 - (2 : ℝ) ^ (-ε) ∧
    pmPowerDampedDivisorCoeff ε 6 = (1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) ∧
    pmPowerDampedDivisorCoeff ε 4 - pmPowerDampedDivisorCoeff ε 6 =
      (1 - (2 : ℝ) ^ (-ε)) * (3 : ℝ) ^ (-ε) := by
  have h4 : pmPowerDampedDivisorCoeff ε 4 = 1 - (2 : ℝ) ^ (-ε) := by
    have h4eq : (4 : ℕ) = 2 ^ 2 := rfl
    rw [h4eq, pmPowerDampedDivisorCoeff_prime_pow ε Nat.prime_two (by decide)]
    norm_num
  have h2 : pmPowerDampedDivisorCoeff ε 2 = 1 - (2 : ℝ) ^ (-ε) := by
    have h2eq : (2 : ℕ) = 2 ^ 1 := rfl
    rw [h2eq, pmPowerDampedDivisorCoeff_prime_pow ε Nat.prime_two (by decide)]
    norm_num
  have h3 : pmPowerDampedDivisorCoeff ε 3 = 1 - (3 : ℝ) ^ (-ε) := by
    have h3eq : (3 : ℕ) = 3 ^ 1 := rfl
    rw [h3eq, pmPowerDampedDivisorCoeff_prime_pow ε Nat.prime_three (by decide)]
    norm_num
  have h6 : pmPowerDampedDivisorCoeff ε 6 = (1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) := by
    have hpronic : pronicSeq 2 = 6 := rfl
    rw [← hpronic, ← pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq ε 2, h2, h3]
  refine ⟨h4, h6, ?_⟩
  rw [h4, h6]
  ring

/-- For every `ε > 0`, `pmPowerDampedDivisorCoeff ε 6 < pmPowerDampedDivisorCoeff ε 4`. -/
theorem pmPowerDampedDivisorCoeff_six_lt_four {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedDivisorCoeff ε 6 < pmPowerDampedDivisorCoeff ε 4 := by
  obtain ⟨_, _, hdiff⟩ := pmPowerDampedDivisorCoeff_four_and_six ε
  have h2 : (2 : ℝ) ^ (-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3 : 0 < (3 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) (-ε)
  have hpos : 0 < (1 - (2 : ℝ) ^ (-ε)) * (3 : ℝ) ^ (-ε) :=
    mul_pos (sub_pos.mpr h2) h3
  linarith

/-! ## §3. Pronic Summation by Parts for `pmPowerDampedDivisorDiscreteEnergy` & Route PM Bridge -/

/-- **Pronic Denominator Form of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T = ∑_{n=1}^T (pmPowerDampedCenteredDivisorPrefix ε n)² / pronicSeq n`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      ∑ n ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
  unfold pmPowerDampedDivisorDiscreteEnergy pronicSeq
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  rfl

/-- **Exact Pronic Abel Summation / Discrete Dirichlet-to-Pronic Energy Identity
(`sum_sq_div_pronicSeq_add_terminal_eq_abel`):**
For every sequence `A : ℕ → ℝ` and every horizon `T ≥ 1`:
`∑_{n=1}^T A(n)² / pronicSeq n + A(T)² / (T + 1) = A(1)² + ∑_{n=1}^{T-1} (A(n + 1)² - A(n)²) / (n + 1)`. -/
theorem sum_sq_div_pronicSeq_add_terminal_eq_abel (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, A n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      A T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      A 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, T = m + 1 := ⟨T - 1, by omega⟩
  clear hT
  induction m with
  | zero =>
    simp only [zero_add, Nat.sub_self, Finset.Icc_self, Finset.sum_singleton,
      Finset.Icc_eq_empty (by decide : ¬ (1 ≤ 0)), Finset.sum_empty, add_zero]
    unfold pronicSeq
    norm_num
  | succ m ih =>
    have hsplit_lhs :
        Finset.Icc 1 (m + 1 + 1) = insert (m + 1 + 1) (Finset.Icc 1 (m + 1)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_lhs : m + 1 + 1 ∉ Finset.Icc 1 (m + 1) := by
      simp only [Finset.mem_Icc]; omega
    have hsplit_rhs :
        Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_rhs : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit_lhs, Finset.sum_insert hnot_lhs]
    simp only [Nat.add_sub_cancel] at ih ⊢
    have hrhs :
        (∑ n ∈ Finset.Icc 1 (m + 1),
          (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ)) / ((n : ℝ) + 1)) =
        (A (m + 1 + 1) ^ (2 : ℕ) - A (m + 1) ^ (2 : ℕ)) / (((m + 1 : ℕ) : ℝ) + 1) +
          ∑ n ∈ Finset.Icc 1 m,
            (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
      rw [hsplit_rhs, Finset.sum_insert hnot_rhs]
    have hpronic :
        A (m + 1 + 1) ^ (2 : ℕ) / (pronicSeq (m + 1 + 1) : ℝ) +
          A (m + 1 + 1) ^ (2 : ℕ) / (((m + 1 + 1 : ℕ) : ℝ) + 1) -
          A (m + 1) ^ (2 : ℕ) / (((m + 1 : ℕ) : ℝ) + 1) =
          (A (m + 1 + 1) ^ (2 : ℕ) - A (m + 1) ^ (2 : ℕ)) / (((m + 1 : ℕ) : ℝ) + 1) := by
      unfold pronicSeq
      have h1 : (((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (((m + 1 + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    linarith

/-- **Exact Pronic Abel Decomposition of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_abel`):**
For every `ε : ℝ` and `T ≥ 1`:
`pmPowerDampedDivisorDiscreteEnergy ε T + (pmPowerDampedCenteredDivisorPrefix ε T)² / (T + 1)`
equals `(pmPowerDampedCenteredDivisorCoeff ε 1)²` plus
`∑_{n=1}^{T-1} ((pmPowerDampedCenteredDivisorPrefix ε (n + 1))² - (pmPowerDampedCenteredDivisorPrefix ε n)²) / (n + 1)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_abel (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPowerDampedDivisorDiscreteEnergy ε T +
      pmPowerDampedCenteredDivisorPrefix ε T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
            pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
    sum_sq_div_pronicSeq_add_terminal_eq_abel (pmPowerDampedCenteredDivisorPrefix ε) hT]
  have h1 : pmPowerDampedCenteredDivisorPrefix ε 1 = pmPowerDampedCenteredDivisorCoeff ε 1 := by
    unfold pmPowerDampedCenteredDivisorPrefix
    simp
  rw [h1]

/-- For every `ε : ℝ` and `T ≥ 1`, dropping the non-negative terminal boundary term
`(pmPowerDampedCenteredDivisorPrefix ε T)² / (T + 1) ≥ 0` bounds
`pmPowerDampedDivisorDiscreteEnergy ε T` by its Pronic Abel sum. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_abel (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
            pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
  have hterm : 0 ≤ pmPowerDampedCenteredDivisorPrefix ε T ^ (2 : ℕ) / ((T : ℝ) + 1) := by
    positivity
  linarith [pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_abel ε hT]

/-- **Route PM Pronic Abel Budget Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmPowerDamped_pronic_abel_budget`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that the Pronic Abel
sum of `pmPowerDampedCenteredDivisorPrefix ε` is bounded by `B` for all `T ≥ 1`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmPowerDamped_pronic_abel_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T →
        pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) +
          (∑ n ∈ Finset.Icc 1 (T - 1),
            (pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
              pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ)) / ((n : ℝ) + 1)) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, max B 0, fun T => ?_⟩
  by_cases hT : 1 ≤ T
  · exact (pmPowerDampedDivisorDiscreteEnergy_le_abel ε hT).trans
      ((hB T hT).trans (le_max_left B 0))
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmPowerDampedDivisorDiscreteEnergy
    simp [le_max_right B 0]

end
end GaloisForLFunctions.BezoutValuationIncidence
