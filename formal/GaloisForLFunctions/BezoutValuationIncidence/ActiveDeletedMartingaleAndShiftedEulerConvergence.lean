import GaloisForLFunctions.BezoutValuationIncidence.ActiveSawtoothClosedFormAndShiftedExponentTotientBridge
import GaloisForLFunctions.BezoutValuationIncidence.PredictableMartingaleDecompositionAndCovarianceCancellationBridge

/-!
# Pillar XIX: Active-Deleted Martingale Identity & Shifted-Exponent Euler Product Convergence (`ε ↦ 1 + ε`)

In Pillar XVII (`SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance`) and Pillar XVIII
(`ActiveSawtoothClosedFormAndShiftedExponentTotientBridge`), we proved that across each step
`n ↦ n + 1`:
1. The active sawtooth sum `activeCenteredSawtoothSum N c (n + 1) n` flips sign and its square
   cancels identically in `W(n + 1)² - W(n)²`.
2. In exact closed form,
   `activeCenteredSawtoothSum N c (n + 1) n = -(1 / 2) * (sieveSeq N c (n + 1) - sieveSeq N (fun d => c d / d) (n + 1))`,
   while the inactive drift is
   `inactiveCenteredSawtoothSum N c (n + 1) (n + 1) - inactiveCenteredSawtoothSum N c (n + 1) n = sieveSeq N (fun d => c d / d) (n + 1) - selbergMultiplesCoord N c 1`.

In this nineteenth pillar of **Bézout–Valuation Incidence Mechanics**, we combine these two laws
with the predictable martingale decomposition (Pillar XIII) to prove the **Active-Deleted Martingale
Identity**: absorbing the deterministic active pre-jump component `2 * ΔW(n) * A(n + 1, n)` into the
diagonal square `ΔW(n)²` **eliminates the divergent square `(sieveSeq N c (n + 1) - Y_N(1))²`** and
replaces it with the **active-deleted shifted-exponent product**
`(sieveSeq N c (n + 1) - Y_N(1)) * (sieveSeq N (fun d => c d / d) (n + 1) - Y_N(1))`.

For Route PM's power-damped Möbius weight `c_ε = pmPowerDampedRealWeight ε`, this replaces the
divergent diagonal square `τ_ε(m)²` (whose local Euler factor gap is `(p^{-ε})²(p - 1)/p² ~ 1/p^{1+2ε}`,
diverging like `1/(2ε)` over primes as `ε → 0⁺`) by the **shifted-exponent totient product**
`τ_ε(m) * τ_{1+ε}(m)`, whose local Euler factor gap is **divided by an extra factor of `p`**
(`(p^{-ε})²(p - 1)/p³ ≤ 1/p²`), making it uniformly summable over all primes down to `ε = 0`!

## Core Main Theorems (100% Unconditional)

1. **Active-Deleted Martingale Identity & Pronic Abel Summation
   (`active_diagonal_reduction`,
   `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale`,
   `sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_active_deleted`,
   `weightedCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sq_sub_sq_active_deleted`)**:
   For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ`:
   $$W_{N,c}(n + 1)^2 - W_{N,c}(n)^2 =
     \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\bigl(s_{N, c/d}(n + 1) - Y_{N,c}(1)\bigr) +
     2\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,\operatorname{inactiveCenteredSawtoothSum}\,N\,c\,(n + 1)\,n.$$
   For `c = pmPowerDampedRealWeight ε` and `n + 1 ≤ N`, the active-deleted diagonal term is
   `(τ_ε(n + 1) - Y_N(1)) * (τ_{1+ε}(n + 1) - Y_N(1))`.

2. **Shifted-Exponent Totient Dominance & Divisor-Sum Representation of `τ_ε(n) * τ_{1+ε}(n)`
   (`pmPowerDampedDivisorCoeff_le_add_one`,
   `activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_nonneg`,
   `pmPowerDampedDivisorCoeff_mul_add_one`)**:
   For every `ε ≥ 0` and `n : ℕ`, `0 ≤ τ_ε(n) ≤ τ_{1+ε}(n) ≤ 1`, and for all `ε : ℝ`,
   $$\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n) =
     \sum_{d \in n.\text{divisors}} \operatorname{pmShiftedExponentSecondCoeff}\,\varepsilon\,d.$$

3. **One-`$p$-th` Suppression of the Shifted-Exponent Euler Factor Gap & Uniform Prime Deficit Convergence
   (`pmShiftedExponentFactor_gap`,
   `pmShiftedExponentFactor_gap_eq_div_p`,
   `pmShiftedExponentPrimeDeficit_bounds`,
   `tendsto_tsum_pmShiftedExponentPrimeDeficit`)**:
   For every `ε : ℝ` and `p > 0`:
   $$\left(1 - \frac{\operatorname{pmShiftedExponentSecondWeight}\,\varepsilon\,p}{p}\right) -
     \left(1 - \frac{p^{-\varepsilon}}{p}\right)\left(1 - \frac{p^{-(1+\varepsilon)}}{p}\right) =
     \frac{(p^{-\varepsilon})^2 (p - 1)}{p^3} =
     \frac{\bigl(1 - \operatorname{pmPowerDampedSecondWeight}\,\varepsilon\,p / p\bigr) -
       \bigl(1 - p^{-\varepsilon} / p\bigr)^2}{p},$$
   and the relative prime deficit `pmShiftedExponentPrimeDeficit ε p` between the local Euler factor
   of `τ_ε(n) * τ_{1+ε}(n)` and `1 - p^{-ε}/p` is bounded by `4 / p²` uniformly for all `ε ≥ 0` and
   satisfies `∑'_{p} pmShiftedExponentPrimeDeficit ε p → 0` as `ε → 0⁺`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Active-Deleted Martingale Identity & Pronic Abel Summation -/

/-- **Active-Martingale Diagonal Reduction (`active_diagonal_reduction`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, combining the diagonal square increment
`(sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1)²` with twice the active pre-jump product
`2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) * activeCenteredSawtoothSum N c (n + 1) n`
cancels `sieveSeq N c (n + 1)` in the second factor and replaces it with the harmonic-divided sieve
`sieveSeq N (fun d => c d / d) (n + 1)`. -/
theorem active_diagonal_reduction (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) ^ (2 : ℕ) +
      2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        activeCenteredSawtoothSum N c (n + 1) n =
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) := by
  rw [activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub]
  ring

/-- **Exact Active-Deleted Martingale Identity for `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the square increment
`weightedCenteredSawtoothSum N c (n + 1)² - weightedCenteredSawtoothSum N c n²` decomposes into
the **active-deleted shifted-diagonal product**
`(sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) * (sieveSeq N (fun d => c d / d) (n + 1) - selbergMultiplesCoord N c 1)`
plus twice the **purely inactive predictable martingale product**
`2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) * inactiveCenteredSawtoothSum N c (n + 1) n`. -/
theorem weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) =
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) +
      2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        inactiveCenteredSawtoothSum N c (n + 1) n := by
  rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_inactive_midpoint]
  have hinact := inactiveCenteredSawtoothSum_succ_sub_eq N c n
  linarith [congrArg
    (fun x => (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) * x) hinact]

/-- **Active-Deleted Pronic Abel Summation Identity
(`sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_active_deleted`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `T ≥ 1`, the Pronic energy of `weightedCenteredSawtoothSum N c`
decomposes into the harmonic sum of active-deleted shifted-diagonal products plus twice the harmonic
sum of purely inactive predictable martingale increments. -/
theorem sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_active_deleted
    (N : ℕ) (c : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T,
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      weightedCenteredSawtoothSum N c T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      (weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          ((sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
            (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) -
              selbergMultiplesCoord N c 1)) / ((n : ℝ) + 1)) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1),
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
            inactiveCenteredSawtoothSum N c (n + 1) n / ((n : ℝ) + 1) := by
  rw [sum_sq_div_pronicSeq_add_terminal_eq_abel (weightedCenteredSawtoothSum N c) hT]
  have hrew :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
          weightedCenteredSawtoothSum N c n ^ (2 : ℕ)) / ((n : ℝ) + 1)) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) -
            selbergMultiplesCoord N c 1)) / ((n : ℝ) + 1)) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1),
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
            inactiveCenteredSawtoothSum N c (n + 1) n / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale]
    ring
  linarith

/-- **Sub-Horizon Active-Deleted Martingale Identity for `pmPowerDampedRealWeight ε`
(`weightedCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sq_sub_sq_active_deleted`):**
For every `ε : ℝ` and every sub-horizon step `n + 1 ≤ N`:
`W(n + 1)² - W(n)² = (τ_ε(n + 1) - Y_N(1)) * (τ_{1+ε}(n + 1) - Y_N(1)) + 2 * (τ_ε(n + 1) - Y_N(1)) * inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n`. -/
theorem weightedCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sq_sub_sq_active_deleted
    (ε : ℝ) {N n : ℕ} (hnN : n + 1 ≤ N) :
    weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) n ^ (2 : ℕ) =
      (pmPowerDampedDivisorCoeff ε (n + 1) -
        selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1) *
        (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) -
          selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1) +
      2 * (pmPowerDampedDivisorCoeff ε (n + 1) -
        selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1) *
        inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n := by
  rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ n + 1) hnN,
    sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one ε (by omega : 1 ≤ n + 1) hnN]

/-! ## §2. Shifted-Exponent Totient Dominance & Divisor-Sum Structure of `τ_ε(n) * τ_{1+ε}(n)` -/

/-- For every `ε : ℝ` and `p : ℕ` with `0 < p`:
`(p : ℝ) ^ (-(1 + ε)) = (p : ℝ) ^ (-ε) / (p : ℝ)`. -/
theorem pm_prime_rpow_add_one (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    (p : ℝ) ^ (-(1 + ε)) = (p : ℝ) ^ (-ε) / (p : ℝ) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  rw [ ← Real.rpow_sub_one hp_pos.ne']
  congr 1
  ring

/-- **Shifted-Exponent Totient Dominance (`pmPowerDampedDivisorCoeff_le_add_one`):**
For every `ε ≥ 0` and every `n : ℕ`:
`0 ≤ pmPowerDampedDivisorCoeff ε n` and
`pmPowerDampedDivisorCoeff ε n ≤ pmPowerDampedDivisorCoeff (1 + ε) n`. -/
theorem pmPowerDampedDivisorCoeff_le_add_one {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ pmPowerDampedDivisorCoeff ε n ∧
      pmPowerDampedDivisorCoeff ε n ≤ pmPowerDampedDivisorCoeff (1 + ε) n := by
  by_cases hn : n = 0
  · subst hn
    simp [pmPowerDampedDivisorCoeff_zero]
  · rw [pmPowerDampedDivisorCoeff_eq_prod ε hn,
      pmPowerDampedDivisorCoeff_eq_prod (1 + ε) hn]
    have hnonneg : ∀ p ∈ n.primeFactors, (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-ε) := by
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      have ht1 : (p : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hε)
      linarith
    have hle : ∀ p ∈ n.primeFactors,
        1 - (p : ℝ) ^ (-ε) ≤ 1 - (p : ℝ) ^ (-(1 + ε)) := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      have hp_pos : (0 : ℝ) < p := by linarith
      have ht_nonneg : 0 ≤ (p : ℝ) ^ (-ε) := Real.rpow_nonneg hp_pos.le (-ε)
      rw [pm_prime_rpow_add_one ε hp_prime.pos]
      have hdiv : (p : ℝ) ^ (-ε) / (p : ℝ) ≤ (p : ℝ) ^ (-ε) :=
        div_le_self ht_nonneg (by linarith)
      linarith
    exact ⟨Finset.prod_nonneg hnonneg, Finset.prod_le_prod hnonneg hle⟩

/-- **Sign of the Active Sawtooth Sum Before the Jump (`activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_nonneg`):**
For every `ε ≥ 0` and every sub-horizon step `n + 1 ≤ N`, because `τ_ε(n + 1) ≤ τ_{1+ε}(n + 1)`,
the pre-jump active sawtooth sum is non-negative:
`0 ≤ activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n`. -/
theorem activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_nonneg
    {ε : ℝ} (hε : 0 ≤ ε) {N n : ℕ} (hnN : n + 1 ≤ N) :
    0 ≤ activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n := by
  rw [activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_eq ε hnN]
  have hle := (pmPowerDampedDivisorCoeff_le_add_one hε (n + 1)).2
  linarith

/-- The shifted-exponent local weight at prime `p` for the product `τ_ε(n) * τ_{1+ε}(n)`:
`pmShiftedExponentSecondWeight ε p = p^{-ε} + p^{-(1+ε)} - p^{-ε} * p^{-(1+ε)}`. -/
def pmShiftedExponentSecondWeight (ε : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-ε) + (p : ℝ) ^ (-(1 + ε)) - (p : ℝ) ^ (-ε) * (p : ℝ) ^ (-(1 + ε))

/-- The damped Möbius arithmetic function generating the shifted-exponent divisor product
`τ_ε(n) * τ_{1+ε}(n) = ∑_{d ∣ n} pmShiftedExponentSecondCoeff ε d`. -/
def pmShiftedExponentSecondCoeff (ε : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.dampedMobius (pmShiftedExponentSecondWeight ε)

/-- **Divisor-Sum Representation of the Active-Deleted Product `τ_ε(n) * τ_{1+ε}(n)`
(`pmPowerDampedDivisorCoeff_mul_add_one`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n = ∑ d ∈ n.divisors, pmShiftedExponentSecondCoeff ε d`. -/
theorem pmPowerDampedDivisorCoeff_mul_add_one (ε : ℝ) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n =
      ∑ d ∈ n.divisors, pmShiftedExponentSecondCoeff ε d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (DampedMobius.dampedMobius_mul_zeta (pmShiftedExponentSecondWeight ε))
  rw [coe_mul_zeta_apply] at h
  rw [show (∑ d ∈ n.divisors, pmShiftedExponentSecondCoeff ε d) =
    DampedMobius.divisorSum (pmShiftedExponentSecondWeight ε) n from h]
  by_cases hn : n = 0
  · subst hn
    simp [pmPowerDampedDivisorCoeff_zero]
  · rw [pmPowerDampedDivisorCoeff_eq_prod ε hn,
      pmPowerDampedDivisorCoeff_eq_prod (1 + ε) hn,
      DampedMobius.divisorSum, prodPrimeFactors_apply hn, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    dsimp only [pmShiftedExponentSecondWeight]
    ring

/-! ## §3. One-`$p$-th` Suppression of the Shifted-Exponent Euler Factor Gap & Uniform Prime Deficit -/

/-- For every `ε : ℝ` and `p : ℕ` with `0 < p`:
`pmShiftedExponentSecondWeight ε p = p^{-ε} + p^{-ε} * (1 - p^{-ε}) / p`. -/
theorem pmShiftedExponentSecondWeight_eq (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    pmShiftedExponentSecondWeight ε p =
      (p : ℝ) ^ (-ε) + (p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) / (p : ℝ) := by
  unfold pmShiftedExponentSecondWeight
  rw [pm_prime_rpow_add_one ε hp]
  ring

/-- **Exact Perturbation of the Shifted-Exponent Euler Factor from `1 - p^{-ε} / p`
(`pmShiftedExponentFactor_sub_divisorFactor`):**
For every `ε : ℝ` and `p : ℕ` with `0 < p`:
`(1 - pmShiftedExponentSecondWeight ε p / p) - (1 - p^{-ε} / p) = -p^{-ε} * (1 - p^{-ε}) / p²`. -/
theorem pmShiftedExponentFactor_sub_divisorFactor (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    (1 - pmShiftedExponentSecondWeight ε p / (p : ℝ)) -
      (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) =
      -((p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) / (p : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [pmShiftedExponentSecondWeight_eq ε hp]
  field_simp [hpR]
  ring

/-- **Exact Local Covariance Gap of the Shifted-Exponent Product `τ_ε(n) * τ_{1+ε}(n)`
(`pmShiftedExponentFactor_gap`):**
For every `ε : ℝ` and `p : ℕ` with `0 < p`, the local Euler factor gap between
`1 - pmShiftedExponentSecondWeight ε p / p` and `(1 - p^{-ε} / p) * (1 - p^{-(1+ε)} / p)` is
`((p : ℝ)^{-ε})² * (p - 1) / p³` (with `p³` in the denominator instead of `p²`!). -/
theorem pmShiftedExponentFactor_gap (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    (1 - pmShiftedExponentSecondWeight ε p / (p : ℝ)) -
      (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) * (1 - (p : ℝ) ^ (-(1 + ε)) / (p : ℝ)) =
      ((p : ℝ) ^ (-ε)) ^ 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 3 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold pmShiftedExponentSecondWeight
  rw [pm_prime_rpow_add_one ε hp]
  field_simp [hpR]
  ring

/-- **One-`$p$-th` Suppression of the Shifted-Exponent Local Gap Relative to the Unshifted Gap
(`pmShiftedExponentFactor_gap_eq_div_p`):**
For every `ε : ℝ` and `p : ℕ` with `0 < p`, the local Euler factor gap of the active-deleted
product `τ_ε(n) * τ_{1+ε}(n)` equals **one-`$p$-th`** of the unshifted second-moment local gap
`(1 - pmPowerDampedSecondWeight ε p / p) - (1 - p^{-ε} / p)²`. -/
theorem pmShiftedExponentFactor_gap_eq_div_p (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    (1 - pmShiftedExponentSecondWeight ε p / (p : ℝ)) -
      (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) * (1 - (p : ℝ) ^ (-(1 + ε)) / (p : ℝ)) =
      ((1 - pmPowerDampedSecondWeight ε p / (p : ℝ)) -
        (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) ^ 2) / (p : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [pmShiftedExponentFactor_gap ε hp, pmPowerDampedSecondFactor_gap ε hp]
  field_simp [hpR]

/-- The relative prime deficit between the shifted-exponent local Euler factor
`1 - pmShiftedExponentSecondWeight ε p / p` and the single divisor density Euler factor
`1 - p^{-ε} / p`:
`pmShiftedExponentPrimeDeficit ε p = p^{-ε} * (1 - p^{-ε}) / (p * (p - p^{-ε}))`. -/
def pmShiftedExponentPrimeDeficit (ε : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε))) / ((p : ℝ) * ((p : ℝ) - (p : ℝ) ^ (-ε)))

/-- **Exact Ratio Factorization of the Shifted-Exponent Euler Factor (`pmShiftedExponentPrimeDeficit_eq_one_sub_div`):**
For every `ε ≥ 0` and every prime `p : Nat.Primes`:
`(1 - pmShiftedExponentSecondWeight ε p / p) / (1 - p^{-ε} / p) = 1 - pmShiftedExponentPrimeDeficit ε p`. -/
theorem pmShiftedExponentPrimeDeficit_eq_one_sub_div {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    (1 - pmShiftedExponentSecondWeight ε p / (p : ℝ)) /
      (1 - (p : ℝ) ^ (-ε) / (p : ℝ)) =
      1 - pmShiftedExponentPrimeDeficit ε p := by
  let t := (p : ℝ) ^ (-ε)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hε)
  have hd : (p : ℝ) - t ≠ 0 := by linarith
  have hf : 1 - t / (p : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one hp0).mpr (by linarith)))
  rw [pmShiftedExponentSecondWeight_eq ε p.property.pos]
  unfold pmShiftedExponentPrimeDeficit
  change (1 - (t + t * (1 - t) / (p : ℝ)) / (p : ℝ)) / (1 - t / (p : ℝ)) =
    1 - (t * (1 - t)) / ((p : ℝ) * ((p : ℝ) - t))
  field_simp [hp0.ne', hd, hf]
  ring

/-- **Uniform `O(1 / p²)` Bounds on `pmShiftedExponentPrimeDeficit` (`pmShiftedExponentPrimeDeficit_bounds`):**
For every `ε ≥ 0` and every prime `p : Nat.Primes`:
`0 ≤ pmShiftedExponentPrimeDeficit ε p`, `pmShiftedExponentPrimeDeficit ε p ≤ 1`, and
`pmShiftedExponentPrimeDeficit ε p ≤ 4 / p²`. -/
theorem pmShiftedExponentPrimeDeficit_bounds {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    0 ≤ pmShiftedExponentPrimeDeficit ε p ∧
      pmShiftedExponentPrimeDeficit ε p ≤ 1 ∧
        pmShiftedExponentPrimeDeficit ε p ≤ 4 / (p : ℝ) ^ 2 := by
  let t := (p : ℝ) ^ (-ε)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hε)
  have hn0 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hn1 : t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg t]
  have hd1 : (1 : ℝ) ≤ (p : ℝ) - t := by linarith
  have hd0 : 0 < (p : ℝ) - t := by linarith
  have hden0 : 0 < (p : ℝ) * ((p : ℝ) - t) := mul_pos hp0 hd0
  have hq0 : 0 ≤ (t * (1 - t)) / ((p : ℝ) * ((p : ℝ) - t)) := div_nonneg hn0 hden0.le
  have hq1 : (t * (1 - t)) / ((p : ℝ) * ((p : ℝ) - t)) ≤ 1 :=
    (div_le_one hden0).mpr (by nlinarith)
  have hq2 : (t * (1 - t)) / ((p : ℝ) * ((p : ℝ) - t)) ≤ 4 / (p : ℝ) ^ 2 := by
    calc
      (t * (1 - t)) / ((p : ℝ) * ((p : ℝ) - t))
        ≤ 1 / ((p : ℝ) * ((p : ℝ) - t)) := div_le_div_of_nonneg_right hn1 hden0.le
      _ ≤ 4 / (p : ℝ) ^ 2 := (div_le_div_iff₀ hden0 (sq_pos_of_pos hp0)).mpr (by nlinarith)
  exact ⟨hq0, hq1, hq2⟩

/-- For every `ε ≥ 0`, `pmShiftedExponentPrimeDeficit ε` is summable over all primes. -/
theorem summable_pmShiftedExponentPrimeDeficit {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (pmShiftedExponentPrimeDeficit ε) :=
  Summable.of_nonneg_of_le (fun p => (pmShiftedExponentPrimeDeficit_bounds hε p).1)
    (fun p => (pmShiftedExponentPrimeDeficit_bounds hε p).2.2)
    summable_pm_variance_prime_majorant

/-- For every prime `p : Nat.Primes`, `pmShiftedExponentPrimeDeficit ε p → 0` as `ε → 0⁺`. -/
theorem tendsto_pmShiftedExponentPrimeDeficit (p : Nat.Primes) :
    Tendsto (fun ε : ℝ => pmShiftedExponentPrimeDeficit ε p) (𝓝[>] 0) (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hc : Continuous (fun ε : ℝ => (p : ℝ) ^ (-ε)) :=
    (Real.continuous_const_rpow hp0).comp continuous_neg
  have ht : Tendsto (fun ε : ℝ => (p : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (ht.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)).div
    ((tendsto_const_nhds (x := (p : ℝ))).mul ((tendsto_const_nhds (x := (p : ℝ))).sub ht))
    (mul_ne_zero hp0 (sub_ne_zero.mpr hp1.ne'))
  simpa [pmShiftedExponentPrimeDeficit, Pi.div_def] using h

/-- **Small-Damping Vanishing of the Total Shifted-Exponent Prime Deficit
(`tendsto_tsum_pmShiftedExponentPrimeDeficit`):**
As `ε → 0⁺`, the sum over all primes of `pmShiftedExponentPrimeDeficit ε p` converges to `0`:
`Tendsto (fun ε => ∑' p : Nat.Primes, pmShiftedExponentPrimeDeficit ε p) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_tsum_pmShiftedExponentPrimeDeficit :
    Tendsto (fun ε : ℝ => ∑' p : Nat.Primes, pmShiftedExponentPrimeDeficit ε p)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence summable_pm_variance_prime_majorant
    tendsto_pmShiftedExponentPrimeDeficit (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ p : Nat.Primes, ‖pmShiftedExponentPrimeDeficit ε p‖ ≤ 4 / (p : ℝ) ^ 2 from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        intro p
        have h := pmShiftedExponentPrimeDeficit_bounds (show 0 ≤ ε from le_of_lt hε) p
        rw [Real.norm_eq_abs, abs_of_nonneg h.1]
        exact h.2.2)
  simpa using h

end
end GaloisForLFunctions.BezoutValuationIncidence
