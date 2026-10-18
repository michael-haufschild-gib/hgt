import GaloisForLFunctions.BezoutValuationIncidence.ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance
import GaloisForLFunctions.BezoutValuationIncidence.SawtoothBezoutSuccessorGradientAndRouteFZZPBridge

/-!
# Pillar XVII: Sawtooth Midpoint Annihilation, Active-Divisor Square Invariance, & Route PM / FZZ-P Affine Bridge

In this seventeenth pillar of **Bézout–Valuation Incidence Mechanics**, we uncover the exact
pointwise mechanism by which the predictable martingale increment cancels the diagonal jump square
in the Pronic Abel sum of `weightedCenteredSawtoothSum` (and `pmPowerDampedRamanujanCenteredSawtoothPrefix`),
and prove that the difference between Route PM's `pmPowerDampedCenteredDivisorPrefix` and
`weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε)` has **zero arithmetic oscillation**
across the entire sub-horizon bulk $0 \le n \le N$.

## Core Main Theorems (100% Unconditional)

1. **Pointwise Active-Divisor Sign Flip, Midpoint Annihilation, & Square Invariance
   (`centeredDiscreteSawtooth_of_dvd_succ`,
   `centeredDiscreteSawtooth_succ_eq_neg_of_dvd`,
   `centeredDiscreteSawtooth_add_succ_eq_zero_of_dvd`,
   `centeredDiscreteSawtooth_succ_sq_eq_sq_of_dvd`,
   `centeredDiscreteSawtooth_addDiff_sq_add_two_mul_eq_zero_of_dvd`)**:
   For **every** modulus `d > 0` and **every** `n : ℕ` (including `n = 0`) such that `d ∣ (n + 1)`:
   - At the predecessor `n`, `centeredDiscreteSawtooth d n = +(d - 1) / (2d)`.
   - At the multiple `n + 1`, `centeredDiscreteSawtooth d (n + 1) = -(d - 1) / (2d) = -centeredDiscreteSawtooth d n`.
   - Consequently, across every divisibility event `d ∣ (n + 1)`, the midpoint sum vanishes
     (`centeredDiscreteSawtooth d n + centeredDiscreteSawtooth d (n + 1) = 0`), the square is
     invariant (`centeredDiscreteSawtooth d (n + 1)² = centeredDiscreteSawtooth d n²`), and the
     squared jump `addDiff (centeredDiscreteSawtooth d) n ^ 2` is cancelled **100% pointwise** by
     twice the predictable martingale product:
     $$\operatorname{addDiff}(\operatorname{centeredDiscreteSawtooth}\,d)\,n ^ 2 +
       2\,\operatorname{addDiff}(\operatorname{centeredDiscreteSawtooth}\,d)\,n \cdot
       \operatorname{centeredDiscreteSawtooth}\,d\,n = 0.$$

2. **Active/Inactive Divisor Decomposition & Active-Square Cancellation in Pronic Abel Sums
   (`weightedCenteredSawtoothSum_eq_active_add_inactive`,
   `activeCenteredSawtoothSum_add_succ_eq_zero`,
   `weightedCenteredSawtoothSum_add_succ_eq_inactive_add_succ`,
   `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_inactive_midpoint`,
   `weightedCenteredSawtoothSum_succ_sq_sub_sq_active_sq_cancelled`)**:
   Splitting `weightedCenteredSawtoothSum N c k` at step `n + 1` into `activeCenteredSawtoothSum N c (n + 1) k`
   (`d ∣ (n + 1)`) plus `inactiveCenteredSawtoothSum N c (n + 1) k` (`d ∤ (n + 1)`):
   - The active component flips sign across `n ↦ n + 1`, so its midpoint sum is `0` and its square
     `activeCenteredSawtoothSum N c (n + 1) (n + 1)² = activeCenteredSawtoothSum N c (n + 1) n²`
     cancels **100% identically** in `weightedCenteredSawtoothSum N c (n + 1)² - weightedCenteredSawtoothSum N c n²`.
   - Thus in the Pronic Abel numerator `(W(n + 1) - W(n))(W(n + 1) + W(n))`, the midpoint factor
     `W(n + 1) + W(n)` is supported **exclusively on inactive (non-dividing) moduli `d ∤ (n + 1)`**.

3. **Zero-Oscillation Affine Bridge Between Route PM and `weightedCenteredSawtoothSum`
   (`addDiff_pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum`,
   `pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum_eq_affine`)**:
   For every `ε : ℝ` and every sub-horizon step `k + 1 ≤ N`, the divisibility impulses in
   `pmPowerDampedCenteredDivisorPrefix ε` and `weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε)`
   cancel identically, leaving a constant forward difference independent of `k`:
   $$\operatorname{addDiff}\bigl(A_\varepsilon - W_{N,\varepsilon}\bigr)(k) =
     \operatorname{selbergMultiplesCoord}\,N\,c_\varepsilon\,1 - \alpha_\varepsilon,$$
   and hence for every `n ≤ N`:
   $$A_\varepsilon(n) - W_{N,\varepsilon}(n) =
     -W_{N,\varepsilon}(0) + n \cdot \bigl(\operatorname{selbergMultiplesCoord}\,N\,c_\varepsilon\,1 - \alpha_\varepsilon\bigr).$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Pointwise Active-Divisor Sign Flip, Midpoint Annihilation, & Square Invariance -/

/-- For every `d > 0` and **all** `n : ℕ` (including `n = 0`) such that `d ∣ (n + 1)`, the sawtooth
at the predecessor `n` is locked at its positive maximum `(d - 1) / (2d)`. -/
theorem centeredDiscreteSawtooth_of_dvd_succ {d n : ℕ} (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d n = ((d : ℝ) - 1) / (2 * (d : ℝ)) :=
  centeredDiscreteSawtooth_pred_of_dvd hd (by omega : 0 < n + 1) hdvd

/-- **Pointwise Active-Divisor Sign Flip (`centeredDiscreteSawtooth_succ_eq_neg_of_dvd`):**
For every `d > 0` and `n : ℕ` such that `d ∣ (n + 1)`, stepping from `n` to `n + 1` flips the sign
of `centeredDiscreteSawtooth d`:
`centeredDiscreteSawtooth d (n + 1) = -centeredDiscreteSawtooth d n`. -/
theorem centeredDiscreteSawtooth_succ_eq_neg_of_dvd {d n : ℕ} (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d (n + 1) = -centeredDiscreteSawtooth d n := by
  rw [centeredDiscreteSawtooth_of_dvd hd hdvd, centeredDiscreteSawtooth_of_dvd_succ hd hdvd]

/-- **Pointwise Active-Divisor Midpoint Annihilation
(`centeredDiscreteSawtooth_add_succ_eq_zero_of_dvd`):**
For every `d > 0` and `n : ℕ` such that `d ∣ (n + 1)`:
`centeredDiscreteSawtooth d n + centeredDiscreteSawtooth d (n + 1) = 0`. -/
theorem centeredDiscreteSawtooth_add_succ_eq_zero_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d n + centeredDiscreteSawtooth d (n + 1) = 0 := by
  rw [centeredDiscreteSawtooth_succ_eq_neg_of_dvd hd hdvd, add_neg_cancel]

/-- **Pointwise Active-Divisor Square Invariance
(`centeredDiscreteSawtooth_succ_sq_eq_sq_of_dvd`):**
For every `d > 0` and `n : ℕ` such that `d ∣ (n + 1)`:
`centeredDiscreteSawtooth d (n + 1)² = centeredDiscreteSawtooth d n²`. -/
theorem centeredDiscreteSawtooth_succ_sq_eq_sq_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    centeredDiscreteSawtooth d (n + 1) ^ (2 : ℕ) =
      centeredDiscreteSawtooth d n ^ (2 : ℕ) := by
  rw [centeredDiscreteSawtooth_succ_eq_neg_of_dvd hd hdvd, neg_sq]

/-- **Pointwise Cancellation Between Squared Jump and Predictable Martingale Increment
(`centeredDiscreteSawtooth_addDiff_sq_add_two_mul_eq_zero_of_dvd`):**
For every `d > 0` and `n : ℕ` such that `d ∣ (n + 1)`, the squared forward jump
`addDiff (centeredDiscreteSawtooth d) n ^ 2` is cancelled **100% pointwise** by twice the
predictable martingale product `2 * addDiff (centeredDiscreteSawtooth d) n * centeredDiscreteSawtooth d n`. -/
theorem centeredDiscreteSawtooth_addDiff_sq_add_two_mul_eq_zero_of_dvd {d n : ℕ}
    (hd : 0 < d) (hdvd : d ∣ (n + 1)) :
    addDiff (centeredDiscreteSawtooth d) n ^ (2 : ℕ) +
      2 * addDiff (centeredDiscreteSawtooth d) n * centeredDiscreteSawtooth d n = 0 := by
  rw [← sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff,
    centeredDiscreteSawtooth_succ_sq_eq_sq_of_dvd hd hdvd, sub_self]

/-- **Simultaneous Active-Divisor Pair Product Invariance
(`centeredDiscreteSawtooth_mul_succ_eq_mul_of_dvd_both`):**
For every `d₁, d₂ > 0` and `n : ℕ` such that both `d₁ ∣ (n + 1)` and `d₂ ∣ (n + 1)`, their sawtooth
product is invariant across the jump `n ↦ n + 1`:
`centeredDiscreteSawtooth d₁ (n + 1) * centeredDiscreteSawtooth d₂ (n + 1) = centeredDiscreteSawtooth d₁ n * centeredDiscreteSawtooth d₂ n`. -/
theorem centeredDiscreteSawtooth_mul_succ_eq_mul_of_dvd_both {d₁ d₂ n : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hdvd₁ : d₁ ∣ (n + 1)) (hdvd₂ : d₂ ∣ (n + 1)) :
    centeredDiscreteSawtooth d₁ (n + 1) * centeredDiscreteSawtooth d₂ (n + 1) =
      centeredDiscreteSawtooth d₁ n * centeredDiscreteSawtooth d₂ n := by
  rw [centeredDiscreteSawtooth_succ_eq_neg_of_dvd hd₁ hdvd₁,
    centeredDiscreteSawtooth_succ_eq_neg_of_dvd hd₂ hdvd₂, neg_mul_neg]

/-! ## §2. Active/Inactive Divisor Split & Active-Square Cancellation in Pronic Abel Sums -/

/-- **Active Divisor Component of `weightedCenteredSawtoothSum` (`activeCenteredSawtoothSum`):**
The portion of `weightedCenteredSawtoothSum N c k` coming from moduli `d ∈ [1, N]` that divide `m`. -/
def activeCenteredSawtoothSum (N : ℕ) (c : ℕ → ℝ) (m k : ℕ) : ℝ :=
  -∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m), c d * centeredDiscreteSawtooth d k

/-- **Inactive Divisor Component of `weightedCenteredSawtoothSum` (`inactiveCenteredSawtoothSum`):**
The portion of `weightedCenteredSawtoothSum N c k` coming from moduli `d ∈ [1, N]` that do not
divide `m`. -/
def inactiveCenteredSawtoothSum (N : ℕ) (c : ℕ → ℝ) (m k : ℕ) : ℝ :=
  -∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ m)), c d * centeredDiscreteSawtooth d k

/-- **Exact Partition of `weightedCenteredSawtoothSum` into Active and Inactive Moduli
(`weightedCenteredSawtoothSum_eq_active_add_inactive`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `m, k : ℕ`:
`weightedCenteredSawtoothSum N c k = activeCenteredSawtoothSum N c m k + inactiveCenteredSawtoothSum N c m k`. -/
theorem weightedCenteredSawtoothSum_eq_active_add_inactive (N : ℕ) (c : ℕ → ℝ) (m k : ℕ) :
    weightedCenteredSawtoothSum N c k =
      activeCenteredSawtoothSum N c m k + inactiveCenteredSawtoothSum N c m k := by
  unfold weightedCenteredSawtoothSum activeCenteredSawtoothSum inactiveCenteredSawtoothSum
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun d => d ∣ m)
    (fun d => c d * centeredDiscreteSawtooth d k)).symm
  linarith

/-- **Active Component Sign Flip Across `n ↦ n + 1`
(`activeCenteredSawtoothSum_succ_eq_neg`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`activeCenteredSawtoothSum N c (n + 1) (n + 1) = -activeCenteredSawtoothSum N c (n + 1) n`. -/
theorem activeCenteredSawtoothSum_succ_eq_neg (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c (n + 1) (n + 1) =
      -activeCenteredSawtoothSum N c (n + 1) n := by
  unfold activeCenteredSawtoothSum
  rw [neg_neg, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd
  rw [centeredDiscreteSawtooth_succ_eq_neg_of_dvd hd.1.1 hd.2]
  ring

/-- **Active Component Midpoint Annihilation (`activeCenteredSawtoothSum_add_succ_eq_zero`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`activeCenteredSawtoothSum N c (n + 1) n + activeCenteredSawtoothSum N c (n + 1) (n + 1) = 0`. -/
theorem activeCenteredSawtoothSum_add_succ_eq_zero (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c (n + 1) n +
      activeCenteredSawtoothSum N c (n + 1) (n + 1) = 0 := by
  rw [activeCenteredSawtoothSum_succ_eq_neg, add_neg_cancel]

/-- **Active Component Square Invariance (`activeCenteredSawtoothSum_succ_sq_eq_sq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`activeCenteredSawtoothSum N c (n + 1) (n + 1)² = activeCenteredSawtoothSum N c (n + 1) n²`. -/
theorem activeCenteredSawtoothSum_succ_sq_eq_sq (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c (n + 1) (n + 1) ^ (2 : ℕ) =
      activeCenteredSawtoothSum N c (n + 1) n ^ (2 : ℕ) := by
  rw [activeCenteredSawtoothSum_succ_eq_neg, neg_sq]

/-- **Midpoint Annihilation of Active Divisors in `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_add_succ_eq_inactive_add_succ`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the midpoint sum
`weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1)` is completely
independent of all active divisors `d ∣ (n + 1)`:
`weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1) = inactiveCenteredSawtoothSum N c (n + 1) n + inactiveCenteredSawtoothSum N c (n + 1) (n + 1)`. -/
theorem weightedCenteredSawtoothSum_add_succ_eq_inactive_add_succ
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1) =
      inactiveCenteredSawtoothSum N c (n + 1) n +
        inactiveCenteredSawtoothSum N c (n + 1) (n + 1) := by
  have h1 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) n
  have h2 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) (n + 1)
  have hact := activeCenteredSawtoothSum_add_succ_eq_zero N c n
  linarith

/-- **Inactive-Midpoint Factorization of the Pronic Abel Square Increment
(`weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_inactive_midpoint`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the square increment
`weightedCenteredSawtoothSum N c (n + 1)² - weightedCenteredSawtoothSum N c n²` equals the product
of the BVI sieve jump `sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1` with the purely inactive
midpoint sum `inactiveCenteredSawtoothSum N c (n + 1) n + inactiveCenteredSawtoothSum N c (n + 1) (n + 1)`. -/
theorem weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_inactive_midpoint
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) =
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (inactiveCenteredSawtoothSum N c (n + 1) n +
          inactiveCenteredSawtoothSum N c (n + 1) (n + 1)) := by
  have hfac :
      weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
        weightedCenteredSawtoothSum N c n ^ (2 : ℕ) =
      (weightedCenteredSawtoothSum N c (n + 1) - weightedCenteredSawtoothSum N c n) *
        (weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1)) := by
    ring
  rw [hfac, weightedCenteredSawtoothSum_succ_sub_eq,
    weightedCenteredSawtoothSum_add_succ_eq_inactive_add_succ]

/-- **Exact Active-Square Cancellation in `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_succ_sq_sub_sq_active_sq_cancelled`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the quadratic self-energy
`activeCenteredSawtoothSum N c (n + 1) n²` of the jumping divisors `d ∣ (n + 1)` cancels **100%
identically** between `n` and `n + 1`, leaving only the smooth inactive square change plus the
active-inactive cross-product:
`W(n + 1)² - W(n)² = (I(n + 1)² - I(n)²) - 2 * A(n) * (I(n) + I(n + 1))`. -/
theorem weightedCenteredSawtoothSum_succ_sq_sub_sq_active_sq_cancelled
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) =
      (inactiveCenteredSawtoothSum N c (n + 1) (n + 1) ^ (2 : ℕ) -
        inactiveCenteredSawtoothSum N c (n + 1) n ^ (2 : ℕ)) -
        2 * activeCenteredSawtoothSum N c (n + 1) n *
          (inactiveCenteredSawtoothSum N c (n + 1) n +
            inactiveCenteredSawtoothSum N c (n + 1) (n + 1)) := by
  have h1 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) n
  have h2 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) (n + 1)
  have hact := activeCenteredSawtoothSum_succ_eq_neg N c n
  rw [h1, h2, hact]
  ring

/-! ## §3. Zero-Oscillation Affine Bridge Between Route PM and `weightedCenteredSawtoothSum` -/

/-- **Exact Cancellation of Divisor Impulses Between Route PM and `weightedCenteredSawtoothSum`
(`addDiff_pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum`):**
For every `ε : ℝ` and every sub-horizon step `k + 1 ≤ N`, the oscillatory divisor impulse
`pmPowerDampedDivisorCoeff ε (k + 1)` cancels **100% identically** between
`pmPowerDampedCenteredDivisorPrefix ε` and `weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε)`,
leaving a constant forward difference independent of `k`:
`addDiff (fun m => pmPowerDampedCenteredDivisorPrefix ε m - weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) m) k = selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 - (pmPowerDampedDivisorDensity ε).re`. -/
theorem addDiff_pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum
    (ε : ℝ) {N k : ℕ} (hkN : k + 1 ≤ N) :
    addDiff (fun m =>
      pmPowerDampedCenteredDivisorPrefix ε m -
        weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) m) k =
      selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 -
        (pmPowerDampedDivisorDensity ε).re := by
  have h1 := addDiff_pmPowerDampedCenteredDivisorPrefix ε k
  have h2 := weightedCenteredSawtoothSum_succ_sub_eq N (pmPowerDampedRealWeight ε) k
  have hsieve := sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
    (ε := ε) (by omega : 1 ≤ k + 1) hkN
  unfold addDiff pmPowerDampedCenteredDivisorCoeff at h1
  unfold addDiff
  dsimp only
  linarith

/-- **Exact Sub-Horizon Affine Linear Equivalence Between Route PM and `weightedCenteredSawtoothSum`
(`pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum_eq_affine`):**
For every `ε : ℝ` and every `n ≤ N`:
`pmPowerDampedCenteredDivisorPrefix ε n - weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) n = -weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) 0 + n * (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 - (pmPowerDampedDivisorDensity ε).re)`. -/
theorem pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum_eq_affine
    (ε : ℝ) {N n : ℕ} (hnN : n ≤ N) :
    pmPowerDampedCenteredDivisorPrefix ε n -
      weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) n =
      -weightedCenteredSawtoothSum N (pmPowerDampedRealWeight ε) 0 +
        (n : ℝ) * (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 -
          (pmPowerDampedDivisorDensity ε).re) := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have hkN : k ≤ N := by omega
    have hstep := addDiff_pmPowerDampedCenteredDivisorPrefix_sub_weightedCenteredSawtoothSum ε hnN
    unfold addDiff at hstep
    have hih := ih hkN
    push_cast
    linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
