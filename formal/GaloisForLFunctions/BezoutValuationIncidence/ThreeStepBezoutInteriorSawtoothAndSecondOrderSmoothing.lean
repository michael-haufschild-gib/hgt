import GaloisForLFunctions.BezoutValuationIncidence.UniversalSawtoothInteriorMartingaleAndPostStepCalculus
import GaloisForLFunctions.BezoutValuationIncidence.ThreeStepPrimorialBezoutAndEvenCubicCeiling

/-!
# Three-Step Bézout Interior Sawtooth Calculus and Second-Order Difference Smoothing

In `UniversalSawtoothInteriorMartingaleAndPostStepCalculus`, the square increment
`weightedCenteredSawtoothSum N c (n + 1) ^ 2 - weightedCenteredSawtoothSum N c n ^ 2` was reduced
with zero diagonal square to the Bézout successor covariance, the harmonic-divided first difference,
and the doubly-inactive Bézout interior martingale product
`2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) * bezoutInteriorSawtoothSum N c n`.

This module develops the intrinsic difference calculus and three-step primorial partition of
`bezoutInteriorSawtoothSum N c n` and its horizon-free counterpart `pmBezoutInteriorPrefix ε n`:

1. **Exact Second-Order Difference Smoothing Law (`addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg`):**
   Across step `n ↦ n + 1`, the forward difference `addDiff (bezoutInteriorSawtoothSum N c) n`
   cancels the middle sieve impulse `sieveSeq N c (n + 1)` identically, replacing it by the
   **outer-pair two-step Bézout average** of `sieveSeq N c n - Y(1)` and `sieveSeq N c (n + 2) - Y(1)`
   minus half the second-order forward difference of the harmonic-divided sieve response:
   $$\operatorname{addDiff}\,(\operatorname{bezoutInteriorSawtoothSum}\,N\,c)\,n =
     \frac{1}{2}\Bigl(\bigl(s_{N,c}(n) - Y_{N,c}(1)\bigr) + \bigl(s_{N,c}(n + 2) - Y_{N,c}(1)\bigr)\Bigr)
     - \frac{1}{2}\,\operatorname{addDiff}\,\bigl(\operatorname{addDiff}\,(s_{N, c/d})\bigr)\,n.$$

2. **Reduction of Middle-Impulse Products to Pure Lag-1 Pronic Covariances
   (`sieveSeq_sub_mul_addDiff_bezoutInteriorSawtoothSum_eq_pronic_avg`,
   `mul_addDiff_pmBezoutInteriorPrefix_eq_pronic_avg`):**
   Multiplying `addDiff (bezoutInteriorSawtoothSum N c) n` (or `addDiff (pmBezoutInteriorPrefix ε) n`)
   by the middle impulse at `n + 1` pairs `n + 1` with the outer endpoints `n` and `n + 2` of the
   three-step triple `(n, n + 1, n + 2)`. Because both `|(n + 1) - n| = 1` and `|(n + 2) - (n + 1)| = 1`
   are unit steps, the product decomposes into the symmetric average of two consecutive **lag-1
   coprime pronic covariances** with **zero diagonal square and zero lag-2 cross-term**.

3. **Three-Step Primorial Bézout Interior Sawtooth Partition
   (`threeStepBezoutInteriorSawtoothSum`, `dvd_two_of_dvd_and_dvd_add_two`,
   `bezoutInteriorSawtoothSum_eq_threeStep_add_two_step_prejump`):**
   Extracting the moduli `d ∣ (n + 2)` from `bezoutInteriorSawtoothSum N c n` defines the triply-inactive
   sawtooth sum `threeStepBezoutInteriorSawtoothSum N c n` over moduli dividing none of
   `n, n + 1, n + 2`, while every modulus dividing both `n` and `n + 2` is forced by
   `gcd(n, n + 2) = gcd(n, 2)` to divide `2`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Outer-Pair Two-Step Smoothing Law for `bezoutInteriorSawtoothSum` -/

/-- **Exact Bridge Between `bezoutInteriorSawtoothSum` and `weightedCenteredSawtoothSum`
(`bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ`, the doubly-inactive Bézout interior
sawtooth sum equals `weightedCenteredSawtoothSum N c n` plus half the forward difference of
`k ↦ sieveSeq N c k - sieveSeq N (fun d => c d / d) k`. -/
theorem bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    bezoutInteriorSawtoothSum N c n =
      weightedCenteredSawtoothSum N c n +
        (1 / 2 : ℝ) *
          addDiff (fun k => sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k) n := by
  have hpart := weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior N c n
  have hpair := bezout_active_pair_eq_neg_half_addDiff N c n
  linarith

/-- **Exact Outer-Pair Two-Step Bézout Smoothing Law for `bezoutInteriorSawtoothSum`
(`addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ`, the forward difference
`addDiff (bezoutInteriorSawtoothSum N c) n` cancels the middle sieve impulse `sieveSeq N c (n + 1)`
identically, yielding the average of the outer-pair impulses at `n` and `n + 2` minus half the
second-order forward difference of the harmonic-divided sieve response `sieveSeq N (fun d => c d / d)`. -/
theorem addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    addDiff (bezoutInteriorSawtoothSum N c) n =
      (1 / 2 : ℝ) *
        ((sieveSeq N c n - selbergMultiplesCoord N c 1) +
          (sieveSeq N c (n + 2) - selbergMultiplesCoord N c 1)) -
      (1 / 2 : ℝ) *
        addDiff (addDiff (sieveSeq N (fun d => c d / (d : ℝ)))) n := by
  have h0 := bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff N c n
  have h1 := bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff N c (n + 1)
  have hw := weightedCenteredSawtoothSum_succ_sub_eq N c n
  unfold addDiff at h0 h1 ⊢
  dsimp only at h0 h1 ⊢
  linarith

/-- **Middle-Impulse Product Reduction to Consecutive Lag-1 Pronic Covariances
(`sieveSeq_sub_mul_addDiff_bezoutInteriorSawtoothSum_eq_pronic_avg`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, multiplying `addDiff (bezoutInteriorSawtoothSum N c) n`
by the middle centered impulse `sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1` produces the
symmetric average of the two consecutive lag-1 Bézout successor covariances at `(n, n + 1)` and
`(n + 1, n + 2)` minus half the second-order harmonic-divided cross-product, with zero diagonal
square and zero lag-2 cross-term. -/
theorem sieveSeq_sub_mul_addDiff_bezoutInteriorSawtoothSum_eq_pronic_avg
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
      addDiff (bezoutInteriorSawtoothSum N c) n =
      (1 / 2 : ℝ) *
        ((sieveSeq N c n - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) +
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (n + 2) - selbergMultiplesCoord N c 1)) -
      (1 / 2 : ℝ) *
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (addDiff (sieveSeq N (fun d => c d / (d : ℝ)))) n := by
  rw [addDiff_bezoutInteriorSawtoothSum_eq_outer_pair_avg]
  ring

/-- **Pointwise Quadratic-Gradient Identity for the Bézout Interior Martingale Product
(`two_mul_sieveSeq_sub_mul_bezoutInterior_eq_addDiff_sq_sub`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, eliminating `sieveSeq N c (n + 1) - Y(1)` via
`bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff` expresses the Bézout interior martingale
product `2 * (sieveSeq N c (n + 1) - Y(1)) * bezoutInteriorSawtoothSum N c n` as the forward
difference of `(bezoutInteriorSawtoothSum N c)²` minus the squared forward difference
`(addDiff (bezoutInteriorSawtoothSum N c) n)²` minus the second-order difference cross-term. -/
theorem two_mul_sieveSeq_sub_mul_bezoutInterior_eq_addDiff_sq_sub
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
      bezoutInteriorSawtoothSum N c n =
      addDiff (fun k => bezoutInteriorSawtoothSum N c k ^ (2 : ℕ)) n -
        addDiff (bezoutInteriorSawtoothSum N c) n ^ (2 : ℕ) -
        bezoutInteriorSawtoothSum N c n *
          addDiff (addDiff (fun k =>
            sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k)) n := by
  have h0 := bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff N c n
  have h1 := bezoutInteriorSawtoothSum_eq_weighted_add_half_addDiff N c (n + 1)
  have hw := weightedCenteredSawtoothSum_succ_sub_eq N c n
  have hstep :
      sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1 =
        addDiff (bezoutInteriorSawtoothSum N c) n -
          (1 / 2 : ℝ) *
            addDiff (addDiff (fun k =>
              sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k)) n := by
    unfold addDiff at h0 h1 ⊢
    dsimp only at h0 h1 ⊢
    linarith
  rw [hstep]
  unfold addDiff
  ring

/-! ## §2. Horizon-Free Outer-Pair Two-Step Smoothing for Route PM (`pmBezoutInteriorPrefix`) -/

/-- **Exact Outer-Pair Two-Step Smoothing Law for `pmBezoutInteriorPrefix`
(`addDiff_pmBezoutInteriorPrefix_eq_outer_pair_avg`):**
For every `ε : ℝ` and `n : ℕ`, the forward difference `addDiff (pmBezoutInteriorPrefix ε) n` equals
the outer-pair average `(1 / 2) * (widetilde_τ_ε(n) + widetilde_τ_ε(n + 2))` minus half the
second-order forward difference of `pmPowerDampedDivisorCoeff (1 + ε)`. -/
theorem addDiff_pmBezoutInteriorPrefix_eq_outer_pair_avg (ε : ℝ) (n : ℕ) :
    addDiff (pmBezoutInteriorPrefix ε) n =
      (1 / 2 : ℝ) *
        (pmPowerDampedCenteredDivisorCoeff ε n +
          pmPowerDampedCenteredDivisorCoeff ε (n + 2)) -
      (1 / 2 : ℝ) *
        addDiff (addDiff (pmPowerDampedDivisorCoeff (1 + ε))) n := by
  have h0 := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  have h1 := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε (n + 1)
  have hp0 := pmPowerDampedCenteredDivisorPrefix_succ ε n
  have hp1 := pmPowerDampedCenteredDivisorPrefix_succ ε (n + 1)
  unfold addDiff at h0 h1 ⊢
  unfold pmActiveSawtoothComponent at h0 h1
  unfold pmPowerDampedCenteredDivisorCoeff at hp0 hp1 ⊢
  linarith

/-- **Middle-Impulse Product Reduction for `pmBezoutInteriorPrefix`
(`mul_addDiff_pmBezoutInteriorPrefix_eq_pronic_avg`):**
For every `ε : ℝ` and `n : ℕ`, multiplying `addDiff (pmBezoutInteriorPrefix ε) n` by the middle
impulse `pmPowerDampedCenteredDivisorCoeff ε (n + 1)` yields the symmetric average of the two
consecutive lag-1 pronic covariances at `n` and `n + 1` minus half the second-order shifted-totient
cross-product. -/
theorem mul_addDiff_pmBezoutInteriorPrefix_eq_pronic_avg (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      addDiff (pmBezoutInteriorPrefix ε) n =
      (1 / 2 : ℝ) *
        (pmPowerDampedCenteredDivisorCoeff ε n *
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) +
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          pmPowerDampedCenteredDivisorCoeff ε (n + 2)) -
      (1 / 2 : ℝ) *
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (addDiff (pmPowerDampedDivisorCoeff (1 + ε))) n := by
  rw [addDiff_pmBezoutInteriorPrefix_eq_outer_pair_avg]
  ring

/-! ## §3. Three-Step Primorial Bézout Interior Sawtooth Partition -/

/-- **Three-Step Bézout Interior Sawtooth Sum (`threeStepBezoutInteriorSawtoothSum`):**
The weighted centered sawtooth sum at step `n` over all moduli `1 ≤ d ≤ N` that divide **none** of
the three consecutive integers `n, n + 1, n + 2`. -/
def threeStepBezoutInteriorSawtoothSum (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  -∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2))),
    c d * centeredDiscreteSawtooth d n

/-- By `gcd(n, n + 2) = gcd(n, 2)`, any modulus `d` dividing both `n` and `n + 2` divides `2`. -/
theorem dvd_two_of_dvd_and_dvd_add_two {d n : ℕ} (hdn : d ∣ n) (hdn2 : d ∣ (n + 2)) :
    d ∣ 2 := by
  have hd_gcd : d ∣ Nat.gcd n (n + 2) := Nat.dvd_gcd hdn hdn2
  rw [gcd_self_add_two_eq_gcd_two] at hd_gcd
  exact hd_gcd.trans (Nat.gcd_dvd_right n 2)

/-- If `d ∣ (n + 2)` and `¬ (d ∣ n)`, then `¬ (d ∣ (n + 1))` holds automatically because
`gcd(n + 1, n + 2) = 1` and `d ≠ 1`. -/
theorem not_dvd_succ_of_not_dvd_of_dvd_add_two {d n : ℕ}
    (hdn : ¬ (d ∣ n)) (hdn2 : d ∣ (n + 2)) :
    ¬ (d ∣ (n + 1)) := by
  intro hdn1
  have hd1 : d = 1 := eq_one_of_dvd_and_dvd_succ hdn1 hdn2
  subst hd1
  exact hdn (one_dvd n)

/-- **Exact Decomposition of `bezoutInteriorSawtoothSum` into Three-Step Interior + `n + 2` Pre-Jump Moduli
(`bezoutInteriorSawtoothSum_eq_threeStep_add_two_step_prejump`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, `bezoutInteriorSawtoothSum N c n` splits into the
triply-inactive `threeStepBezoutInteriorSawtoothSum N c n` plus the contribution of the moduli
`d ∈ [1, N]` dividing `n + 2` but not `n`. -/
theorem bezoutInteriorSawtoothSum_eq_threeStep_add_two_step_prejump
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    bezoutInteriorSawtoothSum N c n =
      threeStepBezoutInteriorSawtoothSum N c n -
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ d ∣ (n + 2)),
          c d * centeredDiscreteSawtooth d n := by
  unfold bezoutInteriorSawtoothSum threeStepBezoutInteriorSawtoothSum
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1))))
    (fun d => d ∣ (n + 2))
    (fun d => c d * centeredDiscreteSawtooth d n)).symm
  have hset1 :
      ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)))).filter
        (fun d => d ∣ (n + 2)) =
      (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ d ∣ (n + 2)) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hdI, hdn, _⟩, hdn2⟩
      exact ⟨hdI, hdn, hdn2⟩
    · rintro ⟨hdI, hdn, hdn2⟩
      exact ⟨⟨hdI, hdn, not_dvd_succ_of_not_dvd_of_dvd_add_two hdn hdn2⟩, hdn2⟩
  have hset2 :
      ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)))).filter
        (fun d => ¬ (d ∣ (n + 2))) =
      (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2))) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  rw [hset1, hset2] at hsplit
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
