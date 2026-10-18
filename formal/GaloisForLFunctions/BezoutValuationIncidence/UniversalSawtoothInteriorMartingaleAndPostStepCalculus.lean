import GaloisForLFunctions.BezoutValuationIncidence.ActivePairMartingaleDissipationAndShiftedTotientReduction

/-!
# Pillar XXXI: Universal Sawtooth Interior Martingale Identity, Two-Point Post-Step Smoothing & Boundary-Free Active-Pair Dissipation

In Pillars XXIV–XXVII (`BezoutPronicTotientInteriorMartingaleSynthesis`,
`PostStepInactivePrefixAndSixDivisibilityPronicDefect`,
`PostStepInactiveEnergyAndPronicGradientConservation`, and
`ActivePairMartingaleDissipationAndShiftedTotientReduction`), we proved the diagonal-free Bézout
interior martingale identity, two-step midpoint duality, post-step inactive two-point Bézout
smoothing, and active-pair martingale dissipation for the 1-parameter power-damped Route PM prefix
`pmPowerDampedCenteredDivisorPrefix ε`.

In this thirty-first pillar of **Bézout–Valuation Incidence Mechanics**, we elevate the entire
Bézout interior martingale and post-step smoothing calculus to **arbitrary sieve weights
`c : ℕ → ℝ` and arbitrary cutoffs `N : ℕ` across all steps `n : ℕ`** (with **no** sub-horizon
restriction `n ≤ N`), establishing three universal laws of the BVI sawtooth-sieve algebra:

1. **Universal Bézout Interior Square-Increment Martingale Identity & Two-Step Midpoint Duality
   (`active_deleted_add_predecessor_active_eq_successor_cov_add_shifted_addDiff`,
   `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior`,
   `sum_Icc_weightedCenteredSawtoothSum_sq_sub_eq_bezout_interior`,
   `sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior`,
   `bezoutInteriorSawtoothSum_add_half_shiftedAddDiff_eq_two_step_midpoint`)**:
   - For **every** cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ` (including `n = 0` and all
     `n > N`), absorbing both the pre-jump active sawtooth sum `activeCenteredSawtoothSum N c (n + 1) n`
     and the predecessor post-jump peak `activeCenteredSawtoothSum N c n n` into the square increment
     `W_{N,c}(n + 1)² - W_{N,c}(n)²` **eliminates the diagonal square `(s_{N,c}(n + 1) - Y(1))²`
     identically** and replaces it with the **Bézout successor covariance**
     `(s_{N,c}(n) - Y(1)) * (s_{N,c}(n + 1) - Y(1))` plus the **harmonic-divided forward difference**
     `(s_{N,c}(n + 1) - Y(1)) * addDiff (sieveSeq N (fun d => c d / d)) n`:
     $$W_{N,c}(n + 1)^2 - W_{N,c}(n)^2 =
       \bigl(s_{N,c}(n) - Y_{N,c}(1)\bigr)\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr) +
       \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,\operatorname{addDiff}\,(s_{N, c/d})\,n +
       2\bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\,\operatorname{bezoutInteriorSawtoothSum}\,N\,c\,n.$$
   - For every `N : ℕ`, `c : ℕ → ℝ`, and `n ≥ 1`, adding
     `(1 / 2) * addDiff (sieveSeq N (fun d => c d / d)) n` to `bezoutInteriorSawtoothSum N c n`
     recovers the exact two-step symmetric midpoint
     `(1 / 2) * (weightedCenteredSawtoothSum N c (n - 1) + weightedCenteredSawtoothSum N c (n + 1))`.

2. **Universal Post-Step Inactive Sawtooth Calculus & Two-Point Bézout Smoothing
   (`inactiveCenteredSawtoothSum_at_self_eq_sub_active`,
   `inactiveCenteredSawtoothSum_at_self_eq_bezoutInterior_add_succ_active`,
   `inactiveCenteredSawtoothSum_succ_sq_sub_sq`,
   `addDiff_inactiveCenteredSawtoothSum_at_self`)**:
   - Across `n ↦ n + 1`, the intra-step square change of the inactive sawtooth sum is driven
     purely by the harmonic-divided sieve impulse `sieveSeq N (fun d => c d / d) (n + 1) - Y(1)`:
     $$I_{N,c}(n + 1, n + 1)^2 - I_{N,c}(n + 1, n)^2 =
       \bigl(s_{N, c/d}(n + 1) - Y_{N,c}(1)\bigr)\bigl(W_{N,c}(n) + W_{N,c}(n + 1)\bigr).$$
   - The BVI forward difference of the post-step inactive sawtooth sum
     `n ↦ inactiveCenteredSawtoothSum N c n n` replaces the single sieve impulse at `n + 1` by the
     **two-point Bézout average** of `s_{N,c}(n) - Y(1)` and `s_{N,c}(n + 1) - Y(1)` plus half the
     harmonic-divided forward difference:
     $$\operatorname{addDiff}\,(\text{fun } k \Rightarrow I_{N,c}(k, k))\,n =
       \frac{1}{2}\Bigl(\bigl(s_{N,c}(n) - Y_{N,c}(1)\bigr) + \bigl(s_{N,c}(n + 1) - Y_{N,c}(1)\bigr)\Bigr) +
       \frac{1}{2}\,\operatorname{addDiff}\,(s_{N, c/d})\,n.$$

3. **Universal Boundary-Free Active-Pair Martingale Dissipation
   (`bezout_active_pair_eq_neg_addDiff_active_at_self`,
   `sieveSeq_sub_mul_bezout_active_pair_eq`,
   `sum_bezout_active_pair_martingale_compensated_eq`,
   `sum_bezout_active_pair_martingale_compensated_le`)**:
   - Because `activeCenteredSawtoothSum N c 1 1 = 0` holds identically for **every** cutoff `N : ℕ`
     and **every** weight `c : ℕ → ℝ` (since `1` is the sole divisor of `1` and `B̃₁(1, 1) = 0`),
     the self-interaction of the Bézout active pair in the compensated Pronic Abel sum has **zero
     boundary term at `n = 1`** and is **100% non-positively dissipative** for arbitrary weights `c`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Bézout Interior Square-Increment Martingale Identity & Two-Step Midpoint Duality -/

/-- **Universal Active-Deleted + Predecessor-Peak Reduction to Successor Covariance + Harmonic `addDiff`
(`active_deleted_add_predecessor_active_eq_successor_cov_add_shifted_addDiff`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ` (including `n = 0`), combining the
active-deleted diagonal product with twice the predecessor-peak active sawtooth product replaces the
diagonal factor at `n + 1` by the predecessor factor at `n` plus the harmonic-divided forward
difference `addDiff (sieveSeq N (fun d => c d / d)) n`. -/
theorem active_deleted_add_predecessor_active_eq_successor_cov_add_shifted_addDiff
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) +
      2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        activeCenteredSawtoothSum N c n n =
      (sieveSeq N c n - selbergMultiplesCoord N c 1) *
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) +
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n := by
  rw [activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub_general]
  unfold addDiff
  ring

/-- **Universal Bézout Interior Square-Increment Martingale Identity
(`weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ` (with no sub-horizon restriction),
the square increment `weightedCenteredSawtoothSum N c (n + 1)² - weightedCenteredSawtoothSum N c n²`
decomposes with **zero diagonal square** into:
1. The Bézout successor covariance `(sieveSeq N c n - Y(1)) * (sieveSeq N c (n + 1) - Y(1))`,
2. The harmonic-divided forward difference `(sieveSeq N c (n + 1) - Y(1)) * addDiff (sieveSeq N (c / d)) n`,
3. Twice the doubly-inactive Bézout interior martingale product
   `2 * (sieveSeq N c (n + 1) - Y(1)) * bezoutInteriorSawtoothSum N c n`. -/
theorem weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) =
      (sieveSeq N c n - selbergMultiplesCoord N c 1) *
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) +
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n +
      2 * (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        bezoutInteriorSawtoothSum N c n := by
  rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_shifted_diagonal_add_inactive_martingale,
    inactiveCenteredSawtoothSum_eq_predecessor_active_add_bezoutInterior,
    ← active_deleted_add_predecessor_active_eq_successor_cov_add_shifted_addDiff]
  ring

/-- **Universal Telescoping Bézout Interior Square Identity Over `Finset.Icc 1 (M - 1)`
(`sum_Icc_weightedCenteredSawtoothSum_sq_sub_eq_bezout_interior`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `M ≥ 1`:
`W_{N,c}(M)² - W_{N,c}(1)²` equals the sum over `1 ≤ n ≤ M - 1` of the Bézout successor covariance,
the harmonic-divided forward difference product, and twice the Bézout interior martingale product. -/
theorem sum_Icc_weightedCenteredSawtoothSum_sq_sub_eq_bezout_interior
    (N : ℕ) (c : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    weightedCenteredSawtoothSum N c M ^ (2 : ℕ) -
      weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ) =
      (∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c n - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1)) +
      (∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n) +
      2 * ∑ n ∈ Finset.Icc 1 (M - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          bezoutInteriorSawtoothSum N c n := by
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, M = K + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction K with
  | zero =>
    simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot, Finset.sum_insert hnot]
    have hstep := weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior N c (k + 1)
    have hih := ih (by omega)
    linarith

/-- **Universal Bézout Interior Pronic Abel Summation Identity
(`sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `T ≥ 1`, the Pronic energy of `weightedCenteredSawtoothSum N c`
decomposes with **zero diagonal square** into the harmonic sum of Bézout successor covariances, the
harmonic sum of shifted-weight forward differences, and twice the harmonic sum of doubly-inactive
Bézout interior martingale products. -/
theorem sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior
    (N : ℕ) (c : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T,
      weightedCenteredSawtoothSum N c n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      weightedCenteredSawtoothSum N c T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ) +
      (∑ n ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c n - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1)) / ((n : ℝ) + 1)) +
      (∑ n ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n) / ((n : ℝ) + 1)) +
      2 * ∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          bezoutInteriorSawtoothSum N c n / ((n : ℝ) + 1) := by
  rw [sum_sq_div_pronicSeq_add_terminal_eq_abel (weightedCenteredSawtoothSum N c) hT]
  have hrew :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
          weightedCenteredSawtoothSum N c n ^ (2 : ℕ)) / ((n : ℝ) + 1)) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c n - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1)) / ((n : ℝ) + 1)) +
      (∑ n ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n) / ((n : ℝ) + 1)) +
      2 * ∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          bezoutInteriorSawtoothSum N c n / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior]
    ring
  linarith

/-- **Universal Two-Step Symmetric Midpoint Duality for `bezoutInteriorSawtoothSum`
(`bezoutInteriorSawtoothSum_add_half_shiftedAddDiff_eq_two_step_midpoint`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n ≥ 1`, adding `(1 / 2) * addDiff (sieveSeq N (c / d)) n` to
the doubly-inactive Bézout interior sawtooth sum `bezoutInteriorSawtoothSum N c n` yields the exact
two-step symmetric midpoint `(1 / 2) * (weightedCenteredSawtoothSum N c (n - 1) + weightedCenteredSawtoothSum N c (n + 1))`. -/
theorem bezoutInteriorSawtoothSum_add_half_shiftedAddDiff_eq_two_step_midpoint
    (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    bezoutInteriorSawtoothSum N c n +
      (1 / 2 : ℝ) * addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n =
      (1 / 2 : ℝ) *
        (weightedCenteredSawtoothSum N c (n - 1) +
          weightedCenteredSawtoothSum N c (n + 1)) := by
  have hpred :
      weightedCenteredSawtoothSum N c n - weightedCenteredSawtoothSum N c (n - 1) =
        sieveSeq N c n - selbergMultiplesCoord N c 1 := by
    have h := weightedCenteredSawtoothSum_succ_sub_eq N c (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have hsucc := weightedCenteredSawtoothSum_succ_sub_eq N c n
  have hpart := weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior N c n
  have hpair := bezout_active_pair_eq_neg_half_addDiff N c n
  unfold addDiff at hpair ⊢
  linarith

/-! ## §2. Universal Post-Step Inactive Sawtooth Calculus & Two-Point Bézout Smoothing -/

/-- For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the post-step inactive sawtooth sum
`inactiveCenteredSawtoothSum N c n n` equals `weightedCenteredSawtoothSum N c n` minus the post-jump
active peak `activeCenteredSawtoothSum N c n n`. -/
theorem inactiveCenteredSawtoothSum_at_self_eq_sub_active
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    inactiveCenteredSawtoothSum N c n n =
      weightedCenteredSawtoothSum N c n - activeCenteredSawtoothSum N c n n := by
  have h := weightedCenteredSawtoothSum_eq_active_add_inactive N c n n
  linarith

/-- For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the post-step inactive sawtooth sum
`inactiveCenteredSawtoothSum N c n n` decomposes into `bezoutInteriorSawtoothSum N c n` plus the
next step's pre-jump trough `activeCenteredSawtoothSum N c (n + 1) n`. -/
theorem inactiveCenteredSawtoothSum_at_self_eq_bezoutInterior_add_succ_active
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    inactiveCenteredSawtoothSum N c n n =
      bezoutInteriorSawtoothSum N c n + activeCenteredSawtoothSum N c (n + 1) n := by
  have h1 := inactiveCenteredSawtoothSum_at_self_eq_sub_active N c n
  have h2 := weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior N c n
  linarith

/-- **Universal Intra-Step Square Change of `inactiveCenteredSawtoothSum` Across `n ↦ n + 1`
(`inactiveCenteredSawtoothSum_succ_sq_sub_sq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the intra-step square change of the inactive sawtooth
sum for `n + 1` across `n ↦ n + 1` equals the harmonic-divided sieve impulse
`sieveSeq N (fun d => c d / d) (n + 1) - selbergMultiplesCoord N c 1` times the full sawtooth
midpoint sum `weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1)`. -/
theorem inactiveCenteredSawtoothSum_succ_sq_sub_sq
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    inactiveCenteredSawtoothSum N c (n + 1) (n + 1) ^ (2 : ℕ) -
      inactiveCenteredSawtoothSum N c (n + 1) n ^ (2 : ℕ) =
      (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) *
        (weightedCenteredSawtoothSum N c n + weightedCenteredSawtoothSum N c (n + 1)) := by
  have hfac :
      inactiveCenteredSawtoothSum N c (n + 1) (n + 1) ^ (2 : ℕ) -
        inactiveCenteredSawtoothSum N c (n + 1) n ^ (2 : ℕ) =
      (inactiveCenteredSawtoothSum N c (n + 1) (n + 1) -
        inactiveCenteredSawtoothSum N c (n + 1) n) *
        (inactiveCenteredSawtoothSum N c (n + 1) n +
          inactiveCenteredSawtoothSum N c (n + 1) (n + 1)) := by
    ring
  rw [hfac, inactiveCenteredSawtoothSum_succ_sub_eq,
    ← weightedCenteredSawtoothSum_add_succ_eq_inactive_add_succ]

/-- **Universal Two-Point Bézout Smoothing Law for `inactiveCenteredSawtoothSum N c n n`
(`addDiff_inactiveCenteredSawtoothSum_at_self`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the BVI forward difference of the post-step inactive
sawtooth sequence `k ↦ inactiveCenteredSawtoothSum N c k k` replaces the single sieve impulse at
`n + 1` by the two-point Bézout average of the centered sieve impulses at `n` and `n + 1` plus half
the harmonic-divided forward difference:
`addDiff (fun k => inactiveCenteredSawtoothSum N c k k) n = (1 / 2) * ((sieveSeq N c n - Y(1)) + (sieveSeq N c (n + 1) - Y(1))) + (1 / 2) * addDiff (sieveSeq N (fun d => c d / d)) n`. -/
theorem addDiff_inactiveCenteredSawtoothSum_at_self
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    addDiff (fun k => inactiveCenteredSawtoothSum N c k k) n =
      (1 / 2 : ℝ) *
        ((sieveSeq N c n - selbergMultiplesCoord N c 1) +
          (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1)) +
      (1 / 2 : ℝ) * addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n := by
  unfold addDiff
  dsimp only
  rw [inactiveCenteredSawtoothSum_at_self_eq_sub_active N c (n + 1),
    inactiveCenteredSawtoothSum_at_self_eq_sub_active N c n,
    activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub_general N c (n + 1),
    activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub_general N c n]
  have hw := weightedCenteredSawtoothSum_succ_sub_eq N c n
  linarith

/-! ## §3. Universal Boundary-Free Active-Pair Martingale Dissipation -/

/-- **Bézout Active Pair as Minus the Forward Difference of `activeCenteredSawtoothSum N c k k`
(`bezout_active_pair_eq_neg_addDiff_active_at_self`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, because `activeCenteredSawtoothSum N c (n + 1) n = -activeCenteredSawtoothSum N c (n + 1) (n + 1)`,
the Bézout active pair `activeCenteredSawtoothSum N c n n + activeCenteredSawtoothSum N c (n + 1) n`
equals `-addDiff (fun k => activeCenteredSawtoothSum N c k k) n`. -/
theorem bezout_active_pair_eq_neg_addDiff_active_at_self
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c n n +
      activeCenteredSawtoothSum N c (n + 1) n =
      -addDiff (fun k => activeCenteredSawtoothSum N c k k) n := by
  have hflip := activeCenteredSawtoothSum_succ_eq_neg N c n
  unfold addDiff
  linarith

/-- **Pointwise Sawtooth Self-Dissipation + Harmonic-Divided Decomposition of the Active-Pair Product
(`sieveSeq_sub_mul_bezout_active_pair_eq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, writing
`sieveSeq N c (n + 1) - Y(1) = 2 * activeCenteredSawtoothSum N c (n + 1) (n + 1) + (sieveSeq N (c / d) (n + 1) - Y(1))`
decomposes the Bézout active-pair martingale product into twice the backward-weighted self-interaction
`-activeCenteredSawtoothSum N c (n + 1) (n + 1) * addDiff (fun k => activeCenteredSawtoothSum N c k k) n`
minus the harmonic-divided cross-term. -/
theorem sieveSeq_sub_mul_bezout_active_pair_eq
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
      (activeCenteredSawtoothSum N c n n +
        activeCenteredSawtoothSum N c (n + 1) n) =
      2 * (-activeCenteredSawtoothSum N c (n + 1) (n + 1) *
        addDiff (fun k => activeCenteredSawtoothSum N c k k) n) -
      (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) *
        addDiff (fun k => activeCenteredSawtoothSum N c k k) n := by
  rw [bezout_active_pair_eq_neg_addDiff_active_at_self]
  have ha := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c n
  have hsplit :
      sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1 =
        2 * activeCenteredSawtoothSum N c (n + 1) (n + 1) +
          (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) := by
    linarith
  rw [hsplit]
  ring

/-- **Universal Boundary-Free Compensated Abel Dissipation of the Bézout Active-Pair Martingale
(`sum_bezout_active_pair_martingale_compensated_eq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `T ≥ 1`, because `activeCenteredSawtoothSum N c 1 1 = 0` holds
identically for **every** weight `c`, the boundary term at `n = 1` vanishes identically (`0`), so
the compensated Bézout active-pair martingale sum decomposes into two purely negative quadratic
dissipation sums minus the harmonic-divided cross-sum. -/
theorem sum_bezout_active_pair_martingale_compensated_eq
    (N : ℕ) (c : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (activeCenteredSawtoothSum N c n n +
          activeCenteredSawtoothSum N c (n + 1) n) *
        (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      -(∑ n ∈ Finset.Icc 1 T,
        activeCenteredSawtoothSum N c n n ^ (2 : ℕ) / (pronicSeq n : ℝ)) -
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (fun k => activeCenteredSawtoothSum N c k k) n ^ (2 : ℕ) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
      ∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (fun k => activeCenteredSawtoothSum N c k k) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have hpoint :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
          (activeCenteredSawtoothSum N c n n +
            activeCenteredSawtoothSum N c (n + 1) n) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      2 * (∑ n ∈ Finset.Icc 1 (T - 1),
        (-activeCenteredSawtoothSum N c (n + 1) (n + 1) *
          addDiff (fun k => activeCenteredSawtoothSum N c k k) n) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
      ∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (fun k => activeCenteredSawtoothSum N c k k) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sieveSeq_sub_mul_bezout_active_pair_eq]
    ring
  have hdiss := sum_neg_succ_mul_addDiff_compensated_eq
    (fun k => activeCenteredSawtoothSum N c k k) hT
  simp only [activeCenteredSawtoothSum_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_mul, zero_sub] at hdiss
  linarith

/-- **Universal Upper Bound on the Compensated Bézout Active-Pair Martingale Sum
(`sum_bezout_active_pair_martingale_compensated_le`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `T ≥ 1`, because both active sawtooth quadratic dissipation sums
are non-negative, the compensated Bézout active-pair martingale sum is bounded above by the negative
harmonic-divided cross-sum alone. -/
theorem sum_bezout_active_pair_martingale_compensated_le
    (N : ℕ) (c : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        (activeCenteredSawtoothSum N c n n +
          activeCenteredSawtoothSum N c (n + 1) n) *
        (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) ≤
      -∑ n ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) - selbergMultiplesCoord N c 1) *
          addDiff (fun k => activeCenteredSawtoothSum N c k k) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  rw [sum_bezout_active_pair_martingale_compensated_eq N c hT]
  have hpr :
      0 ≤ ∑ n ∈ Finset.Icc 1 T,
        activeCenteredSawtoothSum N c n n ^ (2 : ℕ) / (pronicSeq n : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hgr :
      0 ≤ ∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (fun k => activeCenteredSawtoothSum N c k k) n ^ (2 : ℕ) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
    have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
    have hkern : 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)
    exact mul_nonneg (sq_nonneg _) hkern
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
