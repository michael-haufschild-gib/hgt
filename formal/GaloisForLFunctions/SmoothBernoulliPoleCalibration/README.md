# Smooth-Tapered Higher-Order Bernoulli Elimination and Even-Pole Calibration (`GaloisForLFunctions.SmoothBernoulliPoleCalibration`)

This directory formalizes **Mechanism 2: Smooth-Tapered Higher-Order Bernoulli Elimination +
Even-Pole Calibration in the Balanced Regime ($Q \asymp P$)** from
[`docs/reports/review-2110/argon.md`](../../../../docs/reports/review-2110/argon.md) (§1.3).

## Architecture and Module Ledger

1. **[`HigherOrderKernelStatisticAndDualNorm.lean`](./HigherOrderKernelStatisticAndDualNorm.lean)**
   - Defines `higherOrderKernelStatistic N L c' d := ∑ n ∈ Icc 1 N, c' n * potentialTerms d n L`,
     generalizing the order-`2` `kernelStatistic` of `DualNormOfTheCrossScaleFunctional` to
     arbitrary order `L : ℕ`, with base `higherOrderKernelStatistic_zero` and step recursion
     `higherOrderKernelStatistic_succ`.
   - Proves the order-`L` cross-scale dual-norm approximation
     `abs_rowBilinear_sub_higherOrderKernelStatistic_le`, adversarial sign attainment
     `exists_rowBilinear_ge_higherOrderDualNorm`, and upper bound
     `abs_rowBilinear_le_higherOrderDualNorm`, pushing the cross-scale remainder from fourth
     order (`O(d^3 / n^4)`) to arbitrary order `L + 2`
     (`2^L (L+1)! (∑ d, |c d| d^{L+1}) (∑ n, |c' n| / n^{L+2})`).
   - Couples the order-`L` dual norm with `SmoothLargeScaleRowsOfEveryOrder` to prove the
     pointwise prime bound `abs_higherOrderKernelStatistic_le_smoothnessNorm` and the all-order
     smooth dual-norm bound `sum_abs_higherOrderKernelStatistic_le_smoothnessNorm`.

2. **[`SmoothTaperedCrossScaleDispersion.lean`](./SmoothTaperedCrossScaleDispersion.lean)**
   - Defines `crossScaleFunctional N c c' := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' + rowBeta N c * finiteHarmonicSum N c'`
     and proves its exact linearity in `c'` (`crossScaleFunctional_add_right`) via the exact
     residue tail identity `rowBilinear_add_mean_add_beta_eq_tail`.
   - Defines `IsSmoothTaperedAtScale N L Q C₀ c'` (`smoothnessNorm N L c' ≤ C₀ M₂(c') / Q^L`)
     and proves `sum_abs_higherOrderKernelStatistic_le_of_isSmoothTaperedAtScale` and
     `abs_crossScaleFunctional_le_of_isSmoothTaperedAtScale`, showing that smooth tapering
     compresses the polynomial Bernoulli growth `p^{L+1}` across `p ≤ 2P` to `p * (2P / Q)^L`
     and eliminates the sharp-cutoff `θ = 4/3` barrier (`SharpCutoffTypeIStopsAtFourThirds`)
     in every sub-balanced regime `P ≪_L Q`.
   - Proves the **Smooth-Plus-Oscillatory Row Decomposition Bridge**
     `abs_crossScaleFunctional_add_le_of_isSmoothTaperedAtScale` and couples it with
     `CentredPrimeRowPassesTheCoherentBlockObstruction` in
     `exists_abs_crossScaleFunctional_smooth_add_centredPrimeRow_le`.

3. **[`EvenPoleCalibrationAndLogMomentPinning.lean`](./EvenPoleCalibrationAndLogMomentPinning.lean)**
   - Proves the exact odd–even pole decomposition `poleValue_eq_oddPartKernel_add_evenPartWeight`:
     `poleValue k J ε = poleValue (oddPartKernel k) J ε + 2^{ε - 1} * poleValue (evenPartWeight k) J ε`.
   - Proves `both_evenFlip_pair_receiverBounded_iff` and the **Simultaneous Odd–Even Pole
     Calibration Law** `both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole`: for
     `0 < ε ≤ 1/2` and a kernel `k` on `[1, J]` vanishing on multiples of `4`, both
     `c = k ⋆ o` and its even flip `c^♭ = k^♭ ⋆ o` are `ReceiverBounded` if and only if both
     `poleValue (oddPartKernel k) J ε = 0` and `poleValue (evenPartWeight k) J ε = 0`.
   - Couples `TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel` with
     `LogarithmicMomentsAreACompleteReceiverInvariant` to prove
     `exists_logMoment_ne_of_fermi_evenFlip` (on the generalized Fermi horizon where
     `poleValue k J ε = 0` and `poleValue (evenPartWeight k) J ε ≠ 0`, `c` and `c^♭` have
     identical Ramanujan amplitudes at every modulus `e` yet are separated by some logarithmic
     pronic moment `M(· log^m)`) and `evenFlip_eq_of_logMoments_eq` (equality of all logarithmic
     moments pins `c d = c^♭ d` for all `d ≥ 2`).

4. **[`MasterSmoothBernoulliPoleCalibrationTheorem.lean`](./MasterSmoothBernoulliPoleCalibrationTheorem.lean)**
   - Proves `subbalanced_vs_balanced_bernoulli_scaling`, contrasting the sub-balanced damping
     regime `((L + 1).factorial : ℝ) * (P / Q)^L ≤ ε` against the balanced threshold `Q ≤ P`
     where `(P / Q)^L ≥ 1` ceases to damp `(L + 1)!`.
   - Packages the four-part unconditional **`smooth_bernoulli_pole_calibration_master_theorem`**.
