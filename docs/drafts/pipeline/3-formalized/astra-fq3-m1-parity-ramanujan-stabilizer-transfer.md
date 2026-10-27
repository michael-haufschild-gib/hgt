# Parity-Sensitive Multi-Modulus Ramanujan Stabilizer Transfer on Even Shifts

- **ID:** astra-fq3-m1-2026-10-27
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2710/astra.md · Focus Question 3, Milestone 1
- **Statement:** On the odd-prime even-shift coalescent sum `oddEvenShiftPrimeCoalSum` (`θ₀ < 1/3`), `c_2(2r) = +1` merges with `q = 1` into the doubled Poisson-parity baseline `2`, while for every odd `q`, `c_q(2r) = c_{2q}(2r) = c_q(r)` and `4 ∣ n ⟹ sqfreeTotientInv n = 0`; splitting modulo `4` yields the exact parity-halving Ward–Mertens top-octave law and transfers the full even-shift singular-series model `1 ≤ n ≤ N` unconditionally to `-cosTransform Ω 0 * (2 ∑_{3≤q≤N/2, q odd} sqfreeTotientInv q + ∑_{N/2<q≤N, q odd} sqfreeTotientInv q)` with explicit height remainder, while on actual coalescent prime pairs (`θ₀ < 1/3`) the `q = 2` Ramanujan projection equals `primeCoalSum` identically and every doubled odd modulus `2q` matches `q` identically, decomposing `oddEvenShiftPrimeCoalSum` into `stabilizerModelOddCoalSum Q + stabilizerDiscrepancyOddCoalSum Q`.

## Goal
Resolve the modulo-`2` parity doubling on the **singular-series stabilizer model** and on the **Ramanujan projections of `primeCoalSum`** (`θ₀ < 1/3`) without adding conditional premises, isolating the exact centered prime-pair discrepancy `stabilizerDiscrepancyOddCoalSum Q` whose bound is the open analytic input required to discharge `PrimeCoalescentSurplusAtMost β` (`β < 5/36` for `> 2/3` and `β ≤ 1/18` for `≥ 3/4` simple critical-line zeros).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, modulo-`4` bijection and half-scale transfer design
- [x] 1 → 2  fully-proven: complete paper proof of the unconditional model transfer and parity-lock identities in `logs/astra-2710-research.log` (Part VI, Milestone 1)
- [x] 2 → 3  formalized: Lean module `ParitySensitiveRamanujanStabilizerTransfer.lean` (zero conditional premises), `lake --old env lean` exit 0, transitive axioms `[propext, Classical.choice, Quot.sound]`

## Proof
1. **Parity Lock and Odd-Modulus 2-Isomorphism (`ramanujanLagCoefficient_two_even`, `ramanujanLagCoefficient_odd_two_mul`, `ramanujanLagCoefficient_two_mul_odd_two_mul`):** Since `gcd(q, 2r) = gcd(q, r)` for odd `q`, the divisor bijections `d ↦ d` (odd divisors) and `d ↦ 2d` (even divisors, weighted by `μ(2q/(2d)) = μ(q/d)`) preserve `c_q(r)` identically, while `c_2(2r) = μ(1)·2 + μ(2)·1 = 1` for every `r : ℕ`.
2. **Modulo-`4` Pairing and Ward–Mertens Top-Octave Identity (`sum_singularSeries_evenShift_eq_odd_split`, `sum_sqfreeTotientInv_eq_odd_add_half_odd`, `two_mul_sum_odd_sqfreeTotientInv_eq_add_topOctave`):** Partitioning `Icc 1 N` into odd `q`, doubled odd `2q` (`q ≤ N/2`, where `φ(2q) = φ(q)` and `sqfreeTotientInv (2q) = sqfreeTotientInv q / 2`), and multiples of `4` (`sqfreeTotientInv (4k) = 0`) equates `2 ∑_{q≤Q, q odd} sqfreeTotientInv q` to `∑_{n=1}^Q sqfreeTotientInv n + ∑_{Q/2<q≤Q, q odd} sqfreeTotientInv q`.
3. **Even-Shift Singular-Series Model Coalescent Transfer (`abs_poisson_evenShift_cosTransform_add_le`, `abs_sum_odd_singularSeries_evenShift_cosTransform_add_le`, `abs_sum_full_evenShift_singularSeries_cosTransform_add_le`):** Euler–Maclaurin Riemann-sum comparison transfers the `q ∈ {1, 2}` Poisson-parity baseline on `h = 2r`, while substituting half-scale `m' = m / 2` into `abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le` and bounding the `|1/(2r) - 1/(2r ± 1)|` shift error transfers all odd moduli `3 ≤ q ≤ N`.
4. **Centered Stabilizer Discrepancy & Actual Prime-Pair Parity Lock (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`, `primeCoalSum_ramanujan_two_eq`, `primeCoalSum_ramanujan_two_mul_odd_eq`):** Exact decomposition of `oddEvenShiftPrimeCoalSum` around `stabilizerModelOddCoalSum Q`, together with exact `q = 2` parity lock and `(q, 2q)` doubling invariance on the actual prime pairs in `primeCoalSum` (`θ₀ < 1/3`).

## Recorded Open Analytic Gap (Unproved Discrepancy Input — Not Hidden in Premises)
Evaluating the parity-locked Ramanujan singular-series model (`stabilizerModelOddCoalSum Q`) **does not bound `stabilizerDiscrepancyOddCoalSum Q`** and therefore **does not discharge `PrimeCoalescentSurplusAtMost β`** (`β < 5/36` or `β ≤ 1/18`). Discharging `PrimeCoalescentSurplusAtMost β` at bandwidth `λ = 4/3` (`X = (T/2π)^{4/3}`, even shifts `2r ≪ T^{1/3+η} = X^{1/4+3η/4}`) remains an open problem in analytic number theory facing two simultaneous obstructions:
1. **Selberg Twin-Prime Parity Barrier on Unsigned Majorants:** On the positive inner lobe `|θ| ≤ π/(3T)` where `cosTransform Ω θ ≥ (1/2) cosTransform Ω 0`, any upper-bound sieve factor `Υ > 1` on even-shift prime pairs inflates the `q ∈ {1, 2}` baseline by `(Υ - 1) T^{4/3} / log T ≫ N(T, 2T)` (`parityBlind_refutes_quadratic_and_fourThirds_budgets`), while asymptotic Hardy–Littlewood prime-pair averages are currently unconditional only down to shifts `H ≥ X^{7/12+ε} ≫ X^{1/4}`.
2. **Off-Critical Zero-Wave Resonance (`β₀ > 7/8` at `λ = 4/3`, or `β₀ > (λ + 1)/(2λ)` in general):** Any nontrivial zero at abscissa `β₀ > 7/8` contributes an oscillatory wave of scale `T^{(8/3)β₀ - 4/3} log T ≫ N(T, 2T)` inside `stabilizerDiscrepancyOddCoalSum Q`.

Per Proof Integrity rules, no conditional `PrimeCoalescentSurplusAtMost β → ...` wrapper is retained in `ParitySensitiveRamanujanStabilizerTransfer.lean`; only unconditional theorems are formalized, and the missing centered prime-pair discrepancy bound is recorded explicitly here.

## Lean
- Module: `formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean`
- Umbrella: `formal/GaloisForLFunctions/TransThresholdPairCorrelation.lean`

## Log
- 2026-10-27 — created in `1-in-progress`, formalized unconditional parity-sensitive singular-series transfer and actual prime-pair parity lock in Lean 4, removed conditional `PrimeCoalescentSurplusAtMost β` wrapper per Proof Integrity audit, verified `lake --old env lean` exit 0, and promoted unconditional model-transfer theorem to `3-formalized` with the open discrepancy gap recorded.
