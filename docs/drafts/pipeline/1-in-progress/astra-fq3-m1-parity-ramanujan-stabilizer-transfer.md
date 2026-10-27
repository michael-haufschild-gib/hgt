# Parity-Sensitive Multi-Modulus Ramanujan Stabilizer Transfer on Even Shifts

**Stage:** `1-in-progress`
**Category:** `RH-core`
**Created:** 2026-10-27
**Updated:** 2026-10-27

## Statement
Establish the unconditional parity-sensitive multi-modulus Ramanujan stabilizer calculus on the odd-prime even-shift coalescent sum `oddEvenShiftPrimeCoalSum` (`TransThresholdPairCorrelation`):
1. **Parity Lock at `q = 2` and Odd-Modulus 2-Isomorphism:** `ramanujanLagCoefficient 2 (2 * r) = 1` for every `r ≥ 1`, and `ramanujanLagCoefficient q (2 * r) = ramanujanLagCoefficient q r` for every odd modulus `q` (`q % 2 = 1`) and every `r : ℕ`.
2. **Exact Parity-Halving Ward–Mertens Bijection Law:** For every `Q : ℕ`, splitting `Finset.Icc 1 Q` into odd moduli `q`, doubled odd moduli `2q` (`q ≤ Q / 2`), and multiples of `4` (`sqfreeTotientInv (4k) = 0`) yields
   $$\sum_{n=1}^Q \operatorname{sqfreeTotientInv}(n) = \sum_{\substack{1 \le q \le Q \\ q \text{ odd}}} \operatorname{sqfreeTotientInv}(q) + \sum_{\substack{1 \le q \le Q/2 \\ q \text{ odd}}} \operatorname{sqfreeTotientInv}(q),$$
   so $2 \sum_{1 \le q \le Q,\, q \text{ odd}} \operatorname{sqfreeTotientInv}(q) \ge \sum_{n=1}^Q \operatorname{sqfreeTotientInv}(n)$, reconciling the parity doubling factor `2` on even shifts with the full Ward–Mertens repulsion slope.
3. **Parity-Sensitive Singular-Series Coalescent Transfer on Even Shifts (`2r`):** Substituting half-scale `m / 2` into `abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le` transfers the parity-doubled odd-modulus singular-series sum over even shifts `2r` (`1 ≤ r ≤ q R_q`, `3 ≤ q ≤ Q`, `q` odd, `Q b ≤ m`) unconditionally to `-cosTransform Ω 0 * ∑_{3 ≤ q ≤ Q, q odd} sqfreeTotientInv q` with explicit finite-height error.
4. **Centered Stabilizer Discrepancy Decomposition & Proportion Milestones:** Exact decomposition of `oddEvenShiftPrimeCoalSum` around any symmetric lag model `M(n, m)` into the model sum plus centered discrepancy, coupled with the unconditional critical-line proportion consequences of `PrimeCoalescentSurplusAtMost β` at `β < 5/36` (`> 2/3`), `β ≤ 577/4500` (`≥ 254/375`), and `β ≤ 1/18` (`≥ 3/4` critical-line simple zeros).

**Recorded Open Analytic Gap (Proof Integrity Audit):** Unconditionally certifying `PrimeCoalescentSurplusAtMost β` at fixed `β < 5/36` for `λ = 4/3` requires simultaneously overcoming two open analytic barriers identified in Phase 3: (i) Selberg's twin-prime parity barrier on unsigned majorants (`M_T(0) ≥ ½` forces `(Υ - 1) T^{4/3} ≫ T` unless `Υ = 1`), and (ii) the resonant off-line zero wave (`β₀ > 7/8` at `λ = 4/3`, or `β₀ > (λ+1)/(2λ)` in general, produces `T^{(8/3)β₀ - 4/3} log T ≫ N(T, 2T)`). We prove every algebraic/analytic stabilizer transfer unconditionally without hiding any unproved analytic input in hypotheses.

## Idea
Exploit `gcd(q, 2r) = gcd(q, r)` for odd `q` and `φ(2q) = φ(q)` for odd `q`, reducing the even-shift singular series at scale `m` to the all-integer-shift Ramanujan transfer at half-scale `m / 2`.

## Dependencies
- `TransThresholdPairCorrelation/CoalescentPrimeReductionAndParitySieve.lean`
- `TransThresholdPairCorrelation/RamanujanDirichletCoalescentTransfer.lean`
- `SelectivePositivityAndThresholdLaws/ParityLobeObstructionAndEscapeLaplaceSplit.lean`

## Proof
See `logs/astra-2710-research.log` Part VI (Milestone 1).

## Audit
- [x] Proof complete (no gaps)
- [x] Dependencies verified
- [x] Checked against kills (`docs/reports/rh-killed-routes.md`)
- [ ] Formalised in Lean 4

## Lean
- Target: `formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean`
- Umbrella: `formal/GaloisForLFunctions/TransThresholdPairCorrelation.lean`
