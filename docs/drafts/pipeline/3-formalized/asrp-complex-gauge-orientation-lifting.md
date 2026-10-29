# Complex gauge orientation lifting

- **ID:** asrp-complex-gauge-orientation-lifting
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ASRP open topic 6, complex gauge stabilizer.
- **Statement:** Every prime torus gauge admits primewise conjugations preserving its real source at every prime power and making its imaginary partial sums square-root small. Consequently its real count holds exactly when some such complex lift satisfies the complex count.

## Goal

Determine whether passing from a real gauge to a complex Euler source introduces an unavoidable precision obstruction. Classify the obstruction for a fixed orientation and construct an orientation removing it without changing any real coefficient.

## Gates

- [x] In progress: source and conjecture specified; corpus searches completed.
- [x] Dependency-closed paper proof.
- [x] Leaf checked with `lake --old env lean`; transitive axioms audited; umbrella wired.

## Approach

For a fixed gauge, split the imaginary partial sum into the prime sine current and the proper-prime-power remainder, bounded by `psi - theta`. Choose signs greedily so the prime current stays within `log x` at every horizon. The same sign conjugates the whole Euler factor, preserving every cosine coefficient. Combine with the existing exact real gauge stabilizer.

## Novelty boundary

Existing ASRP classifies real gauges only. Scalar sign balancing is established mathematics and is not counted as a contribution. The proposed contribution is the arithmetic lifting theorem, including coherence across prime powers and the exact equivalence for complex counts. Global novelty remains unclaimed.

## Proof [PROVED HERE]

Write `q(x) = sqrt(x) log²(x)`, `z_t(p^k) = exp(2π i k t_p) log p`,
`D_t(x) = Σ_{p≤x}(1-cos(2πt_p))log p`, and `J_t(x) = Σ_{p≤x}sin(2πt_p)log p`.
The real part is the existing `torusGauge`. The imaginary contribution from proper prime powers has absolute value at most `psi(x)-theta(x) = O(sqrt(x))`. Hence

`ComplexCount(z_t) ↔ RH ∧ D_t = O(q) ∧ J_t = O(q)`.

This uses the existing unconditional real classifier `count_torusGauge_iff`, not RH as an assumption.

For construction, put `w_n = 1_Prime(n) sin(2πt_n)log n` and `S_0=0`.
If `S_(n-1) ≥ 0`, orient the next increment as `-|w_n|`; otherwise orient it as `|w_n|`.
This is achieved by choosing `u_n` equal to `t_n` or `-t_n`. Both choices preserve `cos(2π k t_n)` for every natural `k`, so every real prime-power coefficient is unchanged. The elementary inequality `|S_n| ≤ max(|S_(n-1)|, |w_n|)` and `|w_n|≤log n` give `|S_n|≤log n` by induction, with the empty and unit horizons handled directly. Thus `|J_u(x)|≤log x` for all `x≥1`, and

`|Im Σ_{n≤x} z_u(n)| ≤ log x + psi(x)-theta(x)`.

This proves `ComplexCount(z_u) ↔ Count(Re z_t)`. Conversely, any primewise conjugate lift satisfying the complex count gives the real count by taking real parts. The image of complex count gauges under independent Euler-factor conjugation is therefore exactly the real gauge stabilizer.

Any finite prefix may be restored to its original phases. This changes the prime sine weight on a finite set only, hence changes its partial sum by a bounded function. All real coefficients remain fixed, and the complex count criterion is unchanged. Thus a lift exists in every finite-coordinate neighborhood.

## Precision and calibration

- **Precision class:** fixed orientation requires both `D_t=O(q)` and `J_t=O(q)`. Allowing conjugations removes the current obstruction exactly; the deficit criterion remains.
- **Identity/ceiling:** cosine coefficients are preserved identically at every power. The ceiling is a logarithmic prime current plus the square-root proper-power mass. No integrality floor or Möbius inversion is used.
- **Parity:** sign gauges have zero sine current. Conjugation cannot alter their source, so the Liouville twin and cofinite flips still fail; finite flips retain the existing RH-equivalent criterion.
- **Remaining battery:** arbitrary sign gauges keep their exact flipped-mass test. Rescalings `cΛ`, additive power perturbations, and Beurling models are outside the unit-phase conjugation family; this construction does not erase their existing visible real discrepancies.
- **Finite fields:** preserving real traces cannot remove an outer Frobenius mode detected by `countAtPrecision_iff` in `CurvesCalibrateThePrecisionExponent.lean`; in particular the golden datum's real count and precision exponent are unchanged. The new arithmetic mechanism is coherent orientation across prime towers, whose nonprime portion already lies at square-root precision.

## Formalization

Leaf: `ArithmeticOfSquareRootPrecision/EveryRealGaugeHasAComplexCountLift.lean`.
Main targets: `complexCount_torusGauge_iff`, `imaginary_partialSum_balancedGauge_le`,
`complexCount_balancedGauge_iff`, `exists_complexCount_lift_iff`,
`exists_complexCount_lift_preserving_prefix`.
Final leaf check passed with `lake --old env lean GaloisForLFunctions/ArithmeticOfSquareRootPrecision/EveryRealGaugeHasAComplexCountLift.lean`, exit 0, no warnings. Umbrella import wired. All five main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; audit output: `logs/asrp-complex-gauge-axioms.txt`.
