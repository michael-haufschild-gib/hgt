# Sonin to prime--Gamma per-test trace-Hankel transfer

- **ID:** `sonin-prime-arch-per-test-trace-hankel-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[FORMALIZATION] [BRIDGE] [NOT AN RH PROOF]`
- **Source:** top-down whole-corpus RH sweep
- **Statement:** An explicit positive aperture schedule along which every integer-polynomial
  all-prime Sonin Gram value converges to the corresponding normalized prime--Gamma trace-Hankel
  value implies the Riemann hypothesis.

## Goal

Expose the smallest source-to-source coupling between the unconditional all-prime Sonin Gram
positivity theorem and the countable prime--Gamma trace-Hankel RH criterion.  The coupling contains
no Xi divisor, zero location, real-rootedness, or RH-equivalent limiting measure.

For an explicitly supplied schedule

```text
aperture : Int[X] -> Nat -> Real,
```

the premise is

```text
aperture(P,j) > 0,

Re SoninTraceHankel(aperture(P,j),P)
  -> Re PrimeArchTraceHankel(P)                         (1)
```

for every integer polynomial `P`.  The schedule may depend on the countable test, but it is an
argument of the predicate rather than an existential selector defined after inspecting the target
quadratic value.

The formal chain is

```text
SoninPrimeArchPerTestTraceHankelCoupling aperture
  -> PrimeArchSourceTraceHankelIntNonnegative
  -> RiemannHypothesis.                                  (2)
```

## Gates

- [x] 0 → 1 in-progress: source objects and non-circularity condition explicit
- [x] 1 → 2 fully-proven: nonnegative limits and the existing countable prime--Gamma endpoint prove
  `(2)`
- [x] 2 → 3 formalized: exact module build and axiom checks pass
- [ ] 3 → 4 publication-ready: only together with a source proof constructing an aperture schedule
  satisfying `(1)`

## Proof

For each integer polynomial `P`, every Sonin trace-Hankel value in `(1)` is nonnegative by
`soninAllPrimeTraceHankel_re_nonneg`.  Closedness of the nonnegative half-line makes the limiting
prime--Gamma value nonnegative.  Hence
`PrimeArchSourceTraceHankelIntNonnegative` holds, and
`riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative` proves RH.

## Non-circularity and open source theorem

This bridge does not prove the convergence premise.  The residual all-prime Sonin moment sequence
has a different arithmetic law from the prime--Gamma sequence: block orthogonality deletes mixed
prime words and residual energy squares coefficients.  Thus positivity and Hankel collapse alone
do not discharge `(1)`.

The positive research problem is to construct the supplied schedule from a common finite-degree
log-position/Sonin/Gamma carrier and prove `(1)` through the continued prime--archimedean trace.
An aperture chosen from the sign of the target value, or an arbitrary sequence of nonnegative
numbers converging to it, is forbidden.

## Lean certificate

The declarations are in
`formal/GaloisForLFunctions/RHTower/SoninPrimeArchPerTestTransfer.lean`:

- `SoninPrimeArchPerTestTraceHankelCoupling`;
- `primeArchSourceTraceHankelIntNonnegative_of_soninPerTestCoupling`;
- `riemannHypothesis_of_soninPrimeArchPerTestTraceHankelCoupling`.

The exact module build passes.  Both the transfer theorem and RH capstone use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-12 — Source-to-source per-test Sonin/prime--Gamma chain formalized and verified.
