# Prime--Gamma reciprocal-square sector criterion for RH

- **ID:** `prime-arch-reciprocal-square-sector-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** top-down whole-corpus RH sweep
- **Statement:** RH is equivalent to a single sector inequality for the explicit continued
  prime--Gamma reciprocal-square transform on the centered upper strip.

## Goal

Turn the paired reciprocal-square identity already present in the corpus into a source-value RH
criterion which is independent of the active rectangular lower-bound route.  If

```text
T(z) = continuedPrimeArchSourceRelativeTrace(z),
```

then the exact condition is

```text
0 < im z < 1/2 and zeta(1/2 + z I) != 0
  -> 0 <= re z * im (-T(z) / z).
```

The chain is

```text
continued prime--Gamma reciprocal-square sector sign
  -> the same sector sign for -logDeriv(XiC)(z) / z
  -> every off-axis upper-strip XiC zero would emit a negative sample
  -> no right-half Xi zero
  -> RiemannHypothesis.
```

## Exact reciprocal-square identity

Functional-equation reflection pairs the centered Xi divisor and gives, on the continued source
domain,

```text
-T(z) / z
  = sum_q xiZeroCopyReciprocalSquare(q)
      / (1 - z^2 * xiZeroCopyReciprocalSquare(q)).
```

Under RH every reciprocal-square coordinate is positive real.  The imaginary part of each
summand has the sign of `re z` in the upper half-plane, so multiplication by `re z` makes every
term nonnegative.  Absolute summability transfers the sign to the full source value.

## Positive local pole law

Let `alpha` be a zero of `XiC` with

```text
0 < im alpha < 1/2 and re alpha != 0.
```

The normalized logarithmic derivative has its full positive multiplicity as residue.  Along the
horizontal mesh `z_n = alpha + t_n`, choose the sign of `t_n` opposite to `re alpha`.  Then

```text
t_n * (-logDeriv(XiC)(z_n) / z_n)
  -> -m / alpha,
```

whose imaginary part is

```text
m * im alpha / normSq alpha > 0.
```

It follows that some regular `z_n` satisfies

```text
re z_n * im (-logDeriv(XiC)(z_n) / z_n) < 0.
```

This is recorded positively: every off-axis upper-strip zero emits a strict negative sector
sample.  Functional-equation reflection sends any hypothetical right-half Xi zero to such an
upper-strip zero.  A real reflected zero is excluded unconditionally by the real-strip nonvanishing
theorem.

## Non-circularity and open source obligation

The criterion itself is RH-equivalent, so it is not an unconditional RH proof.  Its source
function contains no zero enumeration, divisor-selected pole, limiting zero measure, or
anti-Herglotz assumption: it is the analytically continued prime flux plus the fixed Gamma
boundary term, followed by the fixed scalar transform `T(z) -> -T(z)/z`.

`[CONJECTURE]` The remaining research problem is to prove the sector inequality from an
independent prime--Gamma constraint, covariance, or positive-kernel representation.  A valid
provider must establish the sign before inserting Xi divisor locations.  The theorem shows that
one need not prove the full Weil cone, a limiting measure, real-rootedness, or the rectangular
subpower lower bound.

The new sector is not the existing anti-Herglotz gate in renamed coordinates.  The old condition
controls `im T(z)` on the upper strip.  The present condition controls
`re z * im(-T(z)/z)` and is the Stieltjes orientation naturally attached to the reciprocal-square
moment germ.

## Lean theorem surface

The module
`formal/GaloisForLFunctions/RHTower/PrimeArchReciprocalSquareSectorGate.lean` proves:

- `continuedPrimeArchReciprocalSquareTrace_eq_tsum`;
- `xiReciprocalSquareResolventTerm_sector_nonnegative_of_riemannHypothesis`;
- `continuedPrimeArchReciprocalSquareUpperSectorNonnegative_of_riemannHypothesis`;
- `xiReciprocalSquareUpperSectorNonnegative_of_continuedPrimeArch`;
- `exists_xiReciprocalSquareUpperSector_neg_of_zero`;
- `riemannHypothesis_of_xiReciprocalSquareUpperSectorNonnegative`;
- `riemannHypothesis_of_continuedPrimeArchReciprocalSquareUpperSectorNonnegative`;
- `xiReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis`;
- `continuedPrimeArchReciprocalSquareUpperSectorNonnegative_iff_riemannHypothesis`.

## Formal verification

- targeted module compilation passes;
- the module contains no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration;
- the local pole theorem and RH capstones print only `propext`, `Classical.choice`, and
  `Quot.sound`;
- the project formal lint gate passes.

## Gates

- [x] 0 -> 1 in-progress: source-pure reciprocal-square value relation isolated
- [x] 1 -> 2 fully-proven: termwise RH sign and local off-axis pole contradiction proved
- [x] 2 -> 3 formalized: exact target and continued-source equivalences compile in Lean
- [ ] 3 -> 4 publication-ready: only after an independent source-sector provider is found
