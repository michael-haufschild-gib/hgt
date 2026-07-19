# Polynomial-multiplier preservation of functional hypertranscendence

- **ID:** polynomial-multiplier-hypertranscendence-preservation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `HTGeometry/GaugeReductionToMultiplicative.lean`; the generic substitution and triangular-solvability library
- **Statement:** Multiplication by any nonzero complex polynomial preserves hypertranscendence of an entire-smooth function; an arbitrary subsequent polynomial shift preserves it as well.

## Goal

Close the multiplicative direction needed by the regularized Herglotz gauge.  The theorem is stated
for an arbitrary nonzero polynomial, so it subsumes the special multiplier `1 + z^2` and every
later polynomial-gauge consumer.

## Gates

- [x] 0 → 1  in-progress: exact open interface and polynomial substitution identified
- [x] 1 → 2  fully-proven: complete paper proof below, with no open dependency
- [x] 2 → 3  formalized: `MulPolynomialInvariance.lean`, exact leaf build, and axiom audit
- [ ] 3 → 4  publication-ready: standalone paper treatment

## Statement

Let `a in C[z]` be nonzero and let `f : C -> C` be smooth to every complex order.  Then

```text
DA(z |-> a(z) f(z))  ->  DA(f),
HT(f)                 ->  HT(z |-> a(z) f(z)).
```

More generally, if

```text
m(z) = b(z) + a(z) C(z)
```

with polynomial `b`, then smoothness and hypertranscendence of `C` imply
hypertranscendence of `m`.  No separate differentiability hypothesis for each product or shifted
product jet remains.

This card deliberately does not claim the converse functional implication.  The direction above
is the exact one required to transport a known HT carrier through the regularized Herglotz gauge;
the abstract differential-field API already has two-sided invertible-base-gauge invariance.

## Paper proof

Fix a differential relation of order `N` for `a f` and write `x` for its spectral coordinate.  For
each `0 <= k <= N`, the Leibniz law gives

```text
(a f)^(k) = sum_(i=0)^k binom(k,i) a^(i) f^(k-i).
```

Substitute the right-hand side for the `k`-th jet variable of the relation while fixing `x`.
This is a polynomial substitution.  Ordered by jet degree, it is triangular: its `k`-th coordinate
has diagonal term `a(x) f^(k)` and a polynomial expression in lower jets.

The substitution is injective.  On the Zariski-open locus `a(x) != 0`, any prescribed finite target
jet packet has a preimage: fix the spectral coordinate and solve the triangular system recursively,
dividing every layer by the common diagonal `a(x)`.  The substitution-nonvanishing criterion then
says that the substitution cannot kill a nonzero polynomial, because the nonzero polynomial
`a(x)` defines precisely the exceptional locus omitted by the point-map covering.  The substituted
relation is therefore nonzero and vanishes on every jet packet of `f`.  This proves
`DA(a f) -> DA(f)`; contraposition gives `HT(f) -> HT(a f)`.

Finally, additive polynomial invariance removes `b`.  Infinite complex smoothness supplies all of
the per-jet differentiability premises required by that older interface, so the affine-gauge
capstone has only the natural smoothness and HT hypotheses.

## Lean certificate

Module: `formal/GaloisForLFunctions/HTGeometry/MulPolynomialInvariance.lean`.

Principal declarations:

- `mulPolynomialJetImage` and `mulPolynomialJetSubst`;
- `bindPointMap_mulPolynomialJetImage`;
- `exists_mulPolynomialJetImage_preimage`;
- `mulPolynomialJetSubst_ne_zero`;
- `differentiallyAlgebraic_of_mul_polynomial`;
- `hypertranscendental_mul_polynomial`;
- `hypertranscendental_polynomialGauge`.

Validation on 2026-07-19:

- exact leaf build: `lake build GaloisForLFunctions.HTGeometry.MulPolynomialInvariance` — PASS;
- axiom audit of the substitution, DA transport, HT transport, and affine-gauge capstone — only
  `[propext, Classical.choice, Quot.sound]`.

## Novelty audit

This is a standard closure property, not new science.  Its value is exact interface closure: the
live corpus had isolated this missing multiplicative direction and built all generic nonvanishing
and triangular-solvability ingredients, but had not connected them.  The general theorem avoids a
one-off `1 + z^2` wrapper and removes the old product-jet Prop bundle.

## Log

- 2026-07-19 — exact paper theorem recorded after corpus-first gap audit
- 2026-07-19 — generalized polynomial multiplier and affine gauge formalized, exact leaf build and axiom audit passed
