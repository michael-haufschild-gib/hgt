# LI logarithmic reflection: exact reciprocal-divisor balance

- **ID:** LI-LOG-RECIP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; symbolic paper audit underway
- **Source:** actual Cassini logarithmic-mass current in `LiEvenCrossCassiniLogMassPole.lean` and exact actual source multiplicities.
- **Objective:** classify cancellation outside the interior mass window, rather than presume every actual pole survives evenization.

## Candidate statement

Write `m(b)` for actual squared-Xi-node multiplicity, with zero multiplicity when `b` is absent. For positive mass `v`, at a logarithmic point `t₀` with `v exp(t₀)=−b`, the even germ

`R_v(t)=Γ(v exp t)+Γ(v exp(−t))`

has principal part

`8 [m(b)−m(v²/b)] / (t−t₀)³`.

There are no quadratic or simple terms. Thus the punctured meromorphic germ has an analytic representative exactly when reciprocal multiplicities balance; otherwise its pole has order three. This does not assert `AnalyticAt` of raw totalized Lean function at a canceled pole: assigned point value may differ from removable extension. This is an actual divisor classification, not a positivity premise.

## Derivation to audit

One source node contributes `D_b(z)=2mzb/(z+b)²` and `Γ_b(z)=4mzb(b−z)/(b+z)³`. On writing `z=−b exp(s)`, the universal local expression is

`m cosh(s/2)/sinh(s/2)³`.

It is odd, with principal part `8m/s³`; its quadratic and simple Laurent coefficients vanish. Direct transport contributes `+8m(b)` and reflected transport `−8m(v²/b)`. Analytic source remainders stay analytic. Exact cancellation therefore depends on multiplicity balance, not pole order alone.

A cleaner identity exposes the mechanism. Put `A_v(t)=C(1−v exp t)` and `F_v(t)=A_v(t)/A_v(−t)`. On regular punctured germs,

`R_v = 4 · deriv²(logDeriv F_v)`.

The meromorphic divisor order of `F_v` is exactly `m(b)−m(v²/b)`. Existing logarithmic-derivative local form gives a simple principal part, whose second derivative yields exactly the stated cubic term. Entire factors affect only analytic remainders. Generic pole amplification is classical; actual reciprocal-source classification still needs novelty/significance audit.

For a conjugate pair and mass `v=|b|`, reciprocal reflection pairs `b` with its conjugate. Equal conjugate multiplicities can cancel the complete local principal part. The small-mass gap used by LI-EJ-OSC excludes this case.

## Required audits

1. Search actual corpus for reciprocal-divisor cancellation and exact local logarithmic principal parts.
2. Verify actual source multiplicity conjugation and local factorization APIs.
3. Audit primary literature for this exact source classification; generic Laurent calculus is classical.
4. If new and useful, prove exact survivor in Lean with no unresolved source premises. Do not broaden current disjoint Lean scopes.

## Status

No new Lean theorem claimed. Main LI-EJ-OSC interior formalization continues independently. Proposed all-positive-mass oscillation extension needs only one sufficiently large actual node, whereas complete pole classification needs the sharper reciprocal balance law above.

## Log

- 2026-09-29 — Conjectured while testing extension of retained interior poles to arbitrary positive masses. Found a real cancellation mechanism at nodal modulus; replaced false universal-retention claim with exact signed multiplicity classification.
- 2026-09-29 — Independent audit found totalized-value pitfall: balance gives a removable meromorphic germ, not necessarily literal pointwise analyticity. Corrected statement; quotient-source identity supplies dependency-closed principal-part proof.
