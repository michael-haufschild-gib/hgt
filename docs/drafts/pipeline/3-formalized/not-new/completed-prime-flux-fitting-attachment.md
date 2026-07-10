# Normalized prime-flux residue and canonical seam share the scalar `-1`

- **ID:** completed-prime-flux-fitting-attachment
- **Stage:** 3-formalized / not-new
- **Type:** `[BRIDGE]` local logarithmic-residue calculation plus scalar coincidence
- **Status:** `[PROVED IN LEAN; ATTACHMENT INTERPRETATION REJECTED]`

## Claim

At every zero `rho` of `xi` in the open critical strip, if `m=ord_rho(xi)`, then the continued
prime flux `-zeta'/zeta` has multiplicity-normalized punctured limit `-1`.  The separately defined
canonical cutoff seam at depth `m` has boundary jet `[-1]` in `Q[X]/(X^m)`.

Both statements are correct and formalized.  Their conjunction is only a scalar coincidence:

- the logarithmic residue is divided by `m`, which forces its value to be `-1` at every zero;
- `canonicalCutoffTorsionSeam` was already defined so that its boundary is the constant jet `[-1]`.

There is no constructed homomorphism, natural transformation, or compatibility law sending the
Euler/von-Mangoldt source to the Fitting quotient.  Calling this an attachment would therefore
overstate the theorem.

## Formal surface

- `exists_xi_normalizedLogDeriv_factorization` and `xi_normalizedLogDeriv_tendsto_order` give the
  general local logarithmic-residue formula.
- `xi_analyticOrderAt_eq_riemannZeta_of_mem_strip` transfers multiplicity from `xi` to `zeta` because
  the archimedean factor is a unit in the open strip.
- `riemannZeta_negative_normalizedLogDeriv_tendsto_neg_one_of_mem_strip` proves the normalized
  prime-flux residue statement without a simple-zero assumption.
- `xiCanonicalFittingSeamAt_hasNontrivialFittingBoundary_iff` classifies nontriviality of the
  point-dependent canonical cutoff seam by `xi rho=0`; this uses the analytic order itself as the
  seam depth.
- `infinitePrimeFlux_eq_vonMangoldtLSeries` records the right-half-plane Euler source.
- `infinitePrimeFlux_fitting_scalar_coincidence_of_mem_strip` packages the two `-1` statements and
  explicitly asserts no map between them.

## Anti-theatre verdict

- `[SEARCH]` A logarithmic derivative has residue equal to the zero multiplicity.
- `[BRIDGE]` In the open strip, `xi` and `zeta` have the same order because the Gamma factor is a
  unit.
- `[REJECTED]` The normalized residue does not supply the order-independent Euler--Gamma
  compatibility sought by the prime-jet program.
- `[REJECTED]` The canonical seam imports a cutoff presentation.  It cannot answer the user's
  carrier-free constraint question.
- `[USEFUL INFRASTRUCTURE]` The local factorization and multiplicity transfer remain reusable Lean
  theorems.

## Open core

`[OPEN CORE]` Construct an actual fixed arithmetic map or relation whose restrictions give the
prime-jet defects.  Equality of two scalars chosen or normalized to `-1` is insufficient.  The map
must be independent of a target zero, analytic order, cutoff depth, and separately selected finite
support.

## Verification history

The module previously passed direct compilation, its exact target build, and an axiom audit.  This
card is demoted for novelty/significance, not mathematical incorrectness.
