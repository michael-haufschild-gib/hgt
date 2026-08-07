# The Mertens function as the Mellin datum of `1/ζ`

- **ID:** partial-sum-mellin-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** for `Re s > 1`,

  `1/ζ(s) = s ∫_1^∞ M(⌊t⌋) t^(-(s+1)) dt`,   `M(m) = ∑_{k ≤ m} μ(k)`.

## Correction of an earlier version of this card

The general integral representation — a Dirichlet series as `s` times the Mellin transform of the partial
sums of its coefficients — is **mathlib's**, `LSeries_eq_mul_integral` and `LSeries_eq_mul_integral'`
(`Mathlib/NumberTheory/LSeries/SumCoeff.lean`), and its zeta instance is **the corpus's**,
`RHTower.riemannZeta_eq_mul_integral_floor` (`RHTower/FractionalPartZeta.lean`). An earlier version of
this card claimed both as new; they were re-proofs and have been deleted. What survives, and is new, is
the Möbius instance, three lines from `‖μ‖ ≤ 1` and `RHTower.LSeries_moebius_eq_inv_riemannZeta`.

The search that would have found the general theorem is a grep for the *conclusion shape*
(`s * ∫ t in Ioi 1`, `Icc 1 ⌊t⌋₊`) in mathlib's `NumberTheory/LSeries` and in the corpus — not a query
about "Mellin transform of a partial sum", which is the concept name and appears nowhere in it.

## Module

`formal/GaloisForLFunctions/RHTower/Sieve/PartialSumMellinBridge.lean` —
`inv_riemannZeta_eq_mul_integral_mertens`.

## Why it matters

The kernel attached to the vertical line is `1/s`, decaying like `1/|t|`. Every other Perron passage in
the corpus goes through a *smoothed* cutoff, whose kernel is the Mellin transform of the smoothing
profile: that is what forced the two integrations by parts and the `∫‖W‖ ≍ N log N` estimate behind the
`(log N)²` loss of the pointwise Halász route (`halasz-programme-session-index.md`, no-go 1).

It is also the identity underlying the Mertens-type criteria: `M(x) = O(x^θ)` makes the right-hand side
converge for `Re s > θ`. No criterion is stated — the corpus's own audit
(`rh-criterion-reencoding-template`) records that re-encoding RH as another criterion does not advance
the proof — but the identity is the unconditional half that any such argument consumes, and it was
missing.
