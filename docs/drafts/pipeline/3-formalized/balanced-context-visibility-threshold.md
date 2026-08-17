# Exact visibility threshold for the balanced context anomaly

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN PROVED]`

Lean: `formal/GaloisForLFunctions/HTGeometry/ContextOrderVisibilityThreshold.lean`, headline
`visibilityAttenuatedBalancedContext_posSemidef_iff`. Visibility is intrinsically restricted to
`[0,1]`; theorem is closed without added axioms.

Source: Appendix A of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Statement

At order `n = r + 3`, attenuate every off-diagonal entry of the balanced context kernel by
visibility `1 - eta`, where `eta` lies in `[0,1]`. The attenuated full kernel is positive
semidefinite exactly when

`eta >= 1 / (2(r + 2))`.

## Dependency-closed proof

The attenuated coherence scale is

`t' = (1 - eta) 2/(2r+3)`.

The equality-pattern kernel decomposes orthogonally into the constant line and its complement. Its
two coefficients are

`1 + t'`

and

`1 - (r+2)t' = (2(r+2)eta - 1)/(2r+3)`.

Because `eta` lies in `[0,1]`, the transverse coefficient `1+t'` is positive. Therefore the kernel
is positive semidefinite iff its constant-line coefficient is nonnegative. The denominator
`2r+3` is positive, and the latter inequality is equivalent to

`eta >= 1/(2(r+2))`.

Necessity may also be read directly by evaluating the positive-semidefinite quadratic form on the
constant section; sufficiency follows by adding the two nonnegative multiples of the orthogonal
harmonic projections.
