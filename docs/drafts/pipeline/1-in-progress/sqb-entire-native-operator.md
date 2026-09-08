# SQB: native operator for the entire Casimir transform

Status: construction in progress; RH unproved.

## Proof chain

Original Maass source → modular curvature and exact mass → quarter domination →
Selberg gap → independently constructed Xi occurrence → RH.

The entire scalar transform `F` from
`RHTower.SelbergScatteringEntireTransform` survives the polynomial obstruction.
Its real native preimage criterion alone is equivalent to critical placement of
each Xi zero. It does not supply occurrence. Literal occurrence of the original
complex scattering energy in the native modular domain has a strictly positive,
sharp residual floor (`sqb-native-domain-residual.md`).

## Construction under investigation

Use the original modular embedding `J` and covariance `B = J J†`; the actual
energy operator is the closed inverse of `B`, with normalization `A = 1 − Δ_H`.
For positive real `x`, set

`g(x) = 1 / (F(1/x − 1).re + 2)`, with `g(x) = 0` for `x ≤ 0`.

Establish continuity at zero from the growth of `F` on the positive real ray.
Then construct `C = g(B)` by bounded continuous functional calculus and use
the closed inverse of `C`, shifted by `−2`, as the native realization of
`F(A − 1)`. Required conclusions include its actual graph domain, dense domain,
self-adjointness, lower bound, and its relation to the original source.

The kernel step must be proved, not assumed: a continuous scalar symbol with
no extra zeros on the spectrum preserves injectivity. A proposed proof uses
Dini convergence of `x² / (1 + n g(x)²)` and functional-calculus multiplication.
This is a proof construction, not a numerical approximation used as evidence.

## Current obligations

- [ ] Prove the functional-calculus kernel preservation theorem.
- [ ] Prove continuity and bounds for the reciprocal entire symbol.
- [ ] Construct and audit the actual modular transformed operator and domain.
- [ ] Construct Xi occurrence independently of critical placement.
- [ ] Close the remaining quarter-domination and RH chain unconditionally.

## Corpus basis and audit discipline

Broad OR searches cover functional calculus, closed inverses, spectral mapping,
analytic vectors, semigroups, kernels, injectivity, dense range, and uniform
approximation. Metadata discovery is followed by reading relevant proofs;
search coverage is not a claim to have read every returned proof.

Relevant existing constructions: `FriedrichsFormOperator`,
`BoundedPerturbedFriedrichsOperator`, `ClosedHyperplaneInverse`,
`CfcEigenvector`, `CfcNormBound`, and mathlib's Dini theorem. All new results
require foreground scratch checks, individual module audits, and axiom audits.
The frontier map is read-only. No numerical experiment is involved.
