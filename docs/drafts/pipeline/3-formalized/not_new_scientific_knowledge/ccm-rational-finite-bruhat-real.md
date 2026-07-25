# Rational finite-adele Bruhat reflection

- **Status:** Formalized in Lean
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** Finite local analytic factor of the CCM Real-Brauer lift

## Statement

Let \(X\) be a topological abelian group. On compactly supported locally constant
complex-valued functions define
\[
  (Rf)(x)=\overline{f(-x)}.
\]
Then \(R\) preserves local constancy and compact support, is conjugate-linear, and satisfies
\(R^2=1\). In particular this supplies an even \(K_{\mathbb R}\)-structure on the finite-adele
Bruhat--Schwartz factor
\[
  C_c^\infty(\mathbb A_{\mathbb Q,f},\mathbb C).
\]

## Proof

Negation is a homeomorphism of \(X\), so precomposition preserves local constancy and compact
support. Complex conjugation preserves local constancy and does not change support because
\(\overline z=0\) exactly when \(z=0\). Conjugate-linearity and \(R^2=1\) are pointwise.

## Hostile checks

- Compact support is proved through homeomorphic pullback, not inferred from pointwise decay.
- Result formalizes the algebraic Bruhat factor. Its LF topology is not present in mathlib and
  remains a separate completion obligation.
- No numerical, trace, positivity, spectrum, or RH premise occurs.

## Gates

- [x] Dependency-closed proof
- [x] Formalized in Lean; cached leaf builds and axiom audit passed
- [ ] LF topology and continuity formalized
- [ ] Tensor-product identification with full rational adelic Bruhat--Schwartz space

## Log

- 2026-07-25 — isolated after mathlib audit found finite adeles and locally constant maps but
  no packaged Bruhat--Schwartz restricted-product topology.
- 2026-07-25 — formalized generically in `KRealCompactlySupportedLocallyConstant.lean` and
  instantiated on mathlib's rational finite adele ring in `CCMRationalFiniteBruhatReal.lean`.
  Axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
