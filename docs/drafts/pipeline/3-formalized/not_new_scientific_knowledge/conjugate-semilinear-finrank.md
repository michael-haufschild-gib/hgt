# Conjugate-semilinear equivalences preserve complex finrank

- **ID:** `conjugate-semilinear-finrank`
- **Stage:** 3-formalized
- **Type:** STANDARD LINEAR ALGEBRA (Lean)
- **Role:** finite-rank transport for quaternionic operator conjugation

## Theorem

For complex modules \(E,F\), every conjugate-semilinear equivalence
\[
  e:E\overset{\sim}{\longrightarrow}F
\]
preserves complex finrank:
\[
  \operatorname{finrank}_{\mathbb C}E
   =\operatorname{finrank}_{\mathbb C}F.
\]

## Proof

Because complex conjugation fixes \(\mathbb R\), \(e\) is an \(\mathbb R\)-linear equivalence.
Therefore the real finranks agree. For every complex module \(M\),
\[
  \operatorname{finrank}_{\mathbb R}M
   =2\operatorname{finrank}_{\mathbb C}M.
\]
Canceling the factor \(2\) proves the claim. No finite-dimensional hypothesis is needed because
mathlib's finrank convention and the real/complex finrank identity apply uniformly.

## Lean realization

Module:

- `GaloisForLFunctions.RHTower.KRealConjugateFinrank`

Capstones:

- `conjugateLinearEquivToReal`;
- `finrank_eq_of_conjugateLinearEquiv`.

## Gates

- [x] dependency-closed paper proof
- [x] unconditional Lean proof
- [ ] publication relevance: standard infrastructure, not claimed novel

## Log

- 2026-07-25 — extracted while proving that quaternionic conjugation preserves approximation
  numbers. Scratch Lean check passed; no computation or spectral premise used.
