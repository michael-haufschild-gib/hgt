# Semidefinite Toeplitz-to-atomic factorization

- **ID:** psd-toeplitz-atomic-factorization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Connes--van Suijlekom, arXiv:2511.23257, finite step preceding Corollary 1.1
- **Statement:** Every normalized Hermitian circle-moment sequence whose `T_N` Toeplitz section is PSD admits a positive unit-circle atomic realization of that same `T_N`.

## Goal

Close the reverse direction missing from the existing `BᴴB` atomic theorem. This is not a
rank/corank-one shortcut: it supplies a finite atomic factorization for every normalized
PSD Toeplitz section. The corank-one root theorem still needs its sharp support/rank extraction.

## Gates

- [x] 0 → 1 in-progress: exact finite statement, primary-source audit, and non-circular route
- [x] 1 → 2 fully-proven: diagonal `ε` perturbation → strict Bernstein--Szegő probability laws → compact weak cluster measure → finite circle cubature → atomic Gram identity
- [x] 2 → 3 formalized: `exists_probabilityMeasure_circleToeplitzGram_eq_of_posSemidef_same` and `exists_atomic_caratheodoryFejer_psd_factorization` in `CaratheodoryFejerPSDtoAtomicFactorization.lean`; source check and leaf build green
- [ ] 3 → 4 publication-ready: standalone proof/certificate

## Paper proof

For `ε_m = 1/(m+1)`, put
`c_m(q) = (1+ε_m)⁻¹ (c(q) + ε_m 1_{q=0})`.
Then
`T_N(c_m) = (1+ε_m)⁻¹ (T_N(c)+ε_m I)` is positive definite and
`c_m(0)=1`. Bernstein--Szegő gives a probability law `μ_m` with the required
finite Fourier prefix. Probability laws on the compact circle have a cluster point `μ`.
Weak continuity of each circle Fourier character and `c_m(q) → c(q)` identify
`T_N(μ)=T_N(c)`. Finite-dimensional Carathéodory cubature of the first `N`
real/imaginary Fourier coordinates of `μ` gives `2N+1` nonnegative unit-circle atoms;
Hermitian reconstruction identifies their Vandermonde `BᴴB` Gram matrix with `T_N(c)`.

## Hostile audit

- **Rank claim:** this proof deliberately does not give rank-many/distinct atoms. That sharper
  support statement is separately necessary for the exact corank-one root conclusion.
- **Circularity:** no circle measure for the PSD input is assumed; it is obtained as a compact
  limit of strict measures.
- **Zero depth:** handled separately by the unit Dirac probability law, because the
  Bernstein--Szegő prefix theorem begins at a positive section depth.
- **External status:** the cited 2025 paper proves a stronger corank-one conclusion through a
  C*-algebraic Carathéodory--Fejér argument. This perturbation proof is a standard finite
  truncated-Herglotz realization route, not claimed novel.

## Log

- 2026-08-19 — `[LEAN-PROVED]` exact same-level PSD realization and atomic factorization;
  `lake env lean` source check and targeted leaf build passed. Standard Lean axioms only:
  `propext`, `Classical.choice`, `Quot.sound`.
