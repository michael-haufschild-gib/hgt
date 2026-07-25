# Rational CCM archimedean signed Poisson decay

- **ID:** ccm-q-arch-schwartz-poisson
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Source:** `ccm-rational-cyclic-diagonal-poisson-decay.md`
- **Statement:** In the \(1_{\widehat{\mathbb Z}}\) sector, the CCM integer-lattice trace obeys
  exact scaled Poisson duality; vanishing of evaluation and integral gives explicit
  arbitrary-power bounds at both multiplicative ends.

## Result

For \(f\in\mathcal S(\mathbb R,\mathbb C)\), \(a>0\), define
\[
  \Theta_f(a)=\sum_{n\in\mathbb Z}f(an).
\]
Lean proves
\[
  \Theta_f(a)=a^{-1}\Theta_{\widehat f}(a^{-1}).
\]
For every \(N\), it defines \(p_N=2(N+1)\) and an explicit nonnegative constant \(C_N(f)\).
If \(f(0)=0\), then
\[
  \|\Theta_f(a)\|\le C_N(f)a^{-p_N}.
\]
If \(\widehat f(0)=0\), then
\[
  \|\Theta_f(a)\|\le C_N(\widehat f)a^{p_N-1}.
\]
Finally Lean proves
\(\widehat f(0)=\int_{\mathbb R}f\), so the two CCM source cancellations yield both bounds
simultaneously.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzPoisson`
- Capstones:
  - `ccmRationalArchimedeanLatticeTrace_poisson`
  - `ccmRationalArchimedeanLatticeTrace_large_bound`
  - `ccmRationalArchimedeanLatticeTrace_small_bound`
  - `ccmRationalArchimedeanLatticeTrace_twoSidedDecay`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/CCMRationalArchimedeanSchwartzPoisson.lean`
- Axioms for every capstone:
  `[propext, Classical.choice, Quot.sound]`
- Aggregate module imported by `GaloisForLFunctions.RHTower`.

## Boundary

This proves value-level two-ended decay for the basic finite-adele sector. It does not yet
prove:

- bounds for every multiplicative derivative;
- reduction of a general compactly supported locally constant finite-adele factor to periodic
  weighted lattice sums;
- finite Fourier duality for those periodic weights;
- Bruhat--Schwartz LF continuity or cyclic-degree completion.

## Gates

- [x] Source theorem isolated
- [x] Dependency-closed paper proof
- [x] Formalized without project axioms
- [x] Direct leaf check
- [x] Capstone axiom audit
- [ ] Final aggregate `lake build` audit

## Log

- 2026-07-25 — Formalized exact scaled Poisson identity and explicit two-ended
  arbitrary-power estimates. No numerical computation used.
