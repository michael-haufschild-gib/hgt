# Krylov replica moment amplification law

- **ID:** `krylov-replica-moment-amplification-law`
- **Stage:** 3 — formalized
- **Type:** THEOREM
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Date:** 2026-08-06

## Statement

For finite complex spectral amplitudes

\[
 F(z)=\sum_i c_i e^{\lambda_i z},\qquad
 G(z)=\sum_j d_j e^{\mu_j z},
\]

assume

\[
 \sum_i c_i\lambda_i^k=0,
 \qquad
 \sum_j d_j\mu_j^k=0
 \quad(0\le k\le K).
\]

Then, for every replica order `r` and every
`ell < 2 r (K+1)`, one has

\[
 \left.\frac{d^\ell}{dz^\ell}
   \bigl(F(z)^rG(z)^r\bigr)\right|_{z=0}=0.
\]

Equivalently, annihilating the first `K+1` one-copy spectral moments forces
the paired `r`-replica action measure to annihilate its first `2r(K+1)`
moments.

## Proof

The derivative identity

\[
 F^{(k)}(0)=\sum_i c_i\lambda_i^k
\]

shows that `F` and `G` each have analytic order at least `K+1` at the
origin. Analytic order is multiplied by `r` under the `r`th power and is
additive under products. Therefore `F^rG^r` has order at least
`2r(K+1)`, which is equivalent to vanishing of every lower derivative.

## Meaning for the recurrence programme

Tracelessness is only the `K=0` case.  Removing the Krylov carrier
`span{I,H,...,H^K}` supplies `K+1` moment constraints. Growing replicas then
amplify observer invisibility linearly in `r`, precisely in the signed sector
that the positive `Z_r` relaxation erased.

This theorem does **not** yet imply a quenched circuit-union bound. Moment
cancellation must still be converted into quantitative control of the
finite-time spectral kernel for the common-disorder local-Hamiltonian
ensemble. No manuscript may claim that conversion before its separate proof.

## Formal trace

- `formal/GaloisForLFunctions/HTGeometry/KrylovReplicaMomentAmplificationLaw.lean`
- `finiteComplexExponentialAmplitude_analyticAt`
- `iteratedDeriv_finiteComplexExponentialAmplitude_zero`
- `analyticOrderAt_finiteComplexExponentialAmplitude_ge`
- `iteratedDeriv_replicaProduct_zero_of_moment_null`

The owning file passes `lake env lean`. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: exact statement and role frozen
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: Lean proof and axiom audit
- [ ] 3 -> 4: use only after quantitative kernel conversion and novelty audit

## Log

- 2026-08-06 — Proved exact all-order amplification from Krylov moment nullity
  to paired-replica moment nullity.
