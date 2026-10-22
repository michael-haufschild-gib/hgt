# Infinite-volume l-bit Hilbert dynamics

- **ID:** `infinite-volume-lbit-hilbert-dynamics`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-08-17
- **Statement:** For every Borel measure on the infinite Boolean configuration space, the bounded real quasi-local l-bit energy defines a bounded self-adjoint multiplication Hamiltonian on (L^2), whose exponential phases form a strongly continuous one-parameter unitary group.

## Goal

Replace the current Banach-space phase evolution by standard Hilbert-space Schrödinger dynamics.

## Gates

- [x] 0 → 1: exact target and multiplier infrastructure identified
- [ ] 1 → 2: complete paper proof
- [ ] 2 → 3: Lean theorem `quasiLocalInfiniteLBitHilbertDynamicsLaw`
- [ ] 3 → 4: publication integration

## Approach

Continuity of the bounded real energy gives measurability. Bounded multiplication on
(L^2(\Omega,\mu)) is self-adjoint by the exact inner-product identity. Multiplication by
(e^{-itE}) has unit modulus, inverse (t\mapsto-t), the group law, and preserves norm. Dominated
convergence, implemented through the existing bounded-multiplier continuity theorem, gives strong
continuity of every orbit.

## Log

- 2026-08-17 — created in Stage 1 from explicit limitation of the existing Banach evolution card.

