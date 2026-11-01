# Exact signed Poisson row for odd Ramanujan conductors

- **Stage:** 0-backlog
- **Type:** CANDIDATE / EXACT SIGNED MODEL
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

For a C² function Ω supported in `[a,b]`, `0<a≤b`, m>0, odd q≥1 and
`qb≤m`, prove absolute summability and

`2 Σ_{r≥1} c_q(2r) cosTransform Ω(2r/m) = −φ(q) cosTransform Ω 0`.

Finite summation over `q≤floor(m/b)`, with weights `μ²(q)/φ(q)²`, then
gives the exact negative odd-conductor main term. The cotangent residual
in the current C¹ theorem disappears under C² regularity.

## Mechanism

For every divisor d of q, use `RHTower.hasSum_paperFT_lattice` at period
`L=πm/d`. The support lies strictly between zero and L, so every spatial
lattice value vanishes. Taking real parts and pairing positive and negative
frequencies gives `2Σ_{r≥1} Ωhat(2dr/m)=−Ωhat(0)`.
The odd-conductor divisor identity
`c_q(2r)=Σ_{d|q,d|r} μ(q/d)d` and
`Σ_{d|q} μ(q/d)d=φ(q)` give the target.

For scaled smooth Ω supported near height T, Fourier decay of order k
bounds a truncation at `r≈mθ` by
`O(m (Tθ)^(1−k) Σ_{q≤Q} μ²(q)/φ(q))`.
This can handle `θ=T^(−1+η)` at fixed bandwidth by choosing k sufficiently
large. The existing one-derivative baseline bound alone loses a power at
this aperture. Actual logarithmic phase, pair weights, and row-dependent
versus fixed conductor cutoffs still require transport.

## Lean

The lattice Poisson theorem is already formalized; the stated Ramanujan row
and finite-aperture transport are not.
