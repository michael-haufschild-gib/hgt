# Exact signed Poisson row for odd Ramanujan conductors

- **Stage:** 1-in-progress
- **Type:** CANDIDATE / EXACT SIGNED MODEL
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

For a C² function Ω supported in `[a,b]`, `0<a≤b`, m>0, odd q≥1 and
`qb≤πm`, prove absolute summability and

`2 Σ_{r≥1} c_q(2r) cosTransform Ω(2r/m) = −φ(q) cosTransform Ω 0`.

Finite summation over `q≤floor(πm/b)`, with weights `μ²(q)/φ(q)²`, then
gives the exact negative odd-conductor main term. The cotangent residual
in the current C¹ theorem disappears under C² regularity.

## Stronger finite dual formula

Without the horizon restriction, the same argument should give

`2Σ_{r≥1} c_q(2r) Ωhat(2r/m) + φ(q)Ωhat(0)`
`= πm Σ_{d|q} μ(q/d) Σ_{k∈Z} Ω(kπm/d)`.

The spatial sums are finite by compact support. This identifies the exact
additional terms in rows where a fixed cutoff exceeds the Poisson horizon.
For a prime q and a window meeting `πm/q` but no integer multiple of `πm`,
the correction is positive. The horizon identity is its zero-dual-mode case. Equality at the boundary is allowed because continuity forces Ω(b)=0.

The dual Möbius sum should also equal the primitive spatial sum
`Σ_{n∈Z, gcd(|n|,q)=1} Ω(πmn/q)`. Thus for Ω≥0 every conductor
correction is nonnegative: the negative Ward–Mertens value is a lower
bound, attained exactly when all active primitive samples vanish.
This finite divisor reindexing gives a stronger classification than the
sufficient horizon inequality alone.

A concrete full-packet counterexample is available at `Q=7`, `m=7/π`:
choose smooth `0≤Ω≤1` supported in `[31/32,33/32]` with Ω(1)=1.
The primitive `q=7, n=1` sample contributes `7/36` to the packet
correction; every other primitive contribution is nonnegative. Its negative diagonal is
`−(23/12)∫Ω≥−23/192`, so the complete signed row is at least
`43/576>0`. Such Ω is `u(16τ−31/2)` for a canonical smooth profile u
of collar 1/8. This falsifies negative-row cancellation beyond the sharp
dual horizon; it does not falsify the actual prime-pair conjecture.

## Mechanism

For every divisor d of q, use `RHTower.hasSum_paperFT_lattice` at period
`L=πm/d`. Under `qb≤πm`, the support lies between zero and L;
continuity kills any endpoint value, so every spatial lattice value vanishes. Taking real parts and pairing positive and negative
frequencies gives `2Σ_{r≥1} Ωhat(2dr/m)=−Ωhat(0)`.
The odd-conductor divisor identity
`c_q(2r)=Σ_{d|q,d|r} μ(q/d)d` and
`Σ_{d|q} μ(q/d)d=φ(q)` give the target.

For scaled smooth Ω supported near height T, Fourier decay of order k
bounds a truncation at `r≈mθ` by
`O(m (Tθ)^(1−k) Σ_{q≤Q} μ²(q)/φ(q))`.
This can handle `θ=T^(−1+η)` at fixed bandwidth by choosing k sufficiently
large. The existing one-derivative baseline bound alone loses a power at
this aperture. The corpus already proves `coalescent_term_linearization_bound`, including
the logarithmic phase and square-root pair weight. At bandwidth 4/3,
fourth-order Fourier decay and this quadratic phase error have compatible
power savings at aperture `T^(-5/6)`. Summing those bounds with the actual
taper, aperture, boundary and fixed conductor cutoff still requires transport.

## Logarithmic calibration

At `m=bQ/π`, the sharp horizon is exactly Q. The full signed row equals
`−Ωhat(0) Σ_{q≤Q,odd} μ²(q)/φ(q)`, so division by log Q tends to
`−Ωhat(0)/2` by `tendsto_sum_odd_sqfreeTotientInv_div_log_half`.
This is a precise full linear-row calibration. It does not yet evaluate the
finite logarithmic pair kernel.

## Lean

The lattice Poisson theorem is already formalized; the stated Ramanujan row
and finite-aperture transport are not.
