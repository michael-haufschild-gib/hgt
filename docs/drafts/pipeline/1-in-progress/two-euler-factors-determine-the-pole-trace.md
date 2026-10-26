# Two Euler factors determine the pole trace

- **ID:** adr-two-euler-factors
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean in progress
- **Statement:** For `0 < ε < 1/2`, `α = 1 − ε` and a row `w` with `w(0) = 0`: the rows
  `w − 2^α D₂w` and `w − 3^α D₃w` both have bounded pronic energy iff `w − c n^α` has bounded pronic
  energy for some (unique) `c`. One prime does not suffice: `n^α cos(2π log₂ n)` passes the 2-law.

## Goal
A domain-free form of the renormalized inversion law: applied to `w = Sv` (total cofactor sum) the
two trace-free eta laws are equivalent to `Sv − c n^α` admitted, and `c` is the pole trace. The
single-prime law leaves exactly the 2-adic ghosts `n^α Π({log₂ n})`.

## Approach
Log scale `g(u) = e^{−u/2} w(⌊e^u⌋)`: pronic energy = `∫ g²`, `D_p` = `p^{1/2}` × shift by `ln p`.
Law at `p`: `g − λ_p g(· − ln p) ∈ L²`, `λ_p = e^{κ ln p}`, `κ = 1/2 − ε`. Anti-causal series
`S_p = Σ_{i≥1} λ_p^{−i} f_p(· + i ln p) ∈ L²`, and `π_p = e^{−κu}(g + S_p)` is a.e. `ln p`-periodic.
Two primes: `e^{κu}(π₂ − π₃) ∈ L²`; shifting by `ln 2` leaves a `ln 3`-periodic function in
`L²(0, ∞)`, hence zero; so `π₃` has periods `ln 2, ln 3`, constant by ergodicity of the irrational
rotation; same for `π₂`; equal constants since `e^{κu} ∉ L²`.

## Log
- 2026-10-26: card opened; Lean module `TwoEulerFactorsDetermineThePoleTrace`.
