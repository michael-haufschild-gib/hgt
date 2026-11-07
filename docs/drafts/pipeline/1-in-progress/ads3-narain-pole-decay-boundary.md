# Arithmetic poles force a scalar decay boundary

- **ID:** W11-NB
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [W11](ads3-scalar-modular-bootstrap.md)
- **Statement:** For every arithmetic resonance `p`, and every pair of
  positive target heights, some pair of horizontal coordinates admits no
  estimate `|yH(y)−a log y−b|≤C y^α` on `(0,1]` whenever
  `α>1/2−Re p`. Here `H` is the actual nonvacuum scalar Narain heat sum;
  `a,b,C` are arbitrary constants. In the zeta variable `ρ=1+2p`, the
  boundary is `α≤1−Re ρ/2`.

## Proof target

The mass gap and Gaussian convergence give local continuity of `H` and
`|H(y)|≤B exp(−cy)` for `y≥1`, with `c>0`. Suppose the displayed remainder
bound holds. Put
`g(y)=H(y)−1_(0,1](y)(a log y+b)/y`.
Then `g=O(y^(α−1))` at zero and decays exponentially at infinity.
Its Mellin transform is holomorphic on `Re s>1−α`.

Write `s=1/2+u`, `w=u−1/2`, `D(u)=ξ(1+2u)`, `c(u)=u(1+2u)`.
The cutoff main term has Mellin transform `−a/w²+b/w` on `Re w>0`.
For each target modulus, define the entire filled numerator

`T(u)=(2u−1)Y^(1/2+u)D(u)+(1+2u)ξ(2u)Y^(1/2−u)`
`       +(2u−1)(1+2u)(2u)Tail(u)`.

Away from `u=1/2`, this is `(2u−1)N(u)`. The actual scalar Mellin identity
therefore gives

`c(u)D(u)[w² Mellin(g)(1/2+u)−a+bw]=T₁(u)T₂(u)/2`.

Both sides are holomorphic on `Re u>1/2−α`; uniqueness extends the identity
from the absolute-convergence half-plane. At `u=p` the left side vanishes.
The proved horocycle detector chooses targets with `N₁(p)N₂(p)≠0`.
Since `2p−1≠0`, the right side is nonzero, a contradiction.

This proves an obstruction to faster decay. It does not prove any
RH-strength remainder estimate. Multiple zeros need no simplicity assumption.

## Lean obligations

- Actual heat continuity, local integrability and exponential large-height bound.
- Cutoff logarithmic Mellin identity and convergence.
- Entire filled numerator and the source identity after clearing the main pole.
- Analytic uniqueness on the decay half-plane and the unconditional obstruction.

## Gates

- [x] 0 → 1: pole location and precise decay exponent identified.
- [ ] 1 → 2: all analytic inputs discharged for the literal source.
- [ ] 2 → 3: direct Lean checks, axiom audit and umbrella imports.
