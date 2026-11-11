# Three consequences of a zero half-plane

- **ID:** A113
- **Stage:** 3-formalized
- **Lean:** `SelectiveArithmetic/TheHalfPlaneGivesTheThreeRungs.lean`

## Statement

Under `Θ≤b`:

- Centred contacts `Λ(n)−1` give bounded-shape positivity at every positive
  rung `κ` satisfying `(2b−1)κ<1`.
- Dressed positivity holds on all sufficiently large primes at each level
  `b+1/2+ε`, `ε>0`.
- Heavy prime-orbit returns require `log t≥c y^(1−b)` for some `c>0`,
  above fixed height and support thresholds.

## Proof

The centred partial sum is `ψ(n)−n+1`. The zero-abscissa bound on the
Chebyshev remainder gives cancellation exponent `γ` for every
`γ>Θ−1/2`. Choose `b−1/2<γ<1/(2κ)` and apply the cancellation margin.

For the dressed form use `e=min(ε,1)` and half-plane depth
`α=b−1/2+ε−e`. The existing half-plane producer gives level
`1+α+e=b+1/2+ε` once `log X≥1/e+1`.

Reflection of the zero divisor gives depth at most `b−1/2`.
The heavy-return strip theorem then gives exponent
`1/2−(b−1/2)=1−b`.

Lean declarations: `centred_prime_rung_of_halfPlane`,
`large_prime_level_of_halfPlane`, `heavy_return_bound_of_halfPlane`.
Direct Lean check passed; module imported by `SelectiveArithmetic.lean`.
