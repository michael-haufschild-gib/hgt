# Uniform conductor error in the signed odd-stabilizer model

- **Stage:** 1-in-progress
- **Type:** CANDIDATE / SIGNED MODEL ERROR
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

For every integer Q≥0,
`Σ_{q≤Q, q odd} μ²(q)σ₂(q)/φ(q)² ≤64Q`.
At the actual Poisson horizon `Q=floor(m/b)`, this bounds the existing
cotangent residual by `64 cosTransform Ω 0`, independent of m and Q.
It preserves the negative signed main term
`−cosTransform Ω 0 Σ_{q≤Q, q odd} μ²(q)/φ(q)`.

## Proof

Let `g=μ²/φ`, and let `a(q)=1_{q odd} μ²(q)σ₂(q)/φ(q)²`.
Both are multiplicative and nonnegative. At an odd prime p≥3,
`a(p)=1+2p/(p−1)² ≤1+3/(p−1)=(zeta*g*g*g)(p)`.
At p=2 the left side vanishes. At every higher prime power it vanishes
because of μ². Both sides equal one at q=1, so multiplicativity gives
`a≤zeta*g*g*g` on all positive integers.

Finite divisor summation gives
`Σ_{q≤Q}(zeta*g*g*g)(q) ≤ Q Σ_{d≤Q}(g*g*g)(d)/d`.
Nonnegativity and the hyperbola inclusion in the square give
`Σ_{d≤Q}(g*g*g)(d)/d ≤ (Σ_{d≤Q}g(d)/d)³ ≤4³`.
The last bound is `RHTower.Sieve.sum_sqfreeTotientInv_div_le`.

The conductor residual contains the q=1 term explicitly as one. Thus its
entire conductor factor is exactly the sum above, and `Qb≤m` proves
the uniform bound. No prime-pair discrepancy estimate follows from this
model error bound. Logarithmic-phase transport and model main-term
summation remain separate inputs.

## Lean

Formalization pending. No analytic premise is to be added to the model theorem.
