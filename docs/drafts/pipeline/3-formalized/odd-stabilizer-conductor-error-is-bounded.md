# Uniform conductor error in the signed odd-stabilizer model

- **Stage:** 3-formalized
- **Type:** THEOREM / SIGNED MODEL ERROR
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

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

## Logarithmic main term

Let `F(Q)=Σ_{q≤Q} μ²(q)/φ(q)` and O(Q) be the odd-conductor sum.
The exact parity identity gives `F(Q)≤2O(Q)≤F(2Q)`. The corpus theorem
`F(Q)/log Q→1` and `log(2Q)/log Q→1` therefore give `O(Q)/log Q→1/2`.
The conductor error above is bounded while this signed main coefficient grows
logarithmically. Endpoint and finite-aperture errors remain explicit.

## Lean

`TransThresholdPairCorrelation/OddStabilizerPoissonHorizon.lean` proves:

- `sum_odd_sqfree_sigma2_totient_sq_le`;
- `poissonHorizon_conductor_error_le`;
- `abs_dynamic_poissonHorizon_row_add_le`;
- `tendsto_sum_odd_sqfreeTotientInv_div_log_half`.

All four transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. The exact production leaf passes `lake --old env lean`;
its umbrella import is present.

## Remaining

This estimates rows at `Q=floor(m/b)`. The literal model fixes Q across rows.
Its additional dual terms and actual logarithmic-phase transport remain open.
The [exact C² Poisson row](../1-in-progress/exact-poisson-row-for-the-odd-stabilizer.md)
would sharpen the horizon and remove the cotangent error.
