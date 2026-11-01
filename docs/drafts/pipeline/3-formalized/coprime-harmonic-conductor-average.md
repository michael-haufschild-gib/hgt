# Coprime-harmonic errors have logarithmic conductor cost

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).
- **Lean:** `TransThresholdPairCorrelation/CoprimeHarmonicConductorAverage.lean`.

## Statements

Write `A(q)=μ²(q)/φ(q)²` and `H_q(N)=Σ_{n≤N,(n,q)=1}1/n`.

1. `Σ_{q≥1} A(q)(1+log q)≤576`; the series converges
   (`summable_sqfreeTotientInv_log_div_totient`).
2. For all positive q,N,
   `|H_q(N)−(φ(q)/q)log N|≤Σ_{d|q}(1+log d)/d`
   (`abs_coprimeHarmonic_sub_totient_log_le`). No relation between q and N
   is required.
3. For every Q and arbitrary positive integer horizons N(q),
   `Σ_{q≤Q}qA(q)|H_q(N(q))−(φ(q)/q)log N(q)|≤36864(1+log Q)`
   (`sum_weighted_abs_coprimeHarmonic_sub_totient_log_le`, parametrized by
   N(q)+1 in Lean). Positivity also bounds the odd-conductor subsum.

## Proof

The existing totient-ratio estimate gives
`Σ_{q≤Q}qA(q)≤64(1+log Q)`. Dirichlet-weight Abel summation with exponent
1/2 yields `ΣA(q)sqrt(q)≤192`. Since `1+log q≤3sqrt(q)` for q≥1,
the logarithmic moment is at most 576.

Ordinary floor-harmonic bounds place `H_floor(N/d)−log N` between
`−log d` and 1. Möbius decomposition and `|μ(d)|≤1` give statement 2,
including d>N.

A squarefree product dk has coprime factors, so `A(dk)=A(d)A(k)`;
otherwise A(dk)=0. Thus `A(dk)≤A(d)A(k)` always. Divisor swapping gives

`Σ_{q≤Q}qA(q)Σ_{d|q}(1+log d)/d`
`=Σ_{d≤Q}Σ_{k≤Q/d}kA(dk)(1+log d)`
`≤[Σ_d A(d)(1+log d)]·[Σ_{k≤Q}kA(k)]`
`≤576·64(1+log Q)`.

## Consequence and scope

The arithmetic error remains logarithmic even when each primitive Poisson
sample uses its own horizon `floor(qt/π)`. Weighted taper summation and
odd-base quadrature still need formalization before this supplies the global
model calibration. Actual prime-minus-model discrepancy remains open.

All three transitive axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`; the final direct leaf check passes.
