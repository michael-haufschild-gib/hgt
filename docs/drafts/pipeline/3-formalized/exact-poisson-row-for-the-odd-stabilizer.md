# Exact Poisson rows, primitive samples and the support horizon

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Exact signed identity

For compactly supported C² Ω, m>0 and odd q,

`2 Σ_{r≥1} c_q(2r) Ωhat(2r/m) + φ(q)Ωhat(0)`
`= πm Σ_{n∈Z, gcd(|n|,q)=1} Ω(πmn/q)`.

The Fourier series converges absolutely. Poisson summation at periods
`πm/d`, followed by the divisor formula for c_q and Möbius inversion,
gives the identity. The spatial sum has finite support.

Consequently, the full parity-stabilizer row at any fixed cutoff Q equals
`πm Σ_{q≤Q,odd} μ²(q)/φ(q)² Σ_{n primitive mod q} Ω(πmn/q)`
minus `Ωhat(0) Σ_{q≤Q,odd} μ²(q)/φ(q)`.
For Ω≥0, the negative diagonal is a lower bound. Equality holds exactly
when every primitive sample at an active squarefree odd conductor vanishes.

## Sharp horizon and logarithmic coefficient

If Ω is supported in `[a,b]`, `0<a≤b`, and `Qb≤πm`, every spatial sample
vanishes. Continuity includes the endpoint `Qb=πm`. The complete row is
exactly the negative diagonal.
At `m=bQ/π`, its quotient by log Q tends to `−Ωhat(0)/2`.
This uses the proved odd reciprocal-totient logarithmic mean.

## Positive fixed-cutoff obstruction

Choose smooth `0≤Ω≤1`, supported in `[31/32,33/32]`, with Ω(1)=1.
At Q=7 and m=7/π, the primitive sample n=1 contributes at least 7/36.
All other spatial contributions are nonnegative. Since
`∫Ω≤1/16` and `Σ_{q≤7,odd} μ²(q)/φ(q)=23/12`, the complete row is
at least `43/576>0`. Every sufficiently long finite row is at least
`43/1152>0`. The profile is obtained from an existing smooth bump by an
affine change of variable. Any smaller positive support radius retains the
same lower bound, so positive rows occur arbitrarily close beyond the horizon. See the [failed shortcut](../5-failed/fixed-cutoff-negative-row-cancellation.md).

## Lean

`TransThresholdPairCorrelation/OddStabilizerExactPoisson.lean`:
`ramanujan_evenShift_hasSum_dual`, `ramanujanSpatialDual_eq_primitive`,
`stabilizerLinearRow_eq_neg_of_horizon`, `stabilizerLinearRow_eq_neg_iff`.

`TransThresholdPairCorrelation/OddStabilizerPoissonCalibration.lean`:
`tendsto_stabilizerLinearRow_horizon_div_log`,
`exists_positive_stabilizerLinearRow`,
`exists_eventually_positive_finite_stabilizerRow`.

All sixteen public theorem audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both leaves pass final direct checks and are wired into TTPC.

## Remaining source gap

These are complete linear rows and their finite truncations. Evaluation of
the literal logarithmic pair kernel still needs the
[aperture and boundary transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md).
A fixed Q retains the explicit nonnegative spatial correction. Neither that
transport nor a model evaluation supplies the actual signed prime-minus-model
discrepancy bound needed for 75%.
