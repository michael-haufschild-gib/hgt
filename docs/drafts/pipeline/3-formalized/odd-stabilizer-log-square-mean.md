# Logarithmic square moment of the odd stabilizer mass

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Statement

For `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`, the limit is

`Σ_{q≤Q,odd}(μ²(q)/φ(q))log²(Q/q) / log³Q → 1/6`.

This is the arithmetic coefficient of the proposed global signed model after
primitive spatial/diagonal cancellation. It supplies no actual prime-pair
estimate.

## Mechanism

The corpus proves `O(Q)/log Q→1/2`
(`tendsto_sum_odd_sqfreeTotientInv_div_log_half`). Finite Abel summation gives

`Σ_{q≤Q,odd}(μ²(q)/φ(q))log²(Q/q)`
`=2∫_1^Q O(floor t)(log Q−log t)/t dt`.

For every ε>0 the existing limit implies a constant Cε with
`|O(floor t)−(1/2)log t|≤ε log t+Cε` for all t≥1.
Indeed, the integer estimate applies above a fixed threshold, and
`0≤log t−log(floor t)≤log 2`; the finite initial interval is bounded by
monotonicity of O.

The elementary integrals are

`∫_1^Q (log Q−log t)/t dt = log²Q/2`,
`∫_1^Q log t (log Q−log t)/t dt = log³Q/6`.

Hence the difference from `log³Q/6` is at most
`(ε/3)log³Q+Cε log²Q`. Divide by log³Q and let ε tend to zero.

## Status

`TransThresholdPairCorrelation/OddStabilizerLogSquareMean.lean` proves
`oddStabilizerLogSquareMass_eq_integral` and
`tendsto_oddStabilizerLogSquareMass_div_log_cube`. Floor interpolation and
both integral moments are included. Both transitive axiom audits use only
`propext`, `Classical.choice` and `Quot.sound`; the final direct leaf check
passes. Existing ordinary logarithmic mean is reused unchanged.
