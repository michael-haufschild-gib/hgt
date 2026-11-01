# Logarithmic square moment of the odd stabilizer mass

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

For `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`, prove

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

Paper mechanism identified; Abel identity, floor interpolation, integral
moments and limit transfer await Lean formalization. Existing ordinary
logarithmic mean is reused unchanged.
