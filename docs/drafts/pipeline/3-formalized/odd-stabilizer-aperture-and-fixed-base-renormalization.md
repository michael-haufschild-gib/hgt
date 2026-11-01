# Stabilizer aperture bounds and fixed-base logarithmic cancellation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Finite aperture

For a C⁴ window Ω supported in `[a,b]`, let
`D₄=∫_{a−1}^{b+1}|Ω⁽⁴⁾|` and `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`.
For m>0 and R≥1, the first R positive even-shift terms differ from the
complete stabilizer row by at most

`2 O(Q) D₄ (m/2)⁴/R³`.

The Ramanujan estimate `|c_q(h)|≤φ(q)` gives `|p_Q(h)|≤2O(Q)`.
Fourth-order Fourier decay reduces the omitted terms to a reciprocal fourth
power tail, bounded by R⁻² times the reciprocal square tail R⁻¹.

## Uniformity in the conductor cutoff

At a positive even lag, `|p_Q(2r)|≤32r²`, independently of Q.
Oddness gives `c_q(2r)=c_q(r)`, the divisor formula gives `|c_q(r)|≤r²`,
and `Σ μ²(q)/φ(q)²≤16`. Hence every finite row and the complete row obey

`|row|≤4D₄m⁴`.

Each absolute summand is at most `2D₄m⁴/r²`; the reciprocal-square sum is
at most two.

## Fixed-base spatial renormalization

For fixed m>0, `row_Q(m)/log Q→0`. The exact Poisson identity then gives

`spatialDual_Q(m)/log Q→Ωhat(0)/(2πm)`.

Thus primitive spatial samples cancel the entire leading negative diagonal
at a fixed base. This differs from the proved moving-horizon limit
`row_Q(bQ/π)/log Q→−Ωhat(0)/2`. A horizon estimate cannot be transferred
uniformly to fixed-base rows.

## Lean

`TransThresholdPairCorrelation/OddStabilizerApertureBounds.lean`:
`abs_parityStabilizerWeight_le`, `abs_stabilizerLinearRow_truncation_le`,
`abs_parityStabilizerWeight_even_le`, `abs_stabilizerLinearRow_le`,
`abs_sum_stabilizerLinearRow_le`,
`tendsto_stabilizerLinearRow_fixed_div_log_zero`,
`tendsto_stabilizerSpatialDual_fixed_div_log`.

All seven audits use only standard axioms; the final direct leaf check passes.

## Remaining gap

The [literal logarithmic transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md)
still requires phase, taper and upper-endpoint control. Global model calibration
and the actual signed prime-minus-model estimate remain open.
