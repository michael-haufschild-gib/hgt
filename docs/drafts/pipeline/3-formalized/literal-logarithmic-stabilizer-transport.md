# Literal logarithmic stabilizer rows retain the primitive spatial correction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Finite aperture transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md).

## Exact target and error

Write `p_Q(h)=parityStabilizerWeight Q h`, `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`,
and

`L_Q(m,R)=Σ_{r=1}^R p_Q(2r) Ωhat(log(1+2r/m))/sqrt(m(m+2r))`.

For a compact C⁴ window supported in `[a,b]`, let `M₀=∫|Ω|`,
`M₁=∫|tΩ|`, `D₄=∫|Ω⁽⁴⁾|`, and `D₁=∫|(tΩ)⁽⁴⁾|`, over `[a−1,b+1]`.
At any reference height T>0 put

`C_T=4(M₁/T²+16T²D₁)+2(M₀/T+T³D₄)`.

For `1≤R` and `2R≤m`,

`|L_Q(m,R)−[π spatialDual_Q(m)−Ωhat(0)O(Q)/m]|`
`≤O(Q)C_T/T+O(Q)D₄m³/(8R³)`.

The first error transports logarithmic phase and square-root pair weight;
the second completes the linear row. The primitive correction remains explicit.

## Taper and short rows

For every R with `2R≤m`,

`Σ_{r=1}^R |p_Q(2r) log(1+2r/m) Ωhat(log(1+2r/m))/sqrt(m(m+2r))|`
`≤4O(Q)(M₀/T+16T³D₄)/T`,

and `|L_Q(m,R)|≤O(Q)[4(M₀/T+T³D₄)+C_T/T]`.

The first bound pays the difference of a linear taper at the two endpoints.
The second is uniform in m, including short rows. Both follow by summing
reciprocal-square Fourier envelopes on the positive even-shift lattice.

## Fixed smooth profiles

For every fixed `WindowProfile ε u`, there is a constant C≥0 such that, for
`Ω_T(t)=u((t−T)/T)^4`, T≥1 and `2R≤m`,

- `|L_Q(m,R)|≤C O(Q)`;
- the absolute logarithmic first moment is at most `C O(Q)/T`;
- for R≥1, the signed dual error is at most
  `C O(Q)[1/T+(m/(TR))³]`.

No derivative estimate is left as a premise. Compact support bounds the
fourth derivatives of `u⁴` and `κ(v)=v u(v−1)^4`. The identity
`tΩ_T(t)=Tκ(t/T)` supplies their height scaling. Explicitly,
`C_T≤42+6M₄+192Mκ` for their respective derivative suprema.

## Lean

`TransThresholdPairCorrelation/OddStabilizerLogarithmicTransport.lean`:
`abs_stabilizerLogarithmicRow_sub_linear_le`,
`abs_stabilizerLogarithmicRow_sub_dual_le`,
`sum_abs_stabilizerLogarithmicMoment_le`, `abs_stabilizerLogarithmicRow_le`.

`TransThresholdPairCorrelation/SmoothProfileLogarithmicTransport.lean`:
`WindowProfile.exists_logarithmicTransportBound_le`,
`WindowProfile.exists_stabilizerLogarithmicRow_dual_error_le`,
`WindowProfile.exists_abs_stabilizerLogarithmicRow_le`,
`WindowProfile.exists_stabilizerLogarithmicMoment_le`.

All eight audits use only standard axioms; both final direct leaf checks pass.

## Remaining gap

The literal ordered pair sum still needs exact aperture reindexing, upper
boundary control and global summation of the primitive correction. The actual
signed prime-minus-model discrepancy remains unproved.
