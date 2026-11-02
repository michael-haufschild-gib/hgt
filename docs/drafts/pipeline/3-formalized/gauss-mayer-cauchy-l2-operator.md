# Actual Cauchy operator on logarithmic square-integrable fields

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.

## Target

For `Re w>0`, identify the actual logarithmic convolution kernel

```text
k_w(x)=exp(−w x/2) K_w(exp(−x))
```

with its bounded operator on `L²(ℝ)`. Its Fourier multiplier is
`m(w,w/2+2πiξ)`. Prove injectivity and operator norm at most
`|m(w,w/2)|<2^((1−Re w)/2)`, hence strict contraction for `Re w≥1`.
The identification must concern the actual convolution integral.
For the canonical scattering core, also prove that
`g_w(x)=exp(−w x/2) F_w(exp(−x))` belongs to `L²` and the operator
image is exactly the logarithmic profile of the actual Cauchy transform.
The change of variables gives
`∫ℝ |g_w|² = ∫₀∞ a^(Re w−1)|F_w(a)|² da`.
Consequently the actual Cauchy image has finite weighted energy, bounded
by `|m(w,w/2)|²` times the core's weighted energy.

## Proof mechanism

The already proved absolute central Mellin convergence becomes
`k_w∈L¹` under `a=exp(−x)`. The same substitution identifies its Fourier
transform exactly, with the `2π` normalization. The existing convolution
operator theorem transports the actual integral to this multiplier on
`L²`. The certified frequency maximum bounds its norm. The multiplier
never vanishes, so Fourier unitarity and pointwise multiplication give
injectivity.

## Boundary

This proves a norm law for the actual Cauchy averaging operator. It does
not identify that operator with the Mayer transfer operator, classify
all eigenfunctions, or exclude off-line scattering resonances.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerCauchyL2.lean`, namespace
`MayerCauchyL2`: `operator_ae_integral`, `operator_eq_multiplier`,
`operator_norm_le`, `operator_norm_lt`, `operator_contractive`, and
`operator_injective` certify the actual operator. `convolution_logField`,
`core_log_memLp`, `operator_core_ae`, `cauchy_core_energy_integrable`,
and `cauchy_core_energy_le` identify its canonical input and output.
The direct production check passes without warnings; all 18 audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
