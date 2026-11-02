# Exact frequency maximum of the complex Cauchy multiplier

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.

## Exact result

For `Re w>0`, the actual Mellin multiplier on `Re u=Re w/2` is
maximal at `u=w/2`:

```text
|M K_w(w/2+iξ)| ≤ |M K_w(w/2)| < 2^((1−Re w)/2).
```

This extends the central sharp envelope to every Mellin frequency,
and gives strict contraction throughout that frequency line when `Re w≥1`.

## Proof mechanism

Set `g_d(z)=Γ(z+id)Γ(z−id)/Γ(z)^2`. On `Re z=1/2`, reflection gives

```text
|g_d(1/2+iy)|² = cosh(πy)^2/[cosh(πy)^2+sinh(πd)^2] ≤ 1.
```

For `x≥1/2`, the proved vertical Gamma-ratio inequality and the exact
half-line modulus give `Γ(x)^2/|Γ(x+iy)|² ≤ cosh(πy)`.
The Euler integral bounds each numerator by `Γ(x)`, hence
`|g_d(x+iy)|≤cosh(πy)≤exp(π|y|)`. On the positive real axis its norm is
at most one. Half-plane Phragmen–Lindelof therefore gives `|g_d(z)|≤1`
for `Re z≥1/2`. Apply this at `z=(w+2)/4`, `d=ξ/2` to the exact
Cauchy Gamma symbol. All growth and nonvanishing inputs are explicit.

The corpus's existing symmetric-split theorem bounds the Stirling main
term and retains an error for Gamma itself. The exact split inequality removes that
error on `Re z≥1/2`, with no restriction on the imaginary split.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerCauchyFrequencyMaximum.lean`,
namespace `MayerCauchyFrequencyMaximum`: `split_boundary_norm_sq`,
`split_norm_le_cosh`, and `split_norm_le_one` certify the Gamma split.
`symbol_frequency_split`, `norm_mellin_frequency_le`, and
`frequency_norm_isGreatest` identify the attained maximum for the actual
absolutely convergent Mellin integral. `norm_mellin_frequency_lt` and
`frequency_contractive` give the full frequency-line bounds.
All thirteen public results passed the direct production check with only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Boundary

This scalar multiplier theorem does not yet construct a Mayer Hermitian
form or control its scattering boundary terms. The certified amplification
below abscissa one remains.
