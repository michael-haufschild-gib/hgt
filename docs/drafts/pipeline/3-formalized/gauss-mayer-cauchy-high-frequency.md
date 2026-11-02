# Sharp high-frequency Cauchy multiplier threshold

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [exact multiplier](gauss-mayer-cauchy-mellin-symbol.md).
- **Lean:** `RenormalizedIntersectionTheory/GaussMayerCauchyHighFrequency.lean`, namespace `MayerCauchyHighFrequency`.

## Exact result

For every fixed `σ>0` and `−1<α<σ+1`,

```text
|M K_(σ+iτ)(α+iτ/2)| → 2^((1−σ)/2)  as τ→+∞.
```

These are absolutely convergent Mellin integrals of the actual normalized
Cauchy kernel. The limit is independent of the fixed real Mellin weight.

- `0<σ<1`: the modulus exceeds one at all sufficiently large heights.
- `σ=1`: the limiting modulus is exactly one.
- `σ>1`: this frequency family is eventually strictly contractive.

For every `0<σ<1`, admissible `α`, and real cutoff `T`, there exists
`τ>T` with an absolutely convergent actual Mellin integral of modulus
greater than one. This includes every fixed abscissa in the right half
of the source critical strip.

## Proof

Gamma duplication gives

```text
m(w,u) = 2^((1−w)/2) Γ((u+1)/2) Γ((w+1−u)/2)
         / [Γ((w+1)/4) Γ((w+3)/4)].
```

At the stated parameters, all four Gamma arguments have imaginary part
`τ/4`, positive real parts, and equal sums between numerator and
denominator. The proved vertical Gamma-shift ratios from
`HTGeometry/GammaShiftRatioGeneral.lean`, applied with a common base,
have powers that cancel exactly. The balanced Gamma quotient tends to
one. The prefactor's modulus is exactly `2^((1−σ)/2)`. Identification with
the actual integral and absolute convergence follow from `HasMellin`.

## Lean certificate

`symbol_duplication`, `norm_symbol_vertical`, `tendsto_norm_symbol`,
`vertical_hasMellin`, `tendsto_norm_mellin`, `eventually_amplifying`,
`eventually_contractive`, `tendsto_norm_mellin_one`, and
`exists_amplifying_above` passed the direct production check. All nine
have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Consequence and positive survivor

No fixed real Mellin weight restores uniform Cauchy multiplier contraction
on any fixed source line `0<σ<1`. The exact asymptotic threshold, its
weight independence, and the [strict real squared-energy identity](gauss-mayer-real-cauchy-contraction.md)
remain positive results. This closes a specific scalar contraction
candidate, not the Mayer Hermitian-form or spectral-gap problem.
