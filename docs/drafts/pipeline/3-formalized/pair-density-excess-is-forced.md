# A diagonal atom forces excess pair density

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Positivity ceiling](fable-route-closures.md).

## Statement

Let `g∈L¹(ℝ)∩L²(ℝ)` be real, `g≤1`, and
`ĝ(α)=A−|α|` for `|α|≤1`, with Fourier phase `exp(−2πiαx)`.
The proposed total pair measure is `Aδ₀+(1−g)dx`.
Writing `g₋=max(−g,0)`, its excess density satisfies

```
∫ (g₋²+g₋) ≥ 2A²−3A+2/3.
```

In particular, `A≥13/10` forces this integral to be at least `11/75`.
The shortcut `0≤g≤1`, which would make `A−ĝ≥0` automatic, cannot reach
that mass: it forces `A≤(3+√(11/3))/4`.

## Argument

The value at frequency zero gives `∫g=A`. Parseval and restriction to
`[-1,1]` give `∫g²≥2(A²−A+1/3)`. Pointwise,

```
g²−g = (g₋²+g₋) − g₊(1−g₊).
```

The last term is nonnegative because `g≤1`. The positive survivor is a
quantitative necessary excess above pair density one, not only exclusion
of nonnegative deficits.

## Lean

`TransThresholdPairCorrelation/ADiagonalAtomForcesExcessPairDensity.lean`:

- `deficit_energy_ge_of_fourier_band`: the Parseval lower bound.
- `pairDensityExcess_ge_of_fourier_band`: the general excess bound.
- `pairDensityExcess_ge_eleven_seventy_fifths`: the `11/75` consequence.
- `diagonalMass_le_of_nonnegative_deficit`: the explicit mass ceiling.
- `no_nonnegative_deficit_at_seventy_percent`: unconditional exclusion of
  the proposed nonnegative-deficit class; square integrability follows from
  integrability and `0≤g≤1`.

Direct `lake --old env lean` check passed; module imported by the umbrella.

This does not exclude signed deficits or settle the all-bandwidth problem.
