# Halving descent and the exact Shimura obstruction

- **Stage:** 3-formalized
- **Module:** `ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros.lean`.
- **Namespace:** `GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HalvingPairs`.

## Statements

If RH fails, some zero ρ satisfies `1/2 < Re ρ < 1` and `ζ(ρ/2) ≠ 0`.
Any halving pair forces the global zero abscissa Θ to satisfy `Θ ≥ 2/3`.
For a nonzero Hecke cusp eigenform with its Fourier expansion and nonzero
first coefficient, RH is equivalent to both:

- its energy has decay `O(y^(3/4−ε))` for every `ε > 0`;
- no nonhalving right zero ρ also annihilates its Shimura integral at `ρ/4+1/4`.

The latter point lies in `3/8 < Re w < 1/2`. This identifies the remaining
analytic obstruction; it neither proves Shimura nonvanishing nor excludes
all halving pairs.

## Proof

If every right zero were halved, reflection after halving would produce zeros
converging to `2/3`, contradicting the nonzero zeta value there. For one
halving pair, `Re ρ ≤ Θ` and `1−Re ρ/2 ≤ Θ` give `Θ ≥ 2/3`.
Sharp energy decay forces the diagonal transform to vanish at each right
resonance. The Hecke diagonal factorization, applied to the nonhalving
witness, then forces its Shimura factor to vanish. Conversely, RH gives
sharp decay for every cusp-form energy and excludes every right witness.

## Lean verification

Direct `lake --old env lean` check exited 0. Six audited declarations:
`exists_right_zero_not_halved`, `two_thirds_le_abscissa_of_halving_pair`,
`sharpEnergyRate_of_riemannHypothesis`, `pairing_half_eq_zero_of_sharp_rate`,
`sharp_rate_forces_shimura_zero`,
`riemannHypothesis_iff_sharp_rate_and_no_shimura_obstruction`.
All transitive axiom reports contain only `propext`, `Classical.choice`,
`Quot.sound`. Imported by the owning umbrella.
