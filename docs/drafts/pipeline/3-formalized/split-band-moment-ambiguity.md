# Complementary compressed moments do not force singleton runs

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Lean:** `IncommensurableGaborPinching/SplitBandMomentAmbiguity.lean`

The explicit real six-dimensional projection `E(r,c)` has diagonal `1/2`
and rank three whenever `r²+c²=1/4`. A diagonal involution `D` exchanges
`E` and `I−E` and commutes with `H=diag(−1,1,0,0,0,0)`.
Thus both Hermitian compressions have identical power traces.

The compressed second, third and fourth traces are respectively
`2(1/4−c²)`, `0`, and `2(1/4−c²)²`.
Mixing `(r,c)=(√(1/5),√(1/20))` with weight `5/8` and `(0,1/2)`
with weight `3/8`, then normalizing by rank three, gives exactly
`m₂=1/12`, `m₃=0`, `m₄=1/60`. Yet `I+H` has only four diagonal entries
of multiplicity one. Complementary scalar moments alone therefore do not
force six singleton coordinates.

This is a finite matrix obstruction, not a zeta divisor configuration; it does
not satisfy all the stronger singleton-census inputs used for actual zeta zeros.
The positive survivor is the explicit continuous family of balanced projections,
phase exchange, and complete compressed power-trace symmetry.

Main declarations: `splitBandProjection_rank`,
`splitBand_complementary_trace_pow`, `splitBandCompression_trace_pow`,
`splitBand_actual_mixture_second_fourth`, `splitBandSource_singleton_coordinates`.
The source passes `lake --old env lean`; these declarations use only
`propext`, `Classical.choice`, `Quot.sound`.
