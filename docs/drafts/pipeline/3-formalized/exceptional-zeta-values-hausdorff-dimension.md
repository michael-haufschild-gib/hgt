# Hausdorff dimension of nonrepelling zeta values

- **ID:** exceptional-zeta-values-hausdorff-dimension
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** walls-ledger Γ49
- **Statement:** The set of values `a ∈ ℂ` for which no constants `κ>0`, `D∈ℕ` give `|s′−s|≥κ/(2+|Im s|)^D` for all distinct `a`-points with `0≤Re s≤1`, `|Im s|≥3`, has Hausdorff dimension at most one. In particular this bounds the existing residual exceptional set.

## Paper proof

For a holomorphic function of polynomial growth `A(2+|t|)^B`, the dyadic close-pair cover at separation `2^{-k}` and height cap `2^{⌊k/D⌋}` has at most `C·2^{2k+k/D}` discs, each of radius at most `C′·2^{-2k+Bk/D}`. For every `s>1`, choose integer `D` with `(2D-B)s>2D+1`. Explicitly, put `ℓ=log 2`, `u=2ℓ+ℓ/D`, `v=2ℓ−Bℓ/D`. The grid cardinality is at most `3(β−α+4)e^{uk}` and the radius at most `2000A3^B e^{-vk}`. Choosing `D>(sB+1)/(2(s−1))` gives `u−sv<0`, so the sum of the `s`th powers of cover diameters converges geometrically. Hausdorff covering bounds make the limsup `s`-null. Avoiding that limsup gives polynomial separation with exponent `D`, by the existing dyadic midpoint argument. Zeta's proved strip growth discharges all analytic inputs.

The bound controls the exceptional set's metric size; it does not decide whether `a=0` belongs to it. A dimension-zero bound would require more than the present quadratic grid cover.

## Lean

Module: `formal/GaloisForLFunctions/ArithmeticDiscreteness/TheExceptionalValuesHaveSmallHausdorffDimension.lean`.

- `hausdorffMeasure_nonrepellingValues_eq_zero`: every Hausdorff measure of dimension `s>1` vanishes on the full set of nonrepelling values for a holomorphic function of polynomial strip growth.
- `dimH_zetaNonrepellingValues_le_one`: the unconditional bound for ζ, with the strip-growth input proved in the corpus.
- `dimH_exceptional_values_of_riemannZeta_le_one`: the bound for the existing residual exponential-pair subset.

The full nonrepelling set and its residual exponential-pair subset are distinguished; no equality between them is asserted. Existing area-zero and residual theorems alone do not imply this Hausdorff bound.

Audit: `lake --old env lean GaloisForLFunctions/ArithmeticDiscreteness/TheExceptionalValuesHaveSmallHausdorffDimension.lean` passed. Both public zeta conclusions depend only on `propext`, `Classical.choice`, and `Quot.sound`.
