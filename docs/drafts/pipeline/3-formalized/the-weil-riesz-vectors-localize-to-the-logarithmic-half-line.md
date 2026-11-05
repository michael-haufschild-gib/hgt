# The Weil Riesz vectors localize to the logarithmic half-line

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Both endpoint localizations of every actual precontact Fourier Riesz source are the unique half-line logarithmic Green solutions for their full bounded L² forcings, with exact normalized renewal readouts.

## Proof

Translate the left endpoint to zero. The overlapping cutoff is one up to `a`,
zero from `3a/2`, and has Lipschitz constant `2/a`. A half-line finite-energy
test, multiplied by this cutoff and translated back, belongs to the original
complete aperture domain. The actual Riesz equation, translation invariance
and full cutoff identity therefore give

`q(v,χ_a τ_-a u)=⟨v,P₊(χ_a τ_-a g+Kχ_a τ_-a u)⟩`.

Both actual source and full logarithmic forcing are bounded. The explicit
Schur bound makes the localized forcing bounded and L². Half-line Green
uniqueness identifies the actual localized source. Its normalized limit is
the absolutely convergent renewal integral. Reflection preserves the complete
domain and form, giving the corresponding right endpoint statement. All prime
atoms and both polar terms are retained in the actual forcing.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilRieszVectorsLocalizeToTheLogarithmicHalfLine.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact`.

- `evalVector_leftLocalized_eq_green`
- `evalVector_rightLocalized_eq_green`
- `evalVector_leftLocalized_forcing_bounded`
- `evalVector_rightLocalized_forcing_bounded`
- `evalVector_leftLocalized_normalized_limit`
- `evalVector_rightLocalized_normalized_limit`

Transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
Production plain audit passed. Umbrella imports the module.
The [continuous gluing and actual traces](normalized-boundary-traces-of-weil-riesz-vectors.md)
are also formalized. Aperture variation is not asserted.
