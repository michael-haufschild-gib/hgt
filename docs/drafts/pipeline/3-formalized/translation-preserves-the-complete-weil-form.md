# Translation preserves the complete Weil form

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Physical translation preserves the complete Weil source quadratic, including both polar coordinates. Before contact it induces an exact Hilbert isometry whenever the translated support fits, with Fourier character `exp(-iz h)`.

## Proof

Translation multiplies the Fourier source by a unit-modulus phase, preserving
the Gamma integral. Commuting translations and unitarity preserve every prime
autocorrelation. The two polar coordinates acquire reciprocal factors
`exp(h/2)` and `exp(-h/2)`; their products cancel in the complete pairing.
The unchanged quadratic gives the Hilbert norm identity. Substitution
`y=x+h` in the entire Fourier integral gives the character `exp(-iz h)`.

## Lean

`CanonicalSystemOfTheWindowTower/TranslationPreservesTheCompleteWeilForm.lean`:

- `completeWeilSourceQuadratic_translate`
- `WeilHilbertBeforeContact.translate`
- `WeilHilbertBeforeContact.physical_translate`
- `WeilHilbertBeforeContact.fourier_translate`

Plain Lean audit passes. All four printed dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.
