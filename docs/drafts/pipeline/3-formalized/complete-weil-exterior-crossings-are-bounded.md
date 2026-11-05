# Complete Weil exterior crossings are bounded in physical L²

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The complete Weil pairing between an old aperture source and either exterior source is bounded by `(2π+‖B_b‖)‖u‖₂‖v‖₂`. The same bound holds between sources on opposite half-lines.

## Proof

Translate each exterior source into positive-half-line coordinates; reflect
for the left side. Zero extension reconstructs every source with the stated
support. The exact Gamma crossing is minus its boundary-transfer pairing,
whose operator norm is at most `2π`. The complete bounded remainder `B_b`
retains the scalar, finite-prime, and polar terms. Cauchy–Schwarz bounds its
pairing by `‖B_b‖‖u‖₂‖v‖₂`. Translation and reflection preserve physical L²
norms. The same argument at the origin treats opposite half-lines.

## Lean

`CanonicalSystemOfTheWindowTower/TheWeilFormHasBoundedExteriorCrossings.lean`:

- `rightExterior_reconstruction`, `leftExterior_reconstruction`
- `ccmWeilForm_rightExterior_pair`, `ccmWeilForm_leftExterior_pair`
- `norm_ccmWeilForm_rightExterior_of_supported`
- `norm_ccmWeilForm_leftExterior_of_supported`
- `ccmWeilForm_oppositeHalfLines_pair`
- `norm_ccmWeilForm_oppositeHalfLines_of_supported`

Plain Lean audit passes. Printed main dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.
