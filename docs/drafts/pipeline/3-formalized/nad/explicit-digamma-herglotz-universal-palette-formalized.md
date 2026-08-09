# Explicit digamma Herglotz universal palette — formalized

- **ID:** `explicit-digamma-herglotz-universal-palette-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `explicit-digamma-herglotz-universal-palette.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaHerglotzPalette.lean` | the closed-form source, the palette points, the finite orientation chambers |
| `formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaOrientationLimit.lean` | the infinite signed completion and its Herglotz classification |
| `formal/GaloisForLFunctions/HTGeometry/ExplicitDigammaPaletteIndependence.lean` | joint differential independence of the palette |
| `formal/GaloisForLFunctions/HTGeometry/ShiftedDigammaFamilyIndependence.lean` | the finite pairwise-incongruent shifted-digamma theorem it rests on |
| `formal/GaloisForLFunctions/HTGeometry/UniversalConstraintOrientation.lean`, `.../UniversalOrientedConstraintProduct.lean` | the rational-gauge and Stanley–Reisner consequences |

## Formal theorem chain

1. **The source.**  `explicitDigammaHerglotzSource z = digamma (z + 1/2) + γ`, and
   `explicitDigammaHerglotzSource_im_pos` proves it maps the open upper half-plane strictly into
   itself — the Herglotz law.

2. **The palette.**  `explicitDigammaPalettePoint n = 1/(n+2)`, with
   `explicitDigammaPalettePoint_pos`, `explicitDigammaPalettePoint_le_half`,
   `explicitDigammaPalettePoint_injective` and
   `explicitDigammaPalettePoint_sub_ne_int`: the points lie in `(0, 1/2]`, are pairwise distinct,
   and remain pairwise distinct modulo `ℤ`.  `explicitDigammaPalette_collisionMatroid_eq_free`
   identifies the mathlib collision matroid of the palette with the free matroid.

3. **Finite orientation chambers.**  `explicitDigammaFiniteOrientation_nonneg_iff_empty` — the
   finite chamber is Herglotz exactly at the empty reversal set: reversing one residue destroys
   upper-half-plane positivity.

4. **The Gauss series.**  `summable_norm_gaussDigammaSeriesTerm_all` and
   `tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles` — the reciprocal-difference
   series converges absolutely and sums to the source off the pole lattice;
   `signedDigammaCompletion_one_eq_explicitDigammaHerglotzSource` identifies the all-positive
   completion with the closed-form source.

5. **The infinite orientation.**  `summableLocallyUniformlyOn_signedDigammaRegular`,
   `differentiableOn_signedDigammaCompletion_upperHalf`,
   `signedDigammaBooleanCompletion_eq_regular_sub_atom` and
   `signedDigammaBooleanCompletion_nonneg_iff_allPositive` — every bounded signed completion
   converges compact-locally normally, is holomorphic on the upper half-plane, splits into an atom
   and a regular background, and is Herglotz exactly at the all-positive orientation.

6. **Joint differential independence.**  `DifferentialIndependent.of_finite` — differential
   independence passes from all finite subfamilies to an arbitrary index, because algebraic
   independence does.  `differentialIndependent_digammaShiftMero_general` — an arbitrary family of
   shifted digammas with pairwise integer-incongruent shifts is differentially independent over
   `ℂ(X)` in the global meromorphic differential field.
   `differentialIndependent_explicitDigammaPalette` — the whole countable palette
   `n ↦ ψ(z + 1/(n+2))` is differentially independent, and
   `differentialIndependent_explicitDigammaPalette_fin` is its finite form.

   This is the item the paper card previously left at the cited Hardouin boundary.  It is now an
   unconditional theorem of the corpus: the classical parent is not assumed anywhere.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ExplicitDigammaPaletteIndependence.lean
lake build GaloisForLFunctions.HTGeometry.ExplicitDigammaPaletteIndependence
```

`#print axioms` on `explicitDigammaHerglotzSource_im_pos`,
`explicitDigammaPalettePoint_injective`, `explicitDigammaPalettePoint_sub_ne_int`,
`explicitDigammaPalette_collisionMatroid_eq_free`,
`explicitDigammaFiniteOrientation_nonneg_iff_empty`,
`tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles`,
`signedDigammaCompletion_one_eq_explicitDigammaHerglotzSource`,
`signedDigammaBooleanCompletion_nonneg_iff_allPositive`,
`differentiableOn_signedDigammaBooleanCompletion_upperHalf`,
`differentialIndependent_digammaShiftMero_general` and
`differentialIndependent_explicitDigammaPalette` reports exactly `propext`, `Classical.choice`,
`Quot.sound`.

## Boundary

The formalization covers the construction and its differential independence.  The card's remaining
open gate is a novelty and significance audit of the combined geometry, which is not a
formalization obligation.
