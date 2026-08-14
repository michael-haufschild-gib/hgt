# One-species hypertranscendental elastic saturation — formalized

- **ID:** `one-species-hypertranscendental-elastic-saturation-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `one-species-hypertranscendental-elastic-saturation.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean module

`HTGeometry/ElasticChannelSaturation.lean`.

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- **`mem_of_norm_orthogonalProjectionOnto_eq`**, `orthogonalProjectionOnto_orthogonal_eq_zero_of_compression_norm_eq`, **`mapsTo_of_compression_norm_eq`** — the elastic channel-saturation lemma `(2)`–`(4)`: a compression of norm equal to the full norm forces the vector into the channel subspace, so a saturating scattering operator maps the one-particle channel into itself;
- `geometricCDDCrossingCoordinate_ofReal`, **`norm_geometricCDDStep_ofReal_eq_one`** — every geometric CDD factor has unit modulus on the real rapidity axis, i.e. elastic unitarity of the ladder;
- `sinh_im_eq`, `sinh_ne_neg_I_mul_of_physicalStrip`, **`geometricCDDStep_denom_ne_zero_of_physicalStrip`** — pole-freedom of the physical strip: no bound-state pole is produced by the geometric product.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

## Boundary

The card's three remaining gates are a specialist audit of the particle-spectrum interpretation, a
formula-level novelty audit, and the onward construction of a positive action / operator-flow or
gauge-topological source for the full measure `ν`.  The first two are external literature
obligations; the third is an onward research target the card poses rather than a step of the proved
theorem.  Lechner's inverse-scattering construction and the q-difference rational-or-HT dichotomy
remain cited classical inputs, exposed as hypotheses and never as axioms.
