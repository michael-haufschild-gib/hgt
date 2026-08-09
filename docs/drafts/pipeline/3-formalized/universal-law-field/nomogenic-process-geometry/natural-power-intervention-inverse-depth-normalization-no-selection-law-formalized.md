# Natural power intervention and inverse-depth no-selection law — Lean certification

- **ID:** ULF-NPG-PIN-1
- **Paper card:**
  `natural-power-intervention-inverse-depth-normalization-no-selection-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveNaturalPowerNormalization`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

`naturalMultisetEndomorphism_classification` proves that every monoid endomorphism of finite
multisets natural under every carrier map is uniquely uniform multiplicity scaling.

`ramificationNatural_iff` classifies rational comparisons from raw weight-one ramification
transport to normalized transport as exactly scalar multiples of inverse depth.
`constant_ramificationNatural_iff_zero` proves a depth-independent comparison is natural exactly
when it vanishes. `inverseDepth_preserves_radial` proves canonical inverse-depth normalization
preserves every raw radial parameter.

The capstone
`naturalPowerIntervention_inverseDepthNormalization_noSelection` bundles the classification,
normalization loophole, fixed-frame rigidity, and radial no-selection theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveNaturalPowerNormalization.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveNaturalPowerNormalization
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed. No theorem premise, `sorry`, new axiom, computation certificate, opaque proof,
or unsafe declaration is used.

## Exact field consequence

Full source naturality reduces all free-commutative-monoid interventions to uniform powers, but
power coherence does not select a radial origin: inverse-depth normalization is the unique
nonzero comparison family and preserves every radial parameter. Any live selector must introduce
additional source structure that destroys this normalization freedom.
