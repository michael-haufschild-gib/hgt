# Hedenmalm canonical orientation singularity carrier

- **ID:** `hedenmalm-canonical-orientation-singularity-carrier`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE CARRIER LAW
- **Scientific status:** `[PROVED] [LEAN] [NOVELTY PROVISIONAL] [BRIDGE CORE]`
  `[NOT AN RH PROOF]`
- **Parent:** `hedenmalm-finite-local-autocorrelation-frame-obstruction.md`

## Claim under attack

For `c=1/2+a`, define the canonical horizontal orientation multiplier

```text
Q_a(b)
  =(xi'/xi)(c+i b)+(xi'/xi)(c-i b).
```

On the real frequency axis it satisfies the exact horizontal-current identity

```text
partial_a |xi(c+i b)|^2=Q_a(b)|xi(c+i b)|^2,
```

including at zeros, where both sides vanish.  For every `a>0`, `Q_a` cannot be entire.  Thus the
orientation carrier forced by the actual Hedenmalm source is not merely required to avoid a finite
local frame: it must retain a non-entire transverse divisor singularity.

More precisely, the nonanalytic set of `Q_a` contains the injective affine-frequency image of the
infinite left boundary of the Xi divisor under translation by `2a`.  At a boundary zero `rho`, the
removable residue germ has exact value

```text
-i ord_rho(xi).
```

Thus the carrier transports both infinitely many divisor locations and their multiplicities.

## Verification labels

- `[PROVED]` The horizontal-current identity for the canonical quotient is elementary after
  separating the zero and nonzero cases.
- `[PROVED]` Entire continuation is impossible by the completed-flux translation obstruction.
- `[PROVED]` The forced singular subset is infinite, and every point has the exact nonzero
  multiplicity residue displayed above.

## Lean obligations

- [x] define the canonical multiplier without a hard proposition interface;
- [x] prove its exact real-axis current law, including zeros;
- [x] prove existence of a nonanalytic point for every positive aperture;
- [x] prove infinitely many translated-divisor boundary singularities;
- [x] identify their residue multiplicities.

## Publication boundary

The generic strip-boundary lemma and the residue calculation are bridges.  The source-specific
combination appears to be a new carrier classification for the 2026 Hedenmalm architecture, but it
still supplies no positivity and therefore remains below the publication threshold for an RH
advance.

## Formal theorem surface

The completed unconditional layer is in
`formal/GaloisForLFunctions/RHTower/HedenmalmCanonicalOrientationMultiplier.lean`:

```text
xiCanonicalHorizontalOrientationMultiplier
xiCanonicalHorizontalOrientationMultiplier_real_law
xiCanonicalHorizontalOrientationMultiplier_unique_on_real
not_differentiable_xiCanonicalHorizontalOrientationMultiplier
exists_not_analyticAt_xiCanonicalHorizontalOrientationMultiplier.
```

The real-axis law is proved at zero and nonzero Xi fibers separately, so no division-by-zero
premise is concealed in the statement.

The infinite support and residue layers are in

```text
formal/GaloisForLFunctions/HTGeometry/TranslatedStripBoundary.lean
formal/GaloisForLFunctions/RHTower/HedenmalmInfiniteOrientationSingularities.lean
formal/GaloisForLFunctions/RHTower/HedenmalmOrientationResidues.lean.
```

Their capstones are

```text
infinite_leftShiftBoundary_of_infinite_in_openUnitStrip
xiCanonicalOrientationSingularSet_infinite
xiCanonicalOrientationBoundaryResidueGerm_eventuallyEq
xiCanonicalOrientationBoundaryResidueGerm_zero
xiCanonicalOrientationBoundary_residue_ne_zero.
```

## Honest significance score

`70--80/100`.  The theorem gives a concrete infinite multiplicity-bearing carrier forced on the
actual Hedenmalm source, but its mechanisms are elementary strip combinatorics, logarithmic
derivatives, and residue germs.  It classifies what orientation must transport; it does not prove
the orientation sign and does not clear the `90/100` paper gate.
