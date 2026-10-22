# Theta-cusp modular cold-curvature universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `RHTower/ThetaCusp/ThetaCuspLikelihoodModularFluctuation.lean`
  - `thetaCuspLikelihoodModularSeam_strictFluctuation`
- `RHTower/PrimeArchThetaGaussianApertureSignedProjectiveCurvature.lean`
  - `thetaCuspGaussianAperture_coldSlope_signFlip`
  - `thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff_pos`

## Universal law

At every cold degree `j`, the signed-corrected Gaussian-aperture slope is the literal first-atom
boundary slope multiplied by a strictly positive half-order Gamma second difference. Consequently
the strict modular likelihood fluctuation inequality transports to every degree:

```text
correctedSlope(j)^2 * (1 + M0)^2
  < (2*pi)^2 * gammaCurvature(j)^2 * M0 * M2.
```

Thus one modular order-two moment cone simultaneously controls the entire all-degree signed cold
projective-curvature hierarchy.

## Paper proof

The exact sign-flip identity replaces the sum of the bad `p=4` slope and signed `p=2` correction by
the first-atom boundary slope. The half-order Gamma second difference is positive in every degree.
Multiply the strict modular-seam fluctuation inequality by its positive square and regroup factors;
the left side becomes the squared corrected cold coefficient.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspModularColdCurvatureUniversalityLaw.lean`.

Direct source check is deferred to final audit because both provenance modules currently lack
cached `.olean` artifacts; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
the modular fluctuation and all-degree signed curvature mechanisms separately but no transported
all-degree curvature–moment cone.
