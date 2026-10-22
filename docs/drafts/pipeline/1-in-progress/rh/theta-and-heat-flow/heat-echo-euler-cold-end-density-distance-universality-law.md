# Heat-echo Euler cold-end density-distance universality law

Status: source written; exact Lean audit pending.

## Lean sources

- `tendsto_heatApertureEulerMixedMoment_dyadicScaled`
- `eulerColdEndRadialDistance_tendsto`

## Survivor

For every base heat aperture and depth offset, integer heat depth defines one translated Euler
inverse-temperature ray.  On that ray, the dyadically normalized local second Fisher moment tends
`(log 2)^2`; simultaneously, the square-root normalized continuous radial tail beginning at the
same temperature tends `2`.

This joins pointwise ground-mode selection to the geometry of the entire cold tail.  Local metric
density decays to zero while the end remains at finite, sharply normalized distance.

## Proof skeleton

The affine temperature `1 - sigma + q + k` tends to infinity.  Use the mixed heat/Euler moment law
at order two for the local statement and compose the Euler cold-end distance theorem with the same
affine ray for the tail statement.

## Novelty audit

Pending post-formalization literature search.
