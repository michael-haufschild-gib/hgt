# Homogeneous multiple elliptic-Gamma scale/reflection universality law

## Status

Law 247; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `HTGeometry/HomogeneousMultipleEllipticGamma.lean`
- `HTGeometry/MultipleEllipticGammaReflectionHypertranscendenceUniversalityLaw.lean`

## Theorem-first derivation

The first source restores a base period `ω₀` and proves invariance under simultaneous nonzero
scaling of `ω₀`, every displayed period, and the argument. The second proves parity reflection and
rank-three-minor hypertranscendence for the normalized ratios `ωᵢ / ω₀`. They meet on the exact
identity

`(∑ i, ω i - z) / ω₀ = ∑ i, (ω i / ω₀) - z / ω₀`.

## Universal law

For every finite period family whose normalized ratios lie in the upper half-plane and contain a
rank-three minor, the product and logarithmic derivative are hypertranscendental over `ℂ(z)`. In
the restored homogeneous chart, every common nonzero rescaling commutes with parity reflection
through the physical center `∑ i, ω i`: even rank gives the inverse and odd rank fixes the value.
Both the direct and reflected common-scale orbits have zero derivative at identity scale.

## Paper proof

1. Apply the existing rank-three-minor theorem to `τ i = ω i / ω₀` for the two
   hypertranscendence conclusions.
2. Cancel the common scale `c` using homogeneous scale invariance on both the direct and reflected
   arguments.
3. Distribute division by `ω₀` across the finite sum and subtraction. This converts reflection
   about `∑ωᵢ` into normalized reflection about `∑τᵢ`.
4. Apply the parity reflection theorem.
5. Apply the homogeneous scale-orbit derivative theorem separately at `z` and `∑ωᵢ - z`.

No numerical pre-certification applies: proof is an exact algebraic normalization and theorem
composition, with no numerical claim.

## Lean target

- Module: `GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGammaScaleReflectionUniversalityLaw`
- Capstone: `GaloisForLFunctions.homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality`
- Exact check: `lake env lean GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaScaleReflectionUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
