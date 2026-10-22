# Homogeneous multiple elliptic-Gamma log-derivative reflection universality law

## Status

Formalized in Lean and wired into the HTGeometry umbrella. Kept in progress until global
exhaustion and final audit complete.

## Lean sources

- `GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGamma`
- `GaloisForLFunctions.HTGeometry.MultipleEllipticGammaProduct`
- `GaloisForLFunctions.HTGeometry.MultipleEllipticGammaInversion`
- `GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence`

## Conjecture

Restoring the base period turns the normalized multiple elliptic-Gamma logarithmic derivative
into a homogeneous covector: simultaneous nonzero scaling of every period and the argument
multiplies the logarithmic derivative by the inverse scale.

At the same time, reflection through the physical period sum acts on this homogeneous
logarithmic derivative by the parity sign `(-1)^rank`. Thus value-level scale invariance,
infinitesimal radial Ward rigidity, parity reflection, and rank-three-minor
hypertranscendence all live on one homogeneous carrier.

## Corpus gap

The homogeneous carrier module proves value-level scale invariance and its zero radial Ward
derivative. The normalized inversion module proves parity reflection of the normalized
logarithmic derivative. No theorem transports the logarithmic derivative through the restored
base-period chart, proves its scale weight, or states physical-period reflection for that
homogeneous logarithmic derivative.

## Proof plan

1. Prove global differentiability of the normalized product from its forward/backward products.
2. Apply `logDeriv_comp` to the affine normalization `z ↦ z / ω₀`.
3. Compare the normalized coordinates before and after common nonzero scaling to obtain weight
   `−1`.
4. Rewrite the physical reflected coordinate as the normalized reflected coordinate and apply
   the existing normalized parity law.
5. Combine the new covariance/reflection laws with the existing rank-three-minor
   hypertranscendence theorem.

No numerical computation is used.

## Novelty status

Post-proof searches found Narukawa's modular/integral theory of multiple elliptic-Gamma
functions, ordinary elliptic-Gamma reflection identities, and work on differential algebraicity
of multiple elliptic-Gamma logarithmic derivatives. No searched source stated the exact restored
base-period weight-minus-one law together with physical-period parity reflection and the
rank-three-minor hypertranscendence hypothesis. Novelty claim is restricted to this exact
formal package.

## Lean result

`formal/GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`
proves:

- differentiability of the parity-dependent normalized product on its regular locus;
- exact base-period chain-rule transport of the logarithmic derivative;
- inverse-scale covariance under common period/argument scaling;
- physical-period parity reflection;
- the joint hypertranscendence/scale/reflection capstone.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/HTGeometry/HomogeneousMultipleEllipticGammaLogDerivativeReflectionUniversalityLaw.lean`
