# Dirichlet depth-two/three zero-transition universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/DirichletDepthTwoThreeZeroTransitionUniversalityLaw.lean`.

## Lean-generated inputs

- `CarrierDepthTwoRigidity.lean`: `dirichletPoly 2` is zero-free for positive real part; completed
  depth-two high strip zeros are critical-line aligned and simple.
- `DepthThreeDirichletHighZeros.lean`: `1 + 2⁻ˢ + 3⁻ˢ` has open-strip zeros at arbitrarily high
  positive heights.

## Survivor

The common finite Dirichlet family has a sharp two-to-three depth transition. Two primes cannot
cancel in the open right half-plane and their completed carrier is asymptotically rigid. Adding the
prime `3` produces recurrent direct-factor cancellation cofinally high in the strip.

## Formal target

`GaloisForLFunctions.RHTower.DirichletDepthTwoThreeZeroTransitionUniversalityLaw`

## Novelty audit

Pending post-formalization literature search.
