# SEM dyadic Weyl quadratic-irreducibility universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/SEMDyadicWeylDegeneracyLaw.lean`
  - `dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd`
- `RHTower/SEMDyadicWeylQuadraticIncidenceLaw.lean`
  - `boundaryCompletedJetWeyl_implies_zeroWrap_or_quadraticXiIncidence`
- `RHTower/WeylCommonEigenspaceNoGo.lean`
  - `no_dyadicWeyl_common_eigenvector`

## Universal law

Every positive-depth, nonzero-wrap completed SEM boundary Weyl packet simultaneously has dimension
divisible by `2^k`, jet quadratic index and local Xi-order square divisible by `(2^k)^2`, and no
common nonzero character line for its clock and shift generators.

Thus the same packet carrying the quadratic arithmetic selection rule is forced to remain genuinely
multichannel: its Weyl symmetry cannot be isolated on a common scalar eigendirection.

## Paper proof

The exact boundary Weyl classification and nonzero wrap give `2^k | n+1`, hence the dimension lower
bound.  The SEM split identity transports this divisor to the square of the integral jet index and
the square of the local Xi order.  Independently, a positive-depth dyadic Weyl pair has nontrivial
primitive phase, while any shared nonzero eigendirection with nonzero eigenvalues would force phase
one.  Applying this obstruction to the very same truncated clock and boundary shift rules out every
common character line.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/SEMDyadicWeylQuadraticIrreducibilityUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/RHTower/SEMDyadicWeylQuadraticIrreducibilityUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the arithmetic quadratic-incidence selection and common-eigenspace obstruction separately, but no
theorem asserted their joint consequence on one nonsingular completed SEM Weyl packet.
