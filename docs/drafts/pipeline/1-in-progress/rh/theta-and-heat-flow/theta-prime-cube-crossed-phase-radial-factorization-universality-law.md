# Theta prime-cube crossed-phase radial-factorization universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/ThetaPrimeCubeRadialMomentLaw.lean`
  - `sum_finiteSinePolynomial_thetaFactorPairLogDisplacement`
  - `coeff_sum_finiteCosinePolynomial_primeCube_two_mul`
- `RHTower/XiCTaylorThetaTailProductFiberCrossedTranslation.lean`
  - `finitePositiveNegativeCrossedTranslationPacket`
  - `finiteNegativePositiveCrossedTranslationPacket`

## Universal law

For every prime cube, finite Taylor cutoff, and phase, arithmetic reflection factors both crossed
translation channels through one common finite radial cosine polynomial.  The two channels retain
only opposite external phase factors.  Every even coefficient of the common factor is exactly the
sum of two outer-radius and two inner-radius moments at displacements `3 log(p)/2` and `log(p)/2`.

Thus prime-cube arithmetic reflection is a rank-one phase factorization with an exact two-radius
radial law, rather than merely two separate sine-cancellation and cosine-moment statements.

## Paper proof

Expand each crossed packet into its finite cosine part plus or minus `i` times its finite sine part,
then factor out the phase polynomial independent of the factor pair.  Reflection pairs every
positive logarithmic displacement with its negative, so the total sine polynomial vanishes.  Both
crossed sums therefore share the same remaining cosine sum and differ only in the external phase.
At `p^3`, the factor-pair displacements are the two signed outer radii and two signed inner radii;
the existing coefficient theorem gives the stated even coefficient formula.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/ThetaPrimeCubeCrossedPhaseRadialFactorizationUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/RHTower/ThetaPrimeCubeCrossedPhaseRadialFactorizationUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search exposed
reflection cancellation, prime-cube radial moments, and crossed phase packets on separate theorem
surfaces, but no theorem factorized both crossed families through one explicit common two-radius
radial polynomial.
