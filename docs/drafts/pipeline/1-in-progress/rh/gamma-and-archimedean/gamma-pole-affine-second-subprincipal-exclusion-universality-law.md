# Gamma pole affine/second-subprincipal exclusion universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/GammaPoleScaleSeparatedAffineHorizon.lean`
  - `gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine`
- `HTGeometry/GammaPoleWeightedSecondSubprincipalCofinal.lean`
  - `gammaPoleSecondSubprincipalBoundarySymbol_ne_zero_iff_channels`
  - `exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal_channels`

## Universal law

Every source whose actual factorially scaled Gamma pole profile has degree at most one is affine in
its undifferentiated carrier.  Such a source has zero first-jet and zero Hessian
second-subprincipal channels.  With the first partial cancelled, its complete second-subprincipal
boundary must vanish.

Conversely, any surviving complete second-subprincipal boundary forces actual pole-profile degree
at least two.  Intrinsic channel survival therefore gives both nonlinear source complexity and an
arbitrarily remote common Gamma branch carrying the exact second-subprincipal meromorphic order in
the covariant and native packets.

## Paper proof

Use the affine-horizon equivalence to write the source as `a + b X₀`.  Its derivative in coordinate
one and its second derivative in coordinate zero vanish.  The exact channel classification then
annihilates the boundary whenever the first partial is cancelled.  Contraposition gives the degree
lower bound.  Combine this lower bound with the existing cofinal exact-order theorem.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/GammaPoleAffineSecondSubprincipalExclusionUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/GammaPoleAffineSecondSubprincipalExclusionUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the actual affine pole-profile horizon and the cofinal second-subprincipal channel classification
separately, but no theorem proving their mutual exclusion or coupling nonlinear degree with exact
cofinal order.
