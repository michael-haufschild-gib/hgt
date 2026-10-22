# Gamma affine/second-subprincipal phase-separation universality law

## Status

In progress — paper proof and Lean source complete; exact source check deferred until final parent
build; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/GammaPoleAffineSecondSubprincipalExclusionUniversalityLaw.lean`
  - `gammaPoleSecondSubprincipalBoundarySymbol_eq_zero_of_affineProfile`
  - `two_le_gammaScaleSeparatedSimplePoleProfileEval_natDegree_of_secondSubprincipal`
  - `exists_cofinal_gammaPoleSecondSubprincipal_nonlinearProfile_exactOrder`
- `RHTower/GammaScaleSeparatedAffineOrderEnergyUniversalityLaw.lean`
  - `gammaScaleSeparatedAffineHorizon_orderEnergyUniversality`

## Universal law

For one weighted scale-separated Gamma source with cancelled principal and first-partial channels,
the affine simple-pole order--energy phase and nonlinear second-subprincipal phase are disjoint.
Affine profile forces complete boundary-symbol vanishing and exact moving-pole order/energy
equivalence at every branch.  Any surviving complete second-subprincipal boundary forces profile
degree at least two and exact second-subprincipal order on arbitrarily remote native and covariant
Gamma branches.

## Paper proof

Degree at most one is equivalent to an affine actual Gamma profile.  Its first-jet and Hessian
second-subprincipal channels vanish, so the complete boundary symbol vanishes; constant-polynomial
extension simultaneously enters the moving at-most-simple horizon and its order/energy theorem.
Conversely a nonzero complete boundary symbol exposes a surviving intrinsic channel, which forces
degree at least two and feeds the existing cofinal exact-order construction.  Boundary vanishing
and nonvanishing make overlap impossible.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/GammaAffineSecondSubprincipalPhaseSeparationUniversalityLaw.lean`.

Full exact check is deferred because its new Law-190 parent currently has no cached `.olean`; no
dependency build was run before final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the affine order--energy transport and nonlinear second-subprincipal exclusion on separate theorem
surfaces, but no theorem stated their sharp phase separation for one Gamma source.
