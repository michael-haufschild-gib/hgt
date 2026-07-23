# Gamma scale-separated affine order-energy universality law

## Status

In progress — paper proof and Lean source complete; exact check deferred until final dependency
audit because `GammaAffinePoleEnergyUniversalityLaw` has no cached object file.

## Theorem-first provenance

- `HTGeometry/GammaPoleScaleSeparatedAffineHorizon.lean`
  - `gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine`
- `HTGeometry/GammaPoleMovingAffineProfileHorizon.lean`
  - `gammaPoleProfileAtMostSimple_iff_affine`
- `RHTower/GammaAffinePoleEnergyUniversalityLaw.lean`
  - `gammaPoleProfileAtMostSimple_simple_iff_boundaryEnergy_unbounded`

## Universal law

Extend a complex-coefficient Gamma source to moving polynomial coefficients by applying
`Polynomial.C` coefficientwise.  If its factorially scale-separated profile has degree at most one,
the extension lies on the moving at-most-simple Gamma horizon.  At every branch, exact simple
meromorphic order is then equivalent to failure of every uniform approaching-line `L²` energy
bound for the canonical derivative coefficient.

Thus the algebraic degree-one scale horizon is a sufficient certificate for a local-to-global
order-energy equivalence after the canonical constant-coefficient change of base.

## Paper proof

The scale-separated affine-horizon theorem writes the source as `C a + C b · X₀`.  Coefficientwise
constant-polynomial extension preserves that form, with coefficients `Polynomial.C a` and
`Polynomial.C b`.  The moving-coefficient affine classification therefore puts the extended source
on the at-most-simple horizon.  The canonical Gamma order-energy theorem then applies branchwise.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/GammaScaleSeparatedAffineOrderEnergyUniversalityLaw.lean`.

The coefficient-extension connector was exact-checked independently against cached
`GammaPoleScaleSeparatedAffineHorizon` and `GammaPoleMovingAffineProfileHorizon` modules.  Full
source check is deferred solely because imported
`GaloisForLFunctions.RHTower.GammaAffinePoleEnergyUniversalityLaw.olean` is absent; no dependency
build was run before final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the scale-separated degree classifier, the moving-coefficient affine classifier, and the
order-energy equivalence separately, but no theorem transporting the first certificate through
constant-polynomial coefficient extension into the branchwise local-global law.
