# FZZ-P Hermitian chiral orientation classification — 2026-08-28

## Result

For the literal all-scale FZZ parity conjugate Krein eigenvectors and the full Hermitian quadratic
family `[[a,b+ic],[b-ic,d]]`, the exact value gap is

`-4 * fzzKreinQAt beta * c * sqrt(fzzCigarParityDilatedTwoScaleKreinDiscriminant beta)`.

At `beta>0`, equality holds iff `c=0`; inequality iff `c≠0`; gap negative iff `c>0`; gap positive
iff `c<0`.  Every real-symmetric reporter is blind at every real scale.  Unit imaginary
off-diagonal reporter is strictly oriented at every positive scale.

## Route consequence

FZZ-P no longer needs an unspecified “interacting/off-diagonal Hermitian” producer.  Required
source-native dynamics must generate nonzero imaginary off-diagonal (`i sigma_y`-type) compression
and then land Xi divisor modes into the classified eigenlines.  Diagonal and real-symmetric fixed
quadratic reporters are terminally dead.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/FZZCigarParityHermitianChiralOrientationClassification.lean`
- formalized card: `docs/drafts/pipeline/3-formalized/fzz-p-hermitian-chiral-orientation-classification.md`
- failed-route card: `docs/drafts/pipeline/5-failed/fzz-p-real-symmetric-hermitian-orientation-no-go.md`
- umbrella wired: `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- direct `lake env lean`: passed
- targeted `lake build GaloisForLFunctions.RHTower.FZZCigarParityHermitianChiralOrientationClassification`: passed
- main theorem axioms: only `propext`, `Classical.choice`, `Quot.sound`
- global lint failure remained limited to unrelated pre-existing unreachable modules
- frontier map untouched

## Novelty audit

Mandatory corpus searches found related CCM chiral operators but no FZZ-specific Hermitian
classification.  Primary literature checked FZZ duality/scattering/spectral asymmetry and general
Krein theory; no exact source-specific collision located.  Do not claim absolute priority.
