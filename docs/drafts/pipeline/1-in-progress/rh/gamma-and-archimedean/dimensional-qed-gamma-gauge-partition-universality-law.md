# Dimensional/QED Gamma gauge-partition universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/DimensionalRegularizationGammaBoundary.lean`
  - `masslessBubbleGammaMero_normalForm`
  - `masslessTriangleGammaMero_normalForm`
  - nonzero and DA gauge theorems
- `HTGeometry/ConstantFieldQEDGammaClock.lean`
  - literal scalar/spinor half/unit-shift carriers
  - `constantMagneticSpinorQEDGammaCarrierMero_ne_da_mul_scalar`
- `HTGeometry/FiniteDifferentialCircuitBoundary.lean`
  - DA multiplicative and inverse closure

## Universal law

Nonzero multiplicative differential-algebraic gauges define an equivalence relation on observables.
For the exact Gamma carriers in this corpus, the dimensionally regulated bubble, dimensionally
regulated triangle, and scalar constant-field QED determinant form one equivalence class.  The
spinor constant-field QED determinant belongs to none of those three equivalent presentations.

Thus one half-shift orbit unifies scalar QED with two dimensionally regulated one-loop kernels,
while the Landau-level half-orbit separation excludes spinor QED from the entire class, not merely
from the scalar representative.

## Paper proof

The triangle normal form contains the scalar-QED carrier literally.  The bubble normal form differs
from it by the integer-shift Veneziano ratio at `(-1/2,1)`, which is nonzero and DA.  Reflexivity,
symmetry, and transitivity of nonzero DA multiplication follow from closure under products and
inverses.  The existing scalar/spinor no-gauge theorem excludes spinor QED from the scalar
representative; transitivity then excludes it from the bubble and triangle representatives.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/DimensionalQEDGammaGaugePartitionUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/DimensionalQEDGammaGaugePartitionUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the bubble/triangle common-orbit law and scalar/spinor QED separation separately, but no equivalence
relation or four-carrier gauge partition joining dimensional regularization to constant-field QED.
