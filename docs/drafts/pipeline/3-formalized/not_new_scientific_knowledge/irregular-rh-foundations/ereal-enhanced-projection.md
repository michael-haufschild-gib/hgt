# Proper projection along the extended real compactification

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Topological infrastructure for the enhanced-variable projection.

## Claim

For every topological space `X`, the projection `X × EReal → X` is proper. Therefore inverse image
along this projection defines a functor from compactly supported integer-module sheaves on `X` to
compactly supported integer-module sheaves on `X × EReal`.

## Paper proof

`EReal` is compact. Projection from a product `X × K` onto `X` is proper whenever `K` is compact.
Apply the generic theorem that proper sheaf inverse image preserves stalkwise compact support.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesERealEnhancedProjection.lean` defines:

- `EnhancedCompactification`;
- `enhancedProjection`;
- `enhancedProjection_isProper`;
- `enhancedProjectionPullback`.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesERealEnhancedProjection` pass. Axiom audit of all
four declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- Mathlib compactness of `EReal` and properness of first projection with compact second factor.
- `StokesProperPullbackCompactSupport.properPullback`.
- No analytic, arithmetic, Stokes, or RH hypothesis.

## Hostile audit

- `EReal` supplies the compact ambient line with endpoints `-∞` and `+∞`; this card does not yet
  formalize the bordered-space pair `(Real, EReal)` or quotient away boundary-supported objects.
- Properness would fail for projection along noncompact `Real`; compactification is mathematically
  substantive here.
- This constructs ordinary compact-support pullback, not an ind-, derived-, or enhanced functor.

## Next step

Build functorial ind-extension, then descend its complex-level action to derived categories.
