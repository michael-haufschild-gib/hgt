# Möbius off-diagonal analytic-source universality law

## Status

Paper proof complete. Lean source written; exact typecheck awaits final dependency-aware module
build because terminal additive-triangle universality modules have no cached `.olean`.

## Theorem-first source

- `mobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound_implies_triangleLinearPolylogUpperBound`:
  strict off-diagonal binary Möbius correlation control absorbs the explicit diagonal and gives
  the full additive-triangle bound.
- `mobiusAdditiveTriangleLinearPolylogUpperBound_implies_sourceUniversalCertificate`: the triangle
  bound supplies one retained half-polylog source, RH, reciprocal-square realization, multiplicity
  cap, and sharp maximal-order coefficient cap.
- `mobiusAdditiveTriangleLinearPolylogUpperBound_implies_subpowerMultiplicityCertificate`: the same
  triangle bound supplies every strict half-power decay, analytic Mellin continuation on the right
  half-plane, and the continuation wall.
- `mobiusAdditiveTriangleLinearUpperBound_implies_sourceUniversalCertificate`: at degree zero the
  source strengthens to the complete Hedenmalm RH--simplicity phase and simple-zero coefficient
  law.

The off-diagonal frontier, retained-source, and Mellin-wall branches were terminal separately.

## Universal law

A one-sided degree-`2q` polylogarithmic upper bound on strict off-diagonal additive Möbius pairs
simultaneously realizes the retained degree-`q` Laplace source, RH, reciprocal-square source phase,
critical-line multiplicity and maximal-order coefficient caps, all strict half-power estimates,
right-half-plane Mellin continuation, and its exact wall.  At `q = 0`, the same hypothesis also
forces the full Hedenmalm RH--simplicity certificate and sharp simple-zero coefficient law.

## Paper proof

Use the exact diagonal/off-diagonal decomposition and the uniform diagonal bound to pass from the
strict pair estimate to the full additive triangle.  Apply both terminal triangle consumers to
the same resulting hypothesis and retain the source witnesses from the first.  At degree zero,
the logarithmic factor is one, so the degree-zero triangle hypothesis is the linear triangle
hypothesis; apply the simplicity source theorem in addition.

## Lean formalization

- Module: `GaloisForLFunctions.RHTower.MobiusOffDiagonalAnalyticSourceUniversalityLaw`
- General theorem:
  `RHTower.mobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound_implies_analyticSourceCertificate`
- Degree-zero theorem:
  `RHTower.mobiusAdditiveStrictOffDiagonalLinearUpperBound_implies_simplicityAnalyticSource`
- Development check attempted:
  `lake env lean GaloisForLFunctions/RHTower/MobiusOffDiagonalAnalyticSourceUniversalityLaw.lean`
- Current blocker: missing cached object
  `GaloisForLFunctions/RHTower/MobiusAdditiveTrianglePolylogUniversalityLaw.olean` before
  typechecking begins. Dependency construction is reserved for final `lake build <module>` audit.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
