# Effective scaling geometry and arithmetic height–homotopy theory

- **ID:** effective-scaling-and-height-homotopy
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMMES
- **Sources:** [review-0611 §2.11](../../../reports/review-0611/obstacles-summary.md),
  [review-0711 §2.11](../../../reports/review-0711/obstacles-summary.md)

## Required mathematical end state

| Programme | Constructions and questions requiring resolution |
|---|---|
| Effective scaling geometry | Actual sections and zero divisors reading primitive classes; irreducible curves and nonnegative intersections; negative-degree vanishing; arithmetic curvature; weighted prime filtration; form-independent window index and winding formula; Hecke generation of the ample cone |
| Height and homotopy of arithmetic counts | Arithmetic probe group and addition; nonnegative local-height sum with product formula; finite-radius torsion regularization and self-energy payment; approximate parallelogram and Tate limit; natural fixed-point localization of the nerve; cusp realization and modular action; polarized quadratic refinement and ample cone |

Both must recover the stated curve calibrations and fail on the named fakes.
They must detect full tests, have infinite rank in the limit, and define their
counts independently of `Q`. The prime-complex theory must retain linear Betti
mass and the square-root lower obstruction. An RH equivalence or a finite rung
does not fulfill these requirements.

## Mathematical development

- [Prime-height filtration](esg-prime-height-filtration.md): explicit coning
  after doubling the height; compatibility and persistence are the precise
  additions sought beyond the known levelwise sphere bouquet.
- [Finite-radius torsion](hhac-finite-radius-torsion.md): separate divergent
  diagonal, universal radial term and inverse-chord remainder. The comparison
  with the archimedean reserve remains an independent open inequality.

The programme definitions are
[EffectiveScalingGeometry/README.md](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/README.md)
and
[HeightHomotopyArithmeticCounts/README.md](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/README.md).
These constructions are first tools within the full specification, not a
replacement completion criterion.

## Proof obligations

Every claimed result needs a dependency-closed paper argument, matching Lean
statement, direct `lake --old env lean <module>` audit, and `#print axioms`.
Each programme has its own directory and sibling umbrella. No umbrella builds,
numerical experiments, assumed analytic inputs or proof placeholders.
