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

- [Prime-height filtration](../3-formalized/esg-prime-height-filtration.md): explicit coning
  after doubling the height and the exact interval law for actual inclusion
  maps between the known sphere bouquets.
- [Finite-radius torsion](../3-formalized/hhac-finite-radius-torsion.md): separate divergent
  diagonal, universal radial term and inverse-chord remainder. The comparison
  with the archimedean reserve remains an independent open inequality.
- [Conductor control](../3-formalized/hhac-conductor-controlled-regularization.md): bound the
  remainder for arbitrary signed finite pairings by conductors and totients.
- [Exact chord energy](../3-formalized/hhac-torsion-chord-energy.md): sharpen that cost using
  the full root-of-unity energy and the least common multiple of conductors;
  obtain a conductor-uniform modulus for the spacing-regulated diagonal and
  its quadratic form on arbitrary finite supports.

The programme definitions are
[EffectiveScalingGeometry/README.md](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/README.md)
and
[HeightHomotopyArithmeticCounts/README.md](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/README.md).
These constructions are first tools within the full specification, not a
replacement completion criterion.

## Global mathematical gap

`ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_exists_effectivity`
identifies full scaling-surface Riemann–Roch plus ample effectivity with RH.
The existing source-section constructions prove restricted-aperture cases;
their all-aperture mixed-defect payment remains open. The filtration's interval
law does not supply that payment or bound Euler cancellation.

For heights, the spacing regulator has an indefinite renormalized limit.
Controlling its finite-radius error does not construct a nonnegative local-height
sum, an arithmetic addition law, or a fixed-point localization of the nerve.
Those constructions remain required inputs to the two programmes.

## Proof obligations

Every claimed result needs a dependency-closed paper argument, matching Lean
statement, direct `lake --old env lean <module>` audit, and `#print axioms`.
Each programme has its own directory and sibling umbrella. No umbrella builds,
numerical experiments, assumed analytic inputs or proof placeholders.
