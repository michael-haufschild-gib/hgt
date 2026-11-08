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
- [Mixed spacing convergence](../3-formalized/hhac-weighted-mixed-spacing-convergence.md):
  exact primitive-energy divisor formula, uniform power control of the full mixed
  error on finite positively weighted unit balls, and absolute convergence of
  the error for infinite probes of finite weighted square mass.
- [Weighted torsion completion](../3-formalized/hhac-weighted-torsion-form-completion.md):
  actual symmetric forms on an infinite-rank Hilbert carrier, absolute pair
  series, raw positivity, exact scalar counterterm and operator-norm convergence
  with a power rate for every positive conductor weight.
- [Mixed spacing prime row](../5-failed/hhac-mixed-spacing-prime-row.md):
  no uniform unweighted ℓ² bound; square summability holds exactly for positive
  conductor weights, and the weighted squared error tends to zero.
- [Isolated-prime obstruction](../5-failed/hhac-isolated-prime-fixed-points.md):
  literal square-root-sized fixed sets are impossible for identity-homotopic
  maps. The positive survivor is the exact component classification, connected
  core bouquet and prime-count correction to its Euler characteristic, all formalized.
- [Dirichlet persistence](../3-formalized/esg-dirichlet-persistence-equivalence.md):
  actual augmented cutoff complexes and homology persistence functors;
  natural conjugacy of every complex Dirichlet weighting to the unweighted system.
- [Cycle-height structure](../3-formalized/esg-cycle-height-structure.md):
  natural odd coordinates for cycles and the exact identity that boundaries
  at `N` are cycles at `⌊N/2⌋`, over every commutative ring.
- [Critical coordinate persistence](../3-formalized/esg-critical-coordinate-persistence.md):
  split projection with exact half-cutoff kernel and natural survival maps.
- [Arithmetic homology barcode](../3-formalized/esg-prime-homology-coordinates.md):
  actual augmented homology is naturally the odd-squarefree intervals `[m,2m)`,
  in exterior degree `ω(m)`, over every commutative ring.
- [Integral chain coefficients](../3-formalized/esg-integral-chain-coefficients.md):
  canonical chain and homology maps, with natural tensor base change over every
  commutative ring and explicit cycle representatives.
- [Integral prime persistence](../3-formalized/esg-integral-prime-persistence.md): the natural barcode
  commutes with canonical coefficient extension at every odd-squarefree label.
- [Prime-weighted contraction](../3-formalized/esg-prime-weighted-contraction.md):
  actual nullhomotopy after tripling height, with a sharp augmented obstruction
  to doubling over the integers.
- [Sharp weighted torsion exponent](../3-formalized/esg-prime-weighted-torsion-exponent.md):
  exact boundary saturation, torsion in actual homology killed by two, and a nonzero
  order-two class at height two.
- [Integral weighted cycle coordinates](../3-formalized/esg-prime-weighted-cycle-coordinates.md):
  height-preserving inverse maps and a natural integral basis on bounded odd faces.
- [Integral weighted boundary lattice](../3-formalized/esg-prime-weighted-boundary-lattice.md):
  exact augmented relations from low odd chains, doubled half-height chains,
  and half-height faces containing three; joint free/parity projection is
  surjective with exactly that kernel.
- [Weighted torsion classification](../3-formalized/esg-prime-weighted-torsion-classification.md):
  actual integral arithmetic persistence with free-to-parity reduction;
  the canonical free quotient has no natural section already in empty degree.

- [Two-prime normal form](../3-formalized/esg-two-prime-weighted-normal-form.md): the actual
  weighted chain and homology persistence over every commutative ring is
  naturally isomorphic to the two-prime differential; the comparison preserves
  height and canonical integral coefficient extension. Actual core/tag block
  coordinates have row `(2,3)` and column `(-3,2)`, naturally in height.
  [Arbitrary-coefficient homology](esg-all-coefficient-weighted-homology.md)
  remains in progress.

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
sum, an arithmetic addition law, or signed fixed-point localization of the nerve.
The literal small-fixed-set version is refuted by isolated primes; a replacement
must retain the proved core/component correction and establish cancellation.
The other constructions remain required inputs to the two programmes.

## Proof obligations

Every claimed result needs a dependency-closed paper argument, matching Lean
statement, direct `lake --old env lean <module>` audit, and `#print axioms`.
Each programme has its own directory and sibling umbrella. No umbrella builds,
numerical experiments, assumed analytic inputs or proof placeholders.
