# Prime--Gamma cumulative cofinal universality law

- **ID:** `prime-gamma-cumulative-cofinal-universality-law`
- **Law:** LAW503
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/PrimeGammaCumulativeCofinalUniversalityLaw.lean`

## Theorem

Fix any positive rectangular aperture `L`. For every sufficiently late arithmetic cutoff `N`,
the critical summatory-growth law for the explicit prime--Gamma negative-mass source is equivalent
to the Riemann hypothesis:

```text
eventually N,
  RH iff NonnegativeDirichletSummatoryGrowthAt
    (xiRectangularPrimeGammaTailNegativePart L N) 1.
```

No cutoff witness or per-tail admissibility hypothesis remains.

## Theorem-generated derivation

Whole-corpus same-folder theorem-leaf pairing exposed:

- `riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth`, the exact cumulative
  criterion under a rectangular admissibility premise;
- `eventually_xiRectangularAdmissibleCutoff`, proving that premise for every sufficiently late
  cutoff;
- `eventually_of_xiRectangularAdmissibleCutoff`, the corpus's generic premise-elimination rule.

The cofinal universality module discharges several spectral and thermal criteria, but does not
consume the cumulative negative-mass theorem.

## Dependency-closed paper proof

For fixed `L`, rectangular admissibility holds eventually in `N`. At every such `N`, instantiate
the fixed-cutoff cumulative theorem. Filtering this pointwise implication through the eventual
admissibility set gives the stated eventual equivalence. No numerical computation is used.

## Strict corpus delta

The corpus has fixed-cutoff cumulative RH equivalence and generic cofinal admissibility, but not
their cutoff-free composite. New law places cumulative negative-mass growth on the same cofinal
footing as the existing abscissa, Hausdorff, KMS, and Sonin criteria.

## Lean result

`formal/GaloisForLFunctions/RHTower/PrimeGammaCumulativeCofinalUniversalityLaw.lean`
proves
`eventually_riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/PrimeGammaCumulativeCofinalUniversalityLaw.lean`

The proof derives cofinal admissibility directly from
`exists_xiRectangularAdmissibleCutoff`, avoiding a non-cached module dependency before final
build. The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.

- Classical RH criteria connect zero locations to Chebyshev error growth, and standard Dirichlet
  series theory connects nonnegative coefficient summatory growth to convergence abscissae.
- Searches for a prime--Gamma negative-part source, its cumulative mass, and an eventual
  cutoff-independent RH equivalence found no matching statement. Related Li criteria and
  Chebyshev-bias results concern different coefficient sequences.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`. Novelty is limited to this explicit
prime--Gamma negative-part carrier and uniform cofinal removal of its cutoff premise.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
