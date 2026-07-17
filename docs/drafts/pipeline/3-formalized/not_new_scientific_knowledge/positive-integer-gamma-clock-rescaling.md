# Positive-integer Gamma clock rescaling

- **ID:** `positive-integer-gamma-clock-rescaling`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Gauss multiplication formula; D. Birmingham, I. Sachs, S. N. Solodukhin, *Conformal Field Theory Interpretation of Black Hole Quasi-normal Modes*, arXiv:hep-th/0112055, equations (2), (7), and (8)
- **Statement:** Every finite signed family of genuine meromorphic clocks `Gamma(n_i*z+a_i)` and `Gamma(-n_i*z+b_i)`, with positive natural scales `n_i`, is exactly a nonzero differentially algebraic Gauss gauge times a unit-scale oriented Gamma product; DA and HT classification are preserved and reflected by this reduction.

## Goal

Close the positive-integer clock-rescaling interface needed to reduce commensurable thermal,
scattering, and black-hole Gamma scales to the existing common-scale orbit classifier.  The result
concerns the observability function after clock calibration, not a law of temporal evolution.

## Gates

- [x] 0 → 1 in-progress: exact Gauss reduction and target meromorphic interface identified
- [x] 1 → 2 fully-proven: analytic and meromorphic factorization proved without open hypotheses
- [x] 2 → 3 formalized: Lean module `GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale`
- [ ] 3 → 4 publication-ready: not a standalone novelty claim

## Formal result

`formal/GaloisForLFunctions/HTGeometry/MeromorphicGammaNatScale.lean` proves:

- `reciprocalGammaNatScaleAnalytic_gauss` — the exact analytic Gauss factorization;
- `gammaNatScaleMero_gauss` — the same identity in the genuine global meromorphic field;
- `hypertranscendentalOver_gammaNatScaleGaussProductMero` — the refined shifts are automatically
  separated modulo integer translation, so no nonresonance hypothesis remains;
- `differentialAlgebraicOver_gammaNatScaleGaussGaugeMero` — the constant-exponential factor is DA;
- `hypertranscendentalOver_gammaNatScaleMero` — unconditional HT for every `n > 0` and `a`;
- `gammaNatScaleMero_add_one` — exact scaled parameter recurrence
  `Gamma(nz+a+1)=(nz+a)Gamma(nz+a)` with its rational factor proved nonzero;
- `gammaNatScaleFamilyMero_normalForm` — simultaneous reduction of an arbitrary finite signed
  positive-integer-scale family to one nonzero DA gauge times a unit-scale refined product;
- `differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_refined` and
  `hypertranscendentalOver_gammaNatScaleFamilyMero_iff_refined` — exact transfer of both DA and HT
  classification to the refined product, with no cancellation information lost in the gauges;
- `reciprocalGammaNegativeNatScaleAnalytic_gauss` and `gammaNegativeNatScaleMero_gauss` — the
  negative-orientation analogues for `Gamma(-n*z+b)`;
- `gammaNatScaleMero_one` and `gammaNegativeNatScaleMero_one` — exact bridges from the natural-scale
  API back to the pre-existing unit-scale positive and negative Gamma elements;
- `gammaOrientedNatScaleFamilyMero_normalForm` — simultaneous refinement of arbitrary positive and
  negative integer orientations;
- `differentialAlgebraicOver_gammaOrientedNatScaleFamilyMero_iff_refined` and
  `hypertranscendentalOver_gammaOrientedNatScaleFamilyMero_iff_refined` — exact DA/HT transfer for
  the complete oriented family used by thermal response formulas.

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Corpus value

`ArgumentScalingInvariance.lean` already proves at the actual-function level that
`Gamma(c*z+d)` is HT for every nonzero complex `c`.  Therefore the HT conclusion of this card is
not a new single-factor result and must not be advertised as one.

The added corpus value is the stronger structural interface needed by products: positive integer
rescaling is now an equality inside the genuine global meromorphic differential field, expanding
the scaled factor into a finite common-scale orbit plus a certified nonzero DA gauge.  The existing
actual-function scaling theorem does not provide that normal form or connect a scaled factor to the
meromorphic orbit-charge classifier.  This module therefore discharges the Gauss scale-reduction
hypothesis for finite signed positive commensurable Gamma families and proves that every DA/HT
question is equivalent to the corresponding question for the resulting unit-scale refined product.
The same statement now includes negative clock orientations.  The remaining cross-sector work is
only orbit consolidation and charge evaluation.

`DimensionalRegularizationGammaBoundary.lean` is the first direct QFT consumer.  It reduces the
massless bubble and one-mass triangle kernels, each containing a scale-two negative Gamma factor,
to one half-shift orbit.  Each kernel is HT, while their quotient is DA because the residual shifts
differ by one integer.  Thus the scale-normalization interface now supports an actual
cross-observable cancellation theorem, not only reduction plumbing.

Two further direct consumers now use the same interface.  The Sauter strong-field QED in/out
coefficient has a `2:1:1` Gamma carrier whose complete DA exceptional set is the two possible
matchings of its denominator orbits with the Gauss half- and unit-shift numerator orbits.
The symmetric `K`-category Dirichlet normalizer used in evidential AI and genomic count models is
DA exactly for `K=1` and HT for every `K>1`; its nonzero fractional Gauss orbits cannot all cancel
against `Gamma(z)^K`.

The circular beta-ensemble Selberg partition normalizer is a fourth direct consumer.  The scaled
parameter recurrence proves that it is exactly the symmetric Dirichlet normalizer times
`Kz/z^K`.  Their quotient is therefore DA although both factors are HT for `K>1`, and the full
Dirichlet category-count boundary transfers to the random-matrix coupling clock.

For rotating BTZ observables, it handles the complete `+omega/T` and `-omega/T` Gamma family after
a common frequency normalization whenever the left/right inverse-temperature ratio is rational.
The complete DA/HT verdict still needs cross-sector orbit-charge consolidation after refinement;
incommensurable temperature ratios remain open.

## RH pressure test

The theorem applies to archimedean Gamma factors and can prevent a finite commensurable rescaling
from hiding their HT content.  It does not create a prime source, a zero-free region, or a sign/
positivity statement, so it does not by itself advance an RH implication.  Its RH value is as a
normalization and cancellation audit for future completed-function identities.

## Verification

- targeted cached module build: PASS;
- direct touched-file Lean check: PASS;
- forbidden-token scan: PASS;
- theorem axiom audit: PASS with standard axioms only.

## Log

- 2026-07-17 — exact Gauss gauge factorization, automatic orbit separation, and unconditional
  positive-integer rescaling theorem formalized.
- 2026-07-17 — unit-scale bridges added and used to formalize the dimensional-regularization
  bubble/triangle HT and common-orbit quotient cancellation law.
- 2026-07-17 — the Sauter `2:1:1` QED boundary and the symmetric multiclass Dirichlet
  normalizer dichotomy were added as mixed-scale consumers.
- 2026-07-17 — the scaled additive-parameter recurrence and circular beta-ensemble/Dirichlet
  rational quotient were formalized and verified.
