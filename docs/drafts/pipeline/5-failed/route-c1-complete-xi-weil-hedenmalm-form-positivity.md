# RETIRED SUBROUTE: Route C1 continuous full-source Hilbert-Gram positivity

- **ID:** `route-c1-complete-xi-weil-hedenmalm-form-positivity`
- **Stage:** 5-failed
- **Scope:** continuous full-Schwartz source forms and ordinary-`L²` Hilbert-Gram realizations only
- **Verdict:** `[SUBROUTE RETIRED] [FULL-SOURCE CLASSIFIED] [CLOSED-GRAPH NO-GO]`
- **Formalized survivor:** singular real-Xi-divisor Fourier rigging with dense nonclosed radical
- **Live successor:** source-defined singular Burnol--Hedenmalm boundary-null completion, owned by Route C1
- **Lean status:** unconditional full-source subroute boundary formalized

## Retired claim

Construct a nonnegative completed Xi-Weil/Hedenmalm form on the full admissible source test class
and use its symmetric spectral coordinate to prove RH.

## Why this subroute is no longer open

Two exhaustive results meet at the former open core.

First, on the unrestricted Xi-Weil square-summable test class,

```text
complete nonnegativity <-> RH.
```

Every nonreal functional-equation orbit supplies an explicit finite-support negative sign test,
and normalized two-pole Cauchy packets recover those tests.  Therefore “prove the complete form is
positive” is the RH endpoint, not an upstream source lemma.

Second, the natural full-source Hedenmalm category is completely classified.  Every jointly
Schwartz-continuous nonnegative form which symmetrizes momentum and kills the completed theta
source has one unique positive temperate Fourier measure, supported atomically on the real Xi
divisor.  If nonzero, its ordinary-`L²` radical image is dense, proper, and nonclosed, and the form
is not sequentially closable through ordinary `L²`.

The final possible regular escape was a Hilbert Gram map

```text
Q(u,v)=<Jv,Ju>,   J(k)=0,
```

on the full Schwartz source core.  The closed-graph theorem now proves unconditionally:

```text
leftRadical(Q)=ker J,
ker J != Ck,
every partial L² operator realizing J on the full core is nonclosable.
```

Thus neither a faithful quotient by only the common source nor a closed/closable singular graph
exists in the full-source Hilbert-Gram category.

## Exact boundary

Hedenmalm's parent paper defines the candidate form only on the finite span of zero
eigenfunctions.  A discontinuous form or a completion whose domain is restricted to that target
span is not contradicted by the full-source theorem.  But it must prove that every divided-zero
mode survives and that the centered coordinate is symmetric.  Existing formal closure theorems
show:

```text
first-level faithfulness + symmetry <-> zero reality,
second-level faithfulness + symmetry -> zero simplicity,
conservativity of the divisor metric <-> RH + simplicity.
```

That remaining target-domain assertion is already RH-bearing, but it is not thereby proved or
retired.  A Burnol/Sonin construction acting before Hilbert scalarization could still derive it
from source data while genuinely leaving the full Schwartz Gram category.  Because no other
frontier route owns that exact construction, it remains the open survivor of Route C1.

## No-go subroute closure

The regular full-source subroute is closed by the following partition:

1. **Full Xi-Weil tests:** positivity is exactly RH.
2. **Continuous full Schwartz source forms:** uniquely real-divisor atomic and semidefinite.
3. **Faithful full-source Hilbert quotient:** impossible; its kernel cannot be only `Ck`.
4. **Ordinary-`L²` closed or closable Gram graph:** impossible unless the form is zero.
5. **Finite zero-span/discontinuous boundary form:** not refuted.  Its missing source construction,
   faithfulness, and symmetry form the open Route-C1 survivor.

No unresolved regularity or representation lemma remains inside this failed full-source
subcategory.  Route C1 remains open at the singular boundary-null construction recorded in
`../1-in-progress/burnol-hedenmalm-boundary-null-graph-completion-rh.md`.

## Formalized positive survivor of the no-go

The obstruction exposes a rigid positive object rather than only a negation:

> Every nonzero continuous positive pair-symmetric theta-null source form is a unique singular
> Fourier-sampling rigging on the real Xi divisor.  Its ordinary-`L²` radical is dense, proper, and
> nonclosed; every ordinary-`L²` graph realization is nonclosable; and its exact eigenprofile
> sampling detects real simple zeros through the weights `c_gamma |Xi'(gamma)|²`.

This survivor is useful as a classification and falsification theorem.  It is not an RH proof:
off-real eigenprofiles lie in its radical, and source-derived conservativity is precisely the
RH-and-simplicity-bearing clause.

## Live route-level survivor

Construct, before enumerating the Xi divisor, a positive singular boundary form on a completed
Burnol Sonine/co-Poisson carrier which kills the common source, is faithful on every first divided
vector, retains second divided levels, and makes centered coordinate multiplication symmetric and
graph-closed there.  The full-source no-go forces this object to be discontinuous or
boundary-generated relative to ordinary `L²`; it does not exclude it.  This is Route C1's exact
open core.

## Paper and Lean trace

- `../3-formalized/new_scientific_knowledge/hedenmalm-source-hilbert-gram-closed-graph-no-go.md`
- `../3-formalized/hedenmalm-divisor-metric-dense-radical-no-go.md`
- `../3-formalized/not_new_scientific_knowledge/xi-weil-full-square-summable-positivity-criterion.md`
- `../5-failed/hedenmalm-divided-chain-symmetric-carrier-law.md`
- `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmUniversalPositiveFormClassification.lean`
- `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean`
- `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmSourceHilbertGramClosedGraphNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/XiDivisorSupportedMetric.lean`
- `formal/GaloisForLFunctions/RHTower/XiWeilPositivityCriterion.lean`
- `formal/GaloisForLFunctions/RHTower/XiHedenmalmSymmetricMultiplicity.lean`

Headline declarations:

```text
riemannHypothesis_iff_xiWeilPolarization_nonneg
universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor
universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw
not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical
hilbertGram_leftRadical_eq_ker
hilbertGram_kernel_ne_thetaSourceLine
hilbertGram_l2PartialOperator_not_closable
hilbertGram_nonzero_thetaNull_temperedDenseRadicalLaw
xiThetaMetricConservative_iff_mass_pos_and_simple
symmetric_xiSourceQuotient_implies_rh_and_simple
```

## Literature boundary

Hedenmalm's 16 June 2026 v1 preprint constructs the theta boundary-value eigenproblem and poses
the positive sesquilinear-form problem on the finite zero-eigenfunction span.  It does not classify
full Schwartz-source forms, prove divisor support, study closability, or state the full-source
Hilbert-Gram graph obstruction.  Targeted arXiv searches through 1 August 2026 found no follow-up
closing those questions.  Priority remains provisional because the parent is recent.

## Gates

- [x] exact endpoint equivalence formalized
- [x] full continuous source-form class represented and classified
- [x] ordinary-`L²` nonclosability and dense-radical boundary formalized
- [x] faithful source-line Hilbert Gram quotient excluded
- [x] arbitrary partial ordinary-`L²` graph realization excluded
- [x] finite-span/discontinuous survivor separated from failed full-source subroute
- [x] strongest nontrivial positive survivor extracted
- [x] survivor paper proof dependency-closed
- [x] survivor Lean theorem surface unconditional
- [x] current primary-source search completed
- [x] live survivor assigned explicitly to open Route C1
