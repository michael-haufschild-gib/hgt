# Positive rate-mixture posterior curvature, finite-window, and properness law — Lean certificate

- **ID:** ULF-SHPC-3
- **Stage:** 3-formalized
- **Paper theorem:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/static-heterogeneity-observer-mechanics/positive-rate-mixture-posterior-curvature-finite-window-properness-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveStaticHeterogeneityObserver`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Date:** 2026-08-11

## Certified mechanism

Lean proves, for every finite nonnegative rate packet with at least one active component:

- positive partition mass and normalized nonnegative posterior weights;
- exact partition and first-moment derivative ladder;
- posterior moment normalization;
- variance as a centered square sum and as half a two-replica squared-gap moment;
- moment determinant equals partition square times posterior variance;
- posterior mean derivative equals negative posterior variance;
- apparent-exponent derivative and log-clock balance;
- zero variance iff all active rates coincide;
- common rate-floor inheritance;
- linear apparent-exponent lower bound and bounded clock projection of every exponent sublevel.

## Principal declarations

```text
HTGeometry.hasDerivAt_staticHeterogeneityPartition
HTGeometry.hasDerivAt_staticHeterogeneityMoment_one
HTGeometry.staticHeterogeneityVariance_eq_sum_sq
HTGeometry.staticHeterogeneityPosterior_pairwiseSqGap
HTGeometry.staticHeterogeneityDeterminant_eq_variance
HTGeometry.hasDerivAt_staticHeterogeneityMean
HTGeometry.hasDerivAt_staticHeterogeneityExponent
HTGeometry.staticHeterogeneityExponent_balance
HTGeometry.time_le_of_staticHeterogeneityExponent_le
HTGeometry.active_rates_eq_of_staticHeterogeneityVariance_eq_zero
HTGeometry.staticHeterogeneityVariance_eq_zero_of_active_rates_eq
```

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveStaticHeterogeneityObserver.lean` — PASS
- `lake build GaloisForLFunctions.HTGeometry.ConstitutiveStaticHeterogeneityObserver` — PASS, 8,699 jobs
- scratch `#print axioms` for eight capstones — only `propext`, `Classical.choice`, `Quot.sound`
- `scripts/formal_tools.py lint` — PASS
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` — PASS, 11,829 jobs

No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, computation, RH premise, or route-specific
zero hypothesis occurs.

## Scope

This certifies the finite positive exponential-mixture mechanism. It does not formalize the cited
paper's kinetic Monte Carlo model, prove a universal fitted exponent, classify general
first-passage distributions, or supply an RH selector.
