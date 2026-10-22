# HCF canonical lattice-summed finite-displacement gate

- **ID:** HCF-CANONICAL-LATTICE-SUMMED-DISPLACEMENT
- **Stage:** 2-fully-proven on paper; standalone Lean module added
- **Type:** proved source-reduction theorem
- **Source:** Route HCF; canonical finite displacement + source Plemelj trace

## Goal

Move height-lattice aggregation inside the source observable before scalarization. Earlier finite
displacement realization evaluates one compact boundary integral per feature center and then sums
the resulting scalars. Quantitative Poisson/Fourier cancellation instead needs one test weight
containing the entire lattice sum.

## Corpus audit

Whole-corpus `scripts/formal_tools.py research` searches found:

- source-only compact pole--Gamma observables and their Plemelj limits;
- exact pole--Gamma/von-Mangoldt lattice channels and safe-line `O(card K)` prime bound;
- general finite-sum, periodization, Poisson, and Dirichlet mean-value infrastructure;
- no HCF theorem placing the feature-lattice sum inside one compact source integral;
- no shifted-lattice/phase-averaged HCF budget.

## Failed conjecture: phase averaging alone

Averaging translated integer centers over one phase period turns the full lattice weight into its
real-line integral. But this also exposes essentially the total off-line HCF charge. It supplies no
subunit normalized ceiling by itself, so it is not a quantitative shortcut to 75%.

Positive survivor: retain lattice fusion without claiming phase averaging yields cancellation.

## Theorem FD2

For every finite integer feature lattice `K` and cutoff `M`, define the fused compact source
observable

`∫ (Σ_{k∈K} w_{k,M}(x)) · density_η(x) dx`,

where `density_η` is the literal positive-shift continued pole--Gamma--von-Mangoldt density.
Its one-sided limit as `η ↓ 0` is exactly the sum of the individual critical-line cutoff traces.

On canonical windows there are source-selected sequences `M(n) ≥ n` and
`0 < η(n) < min(1/2,1/(n+1))` such that the fused finite covariance differs from infinite source
Plemelj covariance by `< 1/(n+1)`. Consequently the normalized difference is `o(N(n))`, and the
reflected direct-three-center ceiling `15872/21125` is equivalent for corrected HCF budget and
the fused finite source covariance.

Lean module:
`formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureCanonicalLatticeSummedDisplacement.lean`.

## Frontier consequence

Remaining 75% target is now one collective finite integral per height:

`CriticalFeatureCanonicalAsymptoticUpper
  criticalFeatureCanonicalLatticeSummedDisplacementCovariance (15872 / 21125)`.

Unlike centerwise scalarization, this form permits Poisson summation, Fourier-mode separation,
and cancellation across feature centers before absolute values. User-requested `21/100` and
`4/25` remain stronger possible ceilings.

Selection remains nonconstructive. Next quantitative theorem must either be uniform over the
selected admissible cutoff/displacement pairs or provide an explicit effective schedule.

## Lean verification

- Direct source typecheck: passed.
- Targeted module build: passed (`13,508` jobs).
- Public theorem axiom audit: all fourteen public theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration was added.

## Log

- `2026-08-30`: phase-average shortcut rejected; FD2 survivor proved and formalized. Direct check,
  targeted build, and public axiom audit passed.
