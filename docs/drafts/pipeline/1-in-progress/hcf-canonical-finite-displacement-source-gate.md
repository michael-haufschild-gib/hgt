# HCF canonical finite-displacement source gate

- **ID:** HCF-CANONICAL-FINITE-DISPLACEMENT
- **Stage:** 2-fully-proven on paper; formalized in a standalone Lean module
- **Type:** proved source-reduction theorem
- **Source:** Route HCF; source Plemelj trace + canonical height window + centered real shifts

## Goal

Collapse two nested source limits in canonical HCF pole--Gamma Plemelj covariance to one
height-local compact evaluation at a positive submicroscopic displacement. This exposes a finite,
zero-independent arithmetic object on which a quantitative Euler--Gamma/von-Mangoldt estimate can
act.

## Corpus audit

- `HedenmalmCriticalFeatureSourcePlemeljTrace` unconditionally replaces the critical-line
  `XiZeroCopy` trace by compact positive-shift pole--Gamma observables, then takes shift and cutoff
  limits.
- `HedenmalmCriticalFeatureCanonicalHeightWindow` proves corrected budget and infinite Plemelj
  covariance differ by `o(N)` on canonical windows.
- `XiCenteredRealShiftDiagonalExtractor` and
  `XiCenteredRealShiftCauchyPairExactCorrection` show positive real shifts carry exact diagonal
  multiplicity corrections.
- Whole-corpus research found no theorem selecting one simultaneous cutoff/displacement schedule
  for canonical HCF windows.

## Theorem FD1

There exist source-selected sequences `M(n) : ℕ` and `eta(n) : ℝ` with
`0 < eta(n) < min(1/2, 1/(n+1))` such that the finite source covariance

`poleGammaLatticeBudget(K_n) - sum_{k in K_n} compactPoleGammaObservable(k,M(n),eta(n))`

differs from infinite source-only Plemelj covariance by less than `1/(n+1)`.

Consequently their difference divided by `N(n)` tends to zero, and every canonical asymptotic
ceiling—including reflected direct-three-center constant `15872/21125`—is equivalent for the
finite-displacement covariance and infinite Plemelj covariance.

FD1 is proved in
`formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureCanonicalFiniteDisplacement.lean`.
The selected cutoffs are cofinal, selected displacements are positive and tend to zero, and the
finite covariance error is pointwise `< 1/(n+1)`.

## Lean verification

- Direct source typecheck: passed.
- Targeted module build: passed (`13,507` jobs).
- Public theorem axiom audit: all nine public theorems use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No theorem in this module assumes a zero-density or quantitative source bound.

## Frontier consequence

FD1 does not prove the quantitative ceiling. It removes nested boundary scalarization from that
ceiling and replaces it by one compact positive-shift source evaluation per height. Remaining
arithmetic target becomes a uniform bound for these finite pole--Gamma/von-Mangoldt evaluations:

`CriticalFeatureCanonicalAsymptoticUpper
  criticalFeatureCanonicalFiniteDisplacementCovariance (15872 / 21125)`.

The user-requested `21/100` and `4/25` bounds are stronger possible source ceilings. Selection is
nonconstructive: arithmetic estimates must either be uniform over admissible cutoff/displacement
pairs or supply an effective modulus and an explicit cofinal schedule.

## Log

- `2026-08-30`: FD1 proved and formalized; single finite source observable replaces both nested
  source limits without introducing a divisor-dependent predicate.
