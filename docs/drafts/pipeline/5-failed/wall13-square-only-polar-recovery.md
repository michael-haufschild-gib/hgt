# Square-only polar recovery fails; signed reconstruction survives

- **ID:** BSU-W13-SQUARE-POLAR-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean)
- **Scope:** BiScaleUncertainty, Wall 13; no RH conclusion.
- **Rejected statement:** the complete squared autocorrelation determines the normalized polar moment of every compact continuous real source.

## Exact killing theorem

`SeparatedSquare.polarMoment_not_factor_through_square`, in
`formal/GaloisForLFunctions/BiScaleUncertainty/SchurSquarePolarAmbiguity.lean`,
proves that no functional from real lag profiles to real numbers can recover
the normalized polar moment from the squared autocorrelation.

The hypothesis-free witness theorem
`SeparatedSquare.exists_smooth_same_square_distinct_polar` constructs two smooth
compact sources with positive equal mass, identical squared autocorrelations at
every real lag, and respectively zero and strictly positive polar moment.
`exists_smooth_same_zeros_distinct_polar` also identifies their entire blind-node
sets. Thus the obstruction persists even with complete zero-set information.

## Strongest positive survivor

Fix an actual compact continuous seed with autocorrelation h, mass R, positive
support radius D, and gap T=2D+1. Put g_a(u)=f(u)-a f(u-T), k(a)=a/(1+a²),
and let H_a be its normalized autocorrelation. For nonzero mass, the complete
squared profiles agree exactly when k(a)²=k(b)²; the complete signed profiles
agree exactly when k(a)=k(b). Zero mass is covered separately by the same
unconditional theorem statements. One signed anchor recovers the entire profile:

    H_a(x)=H(x)+H_a(T)[H(x-T)+H(x+T)].

These are the exact Lean theorems `SeparatedSquare.square_profiles_eq_iff`,
`profiles_eq_iff`, and `correlation_reconstruction` in
`SeparatedCopySquareClassification.lean`.

The square also retains a literal product-plane Gram realization and an exact
nonnegative energy split:

    (R²-h(x)²)+(R-h(x))²=2R(R-h(x)).

Integration against the positive Lévy-sinh weight gives
`SchurSquare.levyEnergy_add_quarticDefect` in `SchurSquareCorrelation.lean`.
Both sides are extended nonnegative integrals, so the identity requires no
integrability assumption or subtraction of infinities.

## New insight and boundary

The transfer preserves every blind node and supplies a pointwise nonnegative
Bochner kernel, while losing the signed datum needed for polar balance. For
this separated two-copy family the missing datum is exactly one signed scalar.
This is a reconstruction law, not merely a restated negative result.

The tensor source lives on the product plane under diagonal translations.
No one-dimensional scalar factorization, individually blind fibre decomposition,
general-source reconstruction theorem, or blind-source coercive lower bound is
proved. Wall 13 remains open.

## Status

- Dependency-closed paper proof and exact Lean survivor: complete.
- Three direct leaf checks and final capstone audit: exit 0, empty logs.
- Every public declaration axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wiring and index refresh complete. Global lint has one unrelated concurrent error, `BiScaleUncertainty.FactorialWeilGram` unreachable from its umbrella.
- Full proof, evidence and next unproved closed-cycle conjecture: [formalized package](../3-formalized/wall13-schur-square-orientation.md).

## Log

- 2026-10-18 — Retired exact square-only recovery claim after formalizing its positive classification, signed-anchor reconstruction and energy decomposition.
