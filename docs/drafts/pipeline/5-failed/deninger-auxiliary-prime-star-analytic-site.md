# Auxiliary prime-star analytic site

- **ID:** `deninger-auxiliary-prime-star-analytic-site`
- **Stage:** 5-failed
- **Type:** RETIRED CONSTRUCTION / UNNECESSARY REPLACEMENT
- **Label:** `DAC_AUXILIARY_PRIME_STAR_ANALYTIC_SITE`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`

## Retired construction

Glue a generic analytic torus to one one-coordinate boundary chart for
every rational prime, producing an auxiliary nonseparated
“prime-star” analytic space.  Put the Tate--Milnor coefficient on that
space, compute its Čech complex, then compare its pushforward with
Deninger's coarse invariant coefficient.

## Failure

The construction replaces a source problem by two harder unproved
ones:

1. an analytic realization map from the auxiliary gluing to
   Deninger's actual rational-Witt suspension;
2. a pushforward equivalence with the already-formed invariant
   coefficient.

It also risks repeating the retired chart-cochain type error if
global functions on its pieces are used as the coefficient.

Most importantly, no auxiliary prime-star topology is needed.
`DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS` proves that
\(\operatorname{Spec}\mathbb Z\) itself has exactly the required
generic-prime cofinite topology, and every finite prime boundary gives
an actual open--closed recollement.  Deninger's arithmetic projection
pulls these recollements back to his source space by
`DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`.

## Positive survivor

Use the filtered family of actual finite recollements
\[
 P\hookrightarrow\operatorname{Spec}\mathbb Z
 \hookleftarrow\operatorname{Spec}\mathbb Z\setminus P.
\]
Combine:

- generic pro-Stein derived sections;
- generalized-log prime Kummer purity;
- finite disjoint local cohomology;
- strict filtered passage to the direct-sum residue row.

The exact remaining conjecture is
`DAC_COFINITE_PRO_RECOLLEMENT_ANALYTIC_COMPARISON`.

## No-go closure

The analytic boundary-chart intuition survives only as a local model
for proving generalized-log purity.  It is not a new global space or
source coefficient.

**Verdict:** `RETIRED AS UNNECESSARY SOURCE REPLACEMENT; ACTUAL
SPEC Z RECOLLEMENT BASIS PROVED`.

## Log

- 2026-07-27 — retired before implementation after comparing its
  topology with the exact Zariski topology of
  \(\operatorname{Spec}\mathbb Z\).
