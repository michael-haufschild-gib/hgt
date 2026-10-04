# BAG actual sources: global bounds for every derivative

- **ID:** BAG-C28.56ad.
- **Route:** BAG rational cubic to noncompact critical tests.
- **Namespace:** RHTower.BAGTrace.
- **Leaves:** ChiRamanujanGlobalResidueControl;
  ChiRamanujanGlobalSourceNeighborhoods; ChiRamanujanGlobalSourceDerivatives.
- **Audit status:** all three production leaves and all 12 public-theorem
  axiom audits passed. Formal lint result recorded below.

## Exact new statements

For EVERY derivative order n there is C_n>0 such that the literal actual
realCubicSource A and realAxisSource T satisfy, uniformly for sigma in [1,2],

    norm(D^n A(sigma,u,v)) <= C_n*(1+|u|+|v|)^(54+9*n),
    norm(D^n T(sigma,u))   <= C_n*(1+|u|)^(18+9*n).

These are full joint real Frechet derivatives, including damping derivatives,
not just derivatives along one frequency. The corresponding complex joint
bounds are also proved. No growth assumption or RH premise is supplied.
The exponents certify polynomial growth; optimizing them was not the target.

Actual complex neighborhoods are part of the result: a single positive d
works at every frequency, with radius d/(1+|u|+|v|)^9 (respectively d/(1+|u|)^9).
Every point in these closed balls belongs to the actual source's analytic
domain and obeys its polynomial norm bound. Denominator nonvanishing is
proved separately, not inferred from a totalized reciprocal estimate.

The underlying pole-removed zeta factor F and its reciprocal have uniform
polynomial disks throughout sigma in [1,2], and every scalar derivative is
bounded by C_n*(1+|t|)^(9*(n+1)). Actual H and K Euler corrections have uniform
bounds over their entire fixed complex normal-convergence tubes.

## Dependency-closed proof

1. Combine the pinned corpus's separately audited logarithmic zero-free
   region and reciprocal bound. Outside the upper edge of that logarithmic
   strip, the actual Mobius L-series identity and bound apply. Replacing
   logarithmic widths by smaller polynomial widths yields an unconditional
   polynomial-width zero-free region and polynomial reciprocal control.
2. At high height choose disks about sigma+it of radius c/(1+|t|)^9. Coordinate
   estimates keep them in that region. The corpus's quarter-strip zeta bound
   controls F; the lower bound on |s-1| controls 1/F. At bounded height the
   compact strip segment, including F(1)=1, lies in the open nonvanishing
   locus. A compact thickening gives a uniform zero-free neighborhood and
   simultaneous bounds. This closes the entire damping strip.
3. The actual prime factors obey the existing summable tube majorants.
   Bound each finite product by exp(sum majorant), then pass its actual
   HasProd limit. This proves global bounds for H and K without assuming
   them or replacing the full Euler product.
4. A small complex coordinate ball controls all six residue arguments:
   sigma +/- alpha, sigma +/- beta, sigma +/- (alpha-beta). Four numerator
   factors, two reciprocal denominator factors, and H give the cubic
   polynomial bound. The same argument with two factors and K gives the
   axis bound. The argument includes the diagonal and both frequency axes.
5. Extend the corpus's scalar entire-function Cauchy mechanism to local
   analytic balls and Banach-valued targets. Bound the differential using
   one-dimensional complex lines. Repeating on nested half-radius balls
   gives every joint derivative, with constants depending only on its order.
6. Apply that theorem to the ACTUAL source balls. Restrict complex multilinear
   derivatives to real scalars, then pull back by the frequency isometry
   (sigma,u,v) -> (sigma,iu,iv). Local Taylor composition and the multilinear
   operator norm prove the literal real-source statements above.

## Novelty and failure learning

The source corpus had local smoothness, compact-box derivative bounds,
normal Euler products and the separate zeta estimates. It did not supply
this global actual-source derivative theorem in the inspected searches.
The new result joins those inputs without promoting an assumed source bound.
The conjecture originally requested second derivatives; Cauchy iteration
forces the stronger all-order result, now proved by the same mechanism.

Lean failures were elaboration issues, not counterexamples. Explicit tuple
and source arguments prevented unification from expanding complete Euler
factors. Scalar polynomial identities proved before instantiation avoided
expanding large frequency powers. Local real pullback required the correct
open-neighborhood derivative identity. Default heartbeats retained.

Search17172 nonpartial65507/65507 and search93538 nonpartial65510/65510;
compiler metadata mostly pending/source-only, background refresh incomplete.
All candidate/source/proof/ingredient sections inspected; every applied
mathlib API checked in scratch. No numerical experiment or new axiom.

## Frontier meaning

This closes actual global source growth and all required source derivatives.
It does NOT itself prove the noncompact critical boundary: the complete
reflected finite-part/product-PV quotients still need integrable uniform
dominators, and intersection concentration must retain the moving source.
That is C28.56ae in P1 bag-global-cubic-source-growth.

Physical prime-contraction matching, finite-prime integral-net transfer,
finite-height near-resonances, growing profiles/coupled limits, growing
moments, moving cofactors and positive common-height self-return remain open.
RH is unproved; the BAG goal remains active.

## Audits

Production12824 (GlobalResidueControl), production98490
(GlobalSourceNeighborhoods) and production37747 (GlobalSourceDerivatives)
exited0 without diagnostics. Each used lake --old env lean on the leaf with
explicit olean output. All three are wired once into RHTower; no umbrella
or full build was run. Axiom94140 exited0: all12 public theorems depend only
on propext, Classical.choice and Quot.sound. Index24249 exited0; all12
public names occur in LEAN_API. Lint13364 exited1 with exactly21 unrelated
unreachable-module errors, no new-leaf, proof-debt or freshness error.
Owned scratch sources and fragments removed after successful audits; evidence
logs/search JSON retained. No subagents, numerical computations, heartbeat
changes, new axioms, full builds, commit or push.

Evidence: /tmp/bag-global-residue-production-01a0.log,
/tmp/bag-global-source-neighborhoods-production-01a0.log,
/tmp/bag-global-source-derivatives-production-01a0.log,
/tmp/bag-global-source-axioms-01a0.log, /tmp/bag-global-source-index-01a0.log,
/tmp/bag-global-source-lint-01a0.log.
