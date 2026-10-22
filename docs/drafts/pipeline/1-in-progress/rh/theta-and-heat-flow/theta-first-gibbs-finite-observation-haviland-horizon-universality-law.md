# Theta first-Gibbs finite-observation Haviland-horizon universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.ThetaFirstGibbsFiniteObservationHavilandHorizonUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`ThetaFirstGibbsSupportHavilandUniversalityLaw` proves that the complete first theta-Gibbs moment
sequence has an exact positive-half-line density and is positive on every polynomial nonnegative
on that support.

`HankelGuardrailConsequences` proves that every finite real moment prefix with positive zeroth mass
admits an arbitrarily delayed continuation having a negative polynomial-square test and hence no
positive representing measure.

The theta source has strictly positive zeroth mass by the exact exponential-orientation inequality.
No corpus theorem applies the arbitrary-prefix obstruction to this exact support-Haviland source.

## Statement

The complete first theta-Gibbs moment sequence has its full support-Haviland certificate. Yet, for
every observed prefix through order `N` and every delayed index `n > N`, there exists a real
sequence `b` such that:

1. `b` agrees exactly with the true theta sequence through order `N`;
2. the delayed square `(1 - 2 X^n)^2` has strictly negative `b`-moment;
3. no positive measure on `ℝ` with all polynomial moments represents `b`.

Thus no finite prefix, however long, certifies the global moment/Haviland phase of this exact
theta source.

## Dependency-closed proof

The inequality
`exp (-pi) < 2*pi*thetaCuspLiouvilleGibbsMoment 0 1`, together with positivity of exponential and
`pi`, gives positive zeroth mass. For each `N < n`, instantiate `badMomentContinuation` with the
first `N+1` true theta moments. `badMomentContinuation_prefix` gives exact observational
agreement, while `badMomentContinuation_delayedSquareTest` and the positive zeroth mass make the
test value `-2*m₀ < 0`. `badMomentContinuation_not_momentSequence` excludes every positive
representing measure. Pair this with `thetaFirstGibbs_supportHavilandUniversality`.

No numerical experiment or approximation is used.

## Novelty audit

Corpus audit: exact theorem search found the generic delayed bad continuation and the complete
theta Haviland certificate separately, but no source-specific finite-observation horizon theorem.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Dependency-flattened exact proof check passed:
`lake env lean /private/tmp/law491_scratch.lean`.

The source is wired into `GaloisForLFunctions.RHTower`; direct source, axiom, lint, and umbrella
checks remain for the final audit because LAW481's imported module is not cached yet.
