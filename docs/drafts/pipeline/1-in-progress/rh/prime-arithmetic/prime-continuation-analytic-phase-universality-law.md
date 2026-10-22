# Prime-continuation analytic-phase universality law

- **ID:** `prime-continuation-analytic-phase-universality-law`
- **Law:** LAW505
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/PrimeContinuationAnalyticPhaseUniversalityLaw.lean`

## Theorem

Three independently constructed prime continuations have one universal right-half-plane analytic
phase.  RH is equivalent to simultaneous holomorphy on `Re s > 1` of:

1. the fixed dyadic sharp-prime continuation;
2. the elementary simple-prime divisor continuation;
3. every compact-BV prime-window continuation whose Mellin transform is zero-free there.

Its complement is equally synchronized: failure of RH is equivalent to non-holomorphy of the two
fixed continuations and of every such noncensoring compact-BV continuation.

## Theorem-generated derivation

Whole-corpus reading exposed three terminal criteria:

- `riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne`;
- `riemannHypothesis_iff_simplePrimeDivisorContinuedSource_analyticOn_rightOne`;
- `CompactBVPrimeWindow.riemannHypothesis_iff_continuedSource_analyticOn_rightOne`.

`XiCCMMultiObservableDivisorUniversalityLaw` identifies local pole coordinates and normalized
residues after choosing a right Xi divisor.  It does not state global regularity invariance and
does not quantify over every noncensoring BV window.  The present law closes that missing global
phase.

## Dependency-closed paper proof

Under RH, apply the three existing forward implications; the third is uniform in the window after
supplying its zero-free Mellin hypothesis.  Conversely, the dyadic component alone implies RH by
its existing reverse implication.

For the complementary statement, assume non-RH.  Holomorphy of any listed continuation would
imply RH by its existing reverse implication, contradiction; hence all fail simultaneously.
Conversely, non-holomorphy of the dyadic continuation contradicts its forward implication under
RH.  Classical logic is not needed beyond ordinary negation introduction.  No numerical
computation is used.

## Strict corpus delta

Corpus has three separate RH criteria and a local nine-chart divisor certificate.  It lacks one
parameter-free certificate quantifying over the full noncensoring compact-BV family, and lacks the
dual universal simultaneous-failure law.  This is a family-level analytic-phase invariant, not a
renaming of one detector.

## Lean result

`formal/GaloisForLFunctions/RHTower/PrimeContinuationAnalyticPhaseUniversalityLaw.lean` proves:

- `riemannHypothesis_iff_primeContinuationAnalyticPhaseUniversalCertificate`;
- `not_riemannHypothesis_iff_primeContinuationNonanalyticPhaseUniversalCertificate`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/PrimeContinuationAnalyticPhaseUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.

- Gonek's short-Euler-product work studies families approximating zeta and the behavior of their
  zeros under RH, not a synchronized holomorphic/non-holomorphic phase for the present three
  pole-filled prime continuations.
- Banks' sparse-prime work gives RH-equivalent Lindelöf hypotheses for selected prime subsets, not
  a universal compact-BV Mellin-window analytic certificate.
- Standard Mellin/distributional continuation literature supplies general continuation machinery,
  but targeted searches found no theorem with this full quantified BV family and the two explicit
  companion sources.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed only for the exact
three-construction family certificate and synchronized complement, not for the elementary logical
fact that several RH-equivalent predicates are equivalent.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
