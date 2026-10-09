# Strict positivity in noisy conformal scale recovery

- **ID:** clock-positive-noisy-scale-feasibility
- **Stage:** 3-formalized
- **Type:** PROVED / exact physical-scale feasible-value classification
- **Source:** `ClockGapEnvelopeRecovery`, `ConformalClockNoisyMatrixRecovery`,
  `ConformalClockContinuousMatrixRecovery`.
- **Statement:** Set b(x)=exp(2 sigma(x)), g(x)=norm(projectiveDelayPanel(M(x))).
  A strictly positive competing real scale with L-Lipschitz error u=other-b,
  anchor error u(p)=a, and uniform projective-panel noise <=epsilon exists iff
  both conditions hold at every x:
  `g(x)|a| <= epsilon + g(x)L dist(x,p)` and
  `0 < b(x) + min(0, a + L dist(x,p))`.

## Why this is the next constraint

The completed noisy matrix theorem classifies all real competing scales. Strict
positivity of a physical conformal scale can rule out a negative anchor error even
when it passes every noise inequality and preserves positivity at the anchor.
The cone of errors forced nearby can reach places with a smaller reference scale.
The proposed second condition is the exact global positivity guard. It does not
replace an error-Lipschitz budget by an unproved Lipschitz estimate for logarithms.

## Paper proof [PROVED HERE]

The noise condition is necessary by the completed noisy-projective feasibility iff.
Every admissible error satisfies u(x)<=a+L dist(x,p). If that upper bound is negative,
strict positivity of b(x)+u(x) forces b(x)+a+L dist(x,p)>0. If it is nonnegative,
the proposed guard reduces to b(x)>0, which follows from the exponential definition.
This proves necessity without an assumed positive lower bound on b.

For sufficiency use the existing signed distance tent with anchor a. It realizes
the least absolute error at every point, so the first condition gives the observed
noise bound. If a>=0 the tent is nonnegative, hence b+u>0 automatically. If a<0,
the tent is exactly `min(0,a+L dist(x,p))`; the second condition is then precisely
strict positivity of b+u. The tent has the exact prescribed anchor and Lipschitz
budget. Shifting by b yields the competing scale for arbitrary independent scalar
defects. No regularity of sigma or the mass field is used.

Every strictly positive competing scale can also be written as exp(2 tau), with
tau=(log other)/2. The final Lean theorem supplies this representation without
asserting extra continuity or differentiability of tau.

## Corpus audit

`research "positive conformal scale Lipschitz anchor noise" --no-refresh --json`
returned unrelated scaling/Lipschitz interfaces (partial=false, semantic coverage
unmeasured). A focused lexical search for `positive` in `ConformalClock` modules
matched the existing positive single-species ambiguity and continuous logarithmic
scale uniqueness results, including `continuousConformalLogScale_unique_iff_dense`.
Those classify exact identifiability and do not supply this noisy positivity guard.
Only Lean entries were used; no web searches or external reading.

## Plan

- [x] Corpus searches and exact positivity-guard conjecture.
- [x] Dependency-closed paper proof, including both signs and zero anchor.
- [x] Formalize the strict-positive weighted-error classification.
- [x] Connect that classification to the actual projective matrix noise identity.
- [x] Formalize the positive-exponential representation.
- [x] Direct leaf, all-declaration axiom, umbrella, index and lint audits.

## Final Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ConformalClockPositiveNoisyRecovery.lean`
contains three proved theorems: `positiveClockGap_feasible_iff`,
`positiveNoisyProjectiveClock_feasible_iff`, and `conformalLogScale_noisy_feasible_iff`.
The final direct command
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ConformalClockPositiveNoisyRecovery.olean GaloisForLFunctions/HTGeometry/ConformalClockPositiveNoisyRecovery.lean`
passed with no diagnostics. Imported axiom checks for all three reported only
`propext`, `Classical.choice`, and `Quot.sound`. The scratch proof's unnecessary
sequence-focus warning was removed before the final audit.

Umbrella import occurs exactly once. Index regeneration passed and all three API
rows are present. No forbidden declarations, heartbeat changes, trailing whitespace,
numerical experiments, full builds or umbrella builds were introduced.
The authoritative global lint exited 1 on eight unrelated unreachable modules:
`RHTower.MobiusRieszCausalCalculus`, `RHTower.MobiusRieszSmoothingThreshold`,
`RHTower.XiRealRootedEigenLimitRH`, `HTGeometry.ApertureConeCalculus`,
`HTGeometry.ApertureConeWinding`, `HTGeometry.ApertureLogTranslation`,
`HTGeometry.ApertureOpenHistoryIdeal`, and `HTGeometry.BoundaryCoronaCStarAlgebra`.
No owned-leaf error was reported. Owned `/tmp/hgt-positive-clock*` scratch is cleaned
after evidence is recorded; unrelated work is untouched.

The positivity constraint is fully formalized, including its exponential receiver.
The regularity budget is on the physical scale difference, not on logarithmic scales.
The next corpus investigation is recorded independently in
`../1-in-progress/weil-countable-logshift-minorant-rigidity.md`.
