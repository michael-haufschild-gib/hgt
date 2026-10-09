# Exact recovery from a finite observation window

- **ID:** clock-finite-window-gap-recovery
- **Stage:** 3-formalized
- **Type:** PROVED / exact feasible-value classification
- **Source:** `ClockGapEnvelopeRecovery`, `ClockPowerGapRecovery`.
- **Statement:** For integer k>=1 and L,epsilon,R>=0, an L-Lipschitz real field
  with u(0)=a and |x|^k |u(x)|<=epsilon for every |x|<=R exists iff, with A=|a|,
  both `R^k A <= epsilon + L R^(k+1)` and
  `k A <= (k+1)L R -> k^k A^(k+1) <= (k+1)^(k+1)L^k epsilon` hold.

## Why this follows the completed power-gap result

The global theorem observes the whole real line. A finite observation radius need
not contain the critical radius kA/((k+1)L), so using its global sharp constant
without that geometric check would impose an unjustified constraint. The classification
replaces an infinite family of local observations by an endpoint test and a critical
point test only when that point is observed. R=0 permits every anchor value; L=0
permits precisely the constant amplitudes allowed by the finite endpoint bound.

## Paper argument

The previously proved least envelope reduces function existence to
`t^k max(0,A-Lt)<=epsilon` for all 0<=t<=R. The same signed tent realizes the
least envelope on the whole line, so no extension hypothesis is required.

Necessity of the endpoint test follows at t=R. When L>0 and
kA<=(k+1)LR, evaluate at t=kA/((k+1)L) and use the exact identity from the
power-gap proof to obtain the second test. When L=0 the condition forces A=0,
so that second test is automatic.

For sufficiency when the critical point is inside the window, the completed global
power-gap theorem bounds the entire envelope. In the complementary case put
D=kA-(k+1)LR>=0. For 0<=t<=R, homogeneous Bernoulli with r=t, b=R-t and n=k+1
gives `t^k((k+1)R-kt)<=R^(k+1)`. Also `D t^k<=D R^k`. Adding L times the
first inequality to the second and cancelling k>0 gives
`t^k(A-Lt)<=R^k(A-LR)`. This bounds the positive part by the endpoint test.
If A-Lt<0 the envelope is zero. At R=0 all observations vanish and the endpoint
condition is automatic; the critical condition can only add a tautology.

This algebraic proof includes boundary equality kA=(k+1)LR in the global branch;
no differentiation, division by R, or positivity premise on L/R is needed.

## Corpus audit

`research "bounded interval weighted Lipschitz sharp recovery radius" --no-refresh --json`
returned generic local Lipschitz estimates, compact-window quadrature and unrelated
recovery weights. No matching finite-window feasible-anchor classification appeared.
Only Lean source entries were inspected. partial=false; source-only freshness,
semantic coverage unmeasured. This is not a claim that corpus retrieval is exhaustive
or a claim of external novelty. No web searches or external reading.

## Plan

- [x] Corpus search and exact candidate, including L=0/R=0 endpoint audit.
- [x] Algebraic paper proof based on existing least-envelope and Bernoulli results.
- [x] Formalize the endpoint monotonicity argument inside the classification.
- [x] Formalize finite-window feasibility iff and signed-tent realization.
- [x] Direct leaf, axiom, umbrella, index and lint audits.

## Final Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ClockFiniteWindowGapRecovery.lean` proves
`powerClockGap_critical_radius_value`, `finiteWindowClockGap_envelope_iff`,
`finiteWindowClockGap_feasible_iff`, and `finiteWindowClockGap_extremizer_bound_iff`.
The final direct command
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ClockFiniteWindowGapRecovery.olean GaloisForLFunctions/HTGeometry/ClockFiniteWindowGapRecovery.lean`
passed with no diagnostics. Imported axiom checks for all four theorems reported
only `propext`, `Classical.choice`, and `Quot.sound`. The critical-radius identity
uses totalized division at L=0 and does not assert a global maximum in that case.

Umbrella integration occurs exactly once; index regeneration passed and all four
API rows are present. No forbidden declarations, heartbeat changes, or trailing
whitespace occur in the leaf. No numerical experiment, full build, or umbrella
build was run. The current global lint exited 1 on seven unrelated unreachable
modules: `RHTower.PaperPrimeSeamIdealTrace`, `RHTower.XiOneSidedAtomRigidity`,
`HTGeometry.ApertureConeCalculus`, `HTGeometry.ApertureConeWinding`,
`HTGeometry.ApertureLogTranslation`, `HTGeometry.ApertureOpenHistoryIdeal`,
and `HTGeometry.BoundaryCoronaCStarAlgebra`. No owned-leaf error was reported.

The exact finite-window theorem is now verified. Its error field is globally
Lipschitz while its observation bound is required only in the stated window.
The signed tent realizes every feasible anchor without a separate extension premise.
