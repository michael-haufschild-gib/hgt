# BAG fixed-input Mellin parameter continuity

- **Stage:** 3-formalized

2026-10-06,01ax. Dependency-closed paper proof and Lean production closure.
ChiCubicMellinParameterContinuity362lines/API1, public317.
Production81641/log01 emptyPASS via lake --old env lean and explicit leaf
olean. Imported axiom37195/log01 PASS: propext, Classical.choice, Quot.sound
only. Index80052/log01 PASS/API1, RHT import once23601, scoped code diff PASS.
No admissions, added axioms or resource increases. Authoritative lint30316
terminal1:367warnings23unrelatedunreachable; no owned finding. Global lint
is NOT clean. Exact errors below.

For EVERY fixed physical Schwartz inputf, EVERYq0 in[1,2]^2 and EVERY
0<=s<=2, the complete Fourier Hs energy of
local(q,f)-local(q0,f) tends to zero asq->q0 within the parameter square.
No parameter continuity, domination or Schwartz-budget premise is assumed.

Proof: the literal joint log profile
F(q,u)=exp(-q0*u0-q1*u1)*chi(logNode(u))*f(logNode(u))
is jointly smooth for unrestrictedq, with common compact log support for
allq. Pure log jets are total joint directional derivatives in(0,e_i).
Derivative support containment preserves the common support. Continuity
on compact parameter-square times log-box bounds every fixed jet. Filter
DCT gives L2 convergence of each jet difference. Exact Schwartz jet
identification and linearity attach this to the actual localized profiles.
Fourier differentiation and Plancherel bound the full H2 energy by81 times
mass plus both pure second-jet masses. All three terms tend to zero;
weight comparison and ENNReal order squeeze give every0<=s<=2.

This pays the fixed-input parameter term in the moving-test comparison.
Actual physical/uniform local Cauchy convergence pays its other term.
The signed moving-test cancellation proof is still under audit; full
original sharp-action identification, growing moments/cofactors,
common-height self-return and RH remain open.

Scratch01/02 exposed elaboration issues only: explicit complex-real smooth
composition, typed constants and composition, ENNReal instance alignment.
Scratch03 proved the actual jet L2 limit; the final nhds(ofReal0) conversion
was fixed and production passed. Logs/search JSON retained; completed
parameter scratch sources and template removed after closure.

error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovKLWeight
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionClassLimits
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionFarey
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionOffResonance
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantCount
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantSmall
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ComplexMeasurePairing
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.FirstFailureCompactProperness
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.FirstFailureSourceTomography
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PositiveIntervalConvolutionDomain

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicMellinParameterContinuity` | `bagLocalizedMellin_parameter_energy_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
