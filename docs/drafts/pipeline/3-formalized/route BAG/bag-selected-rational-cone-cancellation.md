# BAG literal selected positive rational cone cancellation

- **Stage:** 3-formalized

2026-10-06,01ay. Dependency-closed paper proof and Lean production closure.
ChiCubicSelectedRationalConeCancellation173lines/API5public32/40/62/129/163.
Production12330/log01terminal0emptyPASS via lake --old env lean and explicit
leaf olean. All5 imported axioms8568/log01standard3: propext, Classical.choice,
Quot.sound. Index21706PASS/API5; RHTimportonce23616; scoped code/generated
diffPASS. No admissions, added axioms, heartbeat or recursion increases.
Authoritative lint70244terminal1:367warnings25unrelatedunreachable,
noownedfinding. Global lint is NOT clean. Exact errors below.

The selected physical Schwartz amplitudeA_N is the literal original
three-coordinate amplitude with controlled edge widthN^(1/4), with zero
only outside its admissible range. Eventual exact amplitude identity is
proved. The ENTIRE positive rational cone action
sum_w criticalRationalMass(P_N,w)*Fourier(A_N)(coneNode(point(w)))
is eventually summable and its complexnorm timeslog²N/N tends to zero.
Both arbitrary numerator cofactors, both distinguished-label exclusions,
the allowed first/second collision and all rational points remain.

Proof: existing full physical_line_hasSum equals this action with the
complete source/Mellin integral on sigma_i=1+1/logN. The actual selected
normalized physical cone is exactlyL³/N timesconeSchwartz(A_N). At the
actual critical parameters, literal log pullback and Fourier linearity
identify the selected moving Mellin transform with the same scalar times
the original physical line profile. The normalized arithmetic source is
exactlythefull source divided byL, with native2*pi frequencies intact.
Therefore its complete integral equalsL²/N times the admitted original
rational cone action. The closed actualmovingtest cancellation, followed
by complexnorm and nonnegative real scalar normalization, proves the limit.
No assumed analytic uniformity, source cancellation or profile replacement.

Audit39766/log01 proved every source/profile/HasSum/admission identity but
failed finalnormrewrite: Complex.norm_real leaves a real norm, so the exact
nativeReal.norm_of_nonneg is required. Removed a redundant ring after
field_simp. Production with those two fixes passed; importedaxioms audited.

SCOPE: sourceprimecutoffP_N, physicalscaleN, POSITIVE EXACT CONE. The whole
sharp cubic onphysicalband[N,2N] uses its covered source throughfloor2N,
ALL globalnonzero transverse defects and bothprojectors. None is identified
away here. NextP1 bag-covered-source-mellin-transfer proves the essential
source2N/physicalN coupling, then coveredcone attachment. Fullglobaldefect
cancellation, growingmixedmoments/cofactors, commonheightreturn and RHopen.

Completedownedcone scratch/axiomsource removed; all logs/search JSON retained.

error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovKLWeight
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovOppositeSign
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
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentLimit
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
| `GaloisForLFunctions.RHTower.ChiCubicSelectedRationalConeCancellation` | `bagCubicSelectedPhysicalSchwartz_eventually_apply`, `bagCubicSelectedRationalConeAction_summable`, `bagCubicSelectedRationalConeAction_norm_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
