# SZ: actual ramp current at the Gamma cusp

- **ID:** SZ-RAMP-CUSP-ENERGY-CONCENTRATION
- **Stage:** 3-formalized; all six public declarations audited.
- **Target:** unconditional canonical-head Gamma--prime--polar positivity.

## Proved statement

The actual exponential-ramp visible energy cannot be uniformly bounded as
the physical cutoff grows. More precisely, its signed current integral
outside every fixed cusp window tends to zero, while its signed total
action does not tend to zero. Gamma capacity of a shrinking neighborhood of zero vanishes, so
bounded visible energy would force the action to vanish.

The positive survivor is an actual concentration law: cofinally large
visible energy in every fixed neighborhood of zero, simultaneously with
nonvanishing signed action, and a signed current integral tending to zero
outside every such neighborhood. This identifies why uniform absolute
energy control cannot supply the cancellation required by route SZ.
It does not prove that the signed action is unbounded or decide RH.

## Proof mechanism

1. `CCMPrimeQuantileHeightLimit` proves both literal cell displacements
   tend to zero. The terminal displacement has the same limit at real
   physical time.
2. `CCMPrimeDeficitFluxBoundary` identifies the flux state as the future
   exponential convolution of the normalized deficit. A tail bound
   epsilon on the incoming amplitude bounds the state by 2 epsilon.
   `CCMPrimeDeficitWeilFlux` identifies outgoing amplitude with actual
   Weil lag plus its archimedean correction. The unconditional lag
   oscillation in `WeilLagFunctionOmega` excludes incoming decay to zero.
3. `CCMQuantileExponentialRampDeficit` identifies the full signed ramp
   action with that incoming amplitude minus a decaying transient.
4. Outside any fixed cusp window, all late cells and terminal current
   vanish exactly. Only a fixed finite head remains; its coefficients
   decay as exp(-T/2) times an affine function of T.
5. Localize the weighted-square identity of
   `CCMExponentialRampCurrentProjection`. Integrability of the capacity
   density forces its shrinking-window integral to zero. Combine with
   steps 2--4 to exclude a cofinal tail bound on cusp visible energy.

No premise asserting RH, a source bound, a spectral gap, or a convergence
rate is allowed in the final actual-source obstruction. Intermediate
implications must be discharged. Full prime powers and both terminal
orientations remain present.

## Retrieval audit

Search `sz_ramp_cusp_search` (generation1220617) was partial, coverage
pending, with no useful primitive-oscillation hit. Direct source reads
established the flux-convolution mechanism above. Search misses do not
establish absence or novelty. The narrower deficit search1220649 was
also partial with coverage pending and irrelevant suggested ingredients.

## Paper proof (dependency closed and Lean audited)

Write I(T)=exp(-T/2)P(T), S(T) for the flux state and O(T)=S(T)-I(T).
The corpus gives S(T)=lim_U integral_T^U exp(-(t-T)/2)I(t)dt. Therefore
|I(t)|<=c for all t>=T implies |S(T)|<=2c and O(T)<=3c.
At T=log n, O(T) equals integerLag(n) plus a nonnegative archimedean
correction: log(2*pi)>1>=trivialZeroSeriesReal(n). The unconditional
recurrence ceiling P0=poleSharpConstant>0 is approached from below
cofinally by integerLag. Taking c=P0/4 contradicts a tail bound on I.
Thus |I(T)|>P0/4 cofinally. Since T exp(-T/2)->0, the literal full ramp
action A(T) has |A(T)|>k=P0/8 cofinally.

Fix a displacement radius delta>0. Both endpoints of every sufficiently
late cell lie in (-delta,delta). The terminal displacement also tends to
zero: add b_(floor(exp T)+1)-log(floor(exp T)) to
log(floor(exp T)/exp T). Consequently the integral of the complete current
outside this window eventually equals a fixed finite sum. Each term is
exp(-T/2) times an affine function of T, with finite fixed spatial
integrals. The outer signed integral tends to zero.

Let C(epsilon) be Gamma capacity on |r|<epsilon. Its integrable density
vanishes at zero, so dominated convergence gives C(epsilon)->0. The
localized weighted-square identity holds for both signs of t:

    2t |integral_{|r|<epsilon} J_T(r)dr|
      <= E_epsilon(T) + t^2 C(epsilon),    t>0.

Suppose E_delta(T)<=B eventually at times with |A(T)|>k. Put
B'=max(B,0)+1 and t=2B'/k. Choose 0<epsilon<delta with
C(epsilon)<k^2/(4B'). Nonnegativity gives E_epsilon<=E_delta<=B at
those times, hence the inner signed integral has absolute value <k/2.
The outer signed integral also has absolute value <k/2 eventually.
This contradicts |A(T)|>k. Therefore, for every delta>0 and every B,
cofinally **both** |A(T)|>k and E_delta(T)>B.

This simultaneous nonvanishing/concentration statement is the positive
survivor. It excludes uniform visible energy and therefore uniform full
arithmetic Gamma energy. It does not exclude bounded signed action,
which remains the RH-equivalent unresolved target.

## Lean audit, 2026-10-04

Leaf: `formal/GaloisForLFunctions/RHTower/CCMExponentialRampCuspConcentration.lean`.
Scratch39975 verified incoming nonvanishing. Combined14103 and35423
required coercion and limit-type repairs;54437 exposed one extra tactic
after its goal was solved. Final93039 exited0 with no diagnostics:

    lake --old env lean GaloisForLFunctions/RHTower/CCMExponentialRampCuspConcentration.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMExponentialRampCuspConcentration.olean

Axiom45260 exited0: every public declaration uses only propext,
Classical.choice, Quot.sound. Mathlib API name checks were included in
the same /tmp audit. One umbrella import; no umbrella/full build, added
axiom, heartbeat override, subagent, or numerical experiment.

Lint83841 exited1 on13 unrelated unreachable modules: CCMApertureChainProfile,
CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MertensProductDiamondPintz,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ThetaTailCorrectionCurrent,
ZetaZeroDensityPowerSaving; HTGeometry.CompactMonoidMeasureAlgebra.
The new leaf was not reported.

RH remains unresolved. The failed candidate is only uniform literal
exponential-ramp visible/full arithmetic Gamma energy. The exact signed
action and canonical-head joint phase credit remain active hard targets.
