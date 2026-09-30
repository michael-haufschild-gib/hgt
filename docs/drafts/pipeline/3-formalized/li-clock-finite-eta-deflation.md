# Exact finite eta deflation exposes required clock cancellation

- **ID:** LI-CLOCK-FINITE-ETA-DEFLATION
- **Stage:** 3-formalized; independent hostile paper and interface audits PASS; 12 public declarations final
- **Type:** THEOREM; exact decomposition and positive cancellation survivor
- **Parent:** [finite eta orientation window](../1-in-progress/li-clock-finite-eta-orientation-window.md)

## Exact arithmetic decomposition

Installed `pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition` (`RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition.lean:98`) gives E_N=sL_N, retaining every positive logarithmic interval. Put C=s(1-s)Gamma_R/d and H_N=C E_N=s(C L_N). On a regular central disk, finite eta nonzero and 0<Re(s)<1 allow logarithmic differentiation:

`T_N(z)=i/s+T_def,N(z)=1/(z-i/2)+T_def,N(z)`.

The same negative trace sine contour, with 0<r<1/2, gives at every complex clock

`F_N(t)=-2sinh(2t)+F_def,N(t)`.

Odd pole derivatives are `(-1)^j*4^(j+1)*(2j+1)!`; squared odd factorial convention in `LiClockCentralTraceSineReflection.lean:131` gives exactly -2sinh(2t). Uniform geometric/sine convergence justifies all terms. No parity or zero center assumption is imposed.

## Domain and filled completion (paper endpoint interpretation)

N=0 has E_0=L_0=0 and cannot use logarithmic splitting. Regular finite eta hypothesis excludes it. For N>0, L_N(0)>0. Literal totalized C(0)=0; use Ctilde=2pi(1-s)Gamma_R(s+2)/d(s), from `gammaReal_shift_two` (`ArchimedeanGamma.lean:29`). Ctilde(0)=-2, C=Ctilde off0 near0; H_N=s*Ctilde*L_N agrees even at0. Thus literal H_N has a simple zero at0, while filled deflated completion is a unit there. Do not confuse filled deflation with totalized H_N(0)/0.

## Strongest calibrated positive survivor

Once finite denominator threshold holds, exact error gives

`|F_def,N(t)-2sinh(2t)-F_C(t)|<=B_N sinh(|t|/r)`.

For real0<=t<=20, q=1051/2184 and A=xiShiftAbsoluteMass0>0,

`Re F_def,N(t)>=2sinh(2t)+[qA-B_N cosh(20/r)/r]t`.

Therefore every fixed theta in(0,1) yields eventual uniform `F_def,N(t)>=2sinh(2t)+theta*qA*t` on0<t<=20. Responses are real by anti-Schwarz reflection, not finite functional equation. This is exact compensating cancellation, not full-clock sign.

## Audit and formal closure

Producer and independent pole-source audits PASS after explicit regular-domain and filled-C-at0 corrections. Root checked finite completion/source analytic APIs and generic squared-factorial contour convention. Independent documented research partialdeadline/reranking generation1146229pending, useful source-only hits. Partition, Gamma recurrence and generic contour mechanisms preexist; source-specific composition has no public/world novelty claim.

The final leaf proves exact elementary pole contour, completed finite Laplace logarithmic splitting and source-specific decomposition. Final literal finite approximation supplies the complete calibrated error and positive cancellation bound. Named build, final exact source and all 12 public axiom audits passed.

Remaining burden is independent `F_def,N(t)>=2sinh(2t)` on growing window. Isolated negative pole contributes no full fixed-N sign or obstruction scale. No route retired.

## Log

- 2026-09-30 — Recorded exact independently audited positive survivor before Lean. All-complex decomposition and calibrated cancellation are paper-closed; implementation pending.

- 2026-09-30 01:27 UTC — Source-defined `LiClockPairedEtaFiniteDeflation.lean` passed complete scratch and named build; all 12 public declarations have foundation-only axioms. Final exact check running. Public decomposition needs eta nonzero only on integration circle and allows any regular 0<r<1/2. Calibrated actual-radius theorem retains complete complex error, explicit qA-minus-error coefficient and every eventual theta fraction on 0<=t<=20. Filled completion/simple-zero endpoint interpretation above remains paper-only; formal source is literal C times L_N within regular strip. No endpoint totalization, fixed-N full-clock sign or growing-window obstruction claimed.

- 2026-09-30 01:32 UTC — FINAL: One leaf: LiClockPairedEtaFiniteDeflation (12). Source-defined literal C times L_N trace, full regular-strip split, exact all-complex negative-two-sinh pole contour and finite decomposition, real response and calibrated complex error/positive compensation are Lean-closed. Sphere-only nonvanishing suffices for decomposition at any 0<r<1/2; actual calibration uses its quantified smaller radius. Filled Gamma endpoint interpretation remains paper-only. Every public declaration passed named build, final exact source and axiom audit, with only [propext, Classical.choice, Quot.sound]. Root spot-check complete; umbrella wiring complete. No growing-window source sign, converse, RH proof or route retirement claimed.

- 2026-09-30 01:37 UTC — Index gate exit0 (/tmp/hgt-li-clock-negative-deflation-index.log), four changed indexed sources. Authoritative lint exit1 (/tmp/hgt-li-clock-negative-deflation-lint.log): exactly19 unrelated unreachable modules, no proof-debt errors; all five new leaves wired. Additional external reachability errors since prior15 gate are DeBruijnTopZeroVelocity, WeilDeviationBumps, WeilDeviationFejerTest and WeilDeviationPacketLimit. No whole-tree green claim.
