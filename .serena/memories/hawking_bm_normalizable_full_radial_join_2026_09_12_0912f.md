# HB full normalizable temporal radial join — 2026-09-12, 0912f

Goal ACTIVE and unproved. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Verified result
The complete original normalizable temporal current is now restored over BOTH original radial intervals, with its residue evaluated from the actual source. No source-moment/nonvanishing/regularity hypothesis was inserted. Four new leaves installed, exact-audited, and wired into formal/GaloisForLFunctions/RHTower.lean:
1. RHTower.ThetaCuspHawkingBMTemporalCurrentFundamentalFactor (audit52s):
 physicalTemporalFundamentalAmplitude K = angularSquare * (-2*w0*(physicalAngularParameter²-1/4-2)) * physicalSelfSourceCoefficient * fundamentalSourceMoment(w0,s,a) * clearedOnset(s,w0).
 selfClearedProfile_fundamental; clearedDensityProfile_fundamental_factor F(w0,z)=K*incomingPairingFactor; actual jet coefficient uniqueness; clearedDensityProfile_fundamental_finitePart N_b(w0)=K*incomingNormFinitePart.
2. RHTower.ThetaCuspHawkingBMTemporalOppositeOuterCurrent (22s):
 oppositeTemporalOuterDensity = -1/(2u(u-2s))*angularSquare*(-2u*spin*selfExpression-u*contactExpression)*tortoiseMode false (-u) chi.
 Exact identity with original Jn-Aplus*Ji for t<0; spatial continuity, frequency analyticity, common outer majorant, analytic original oppositeTemporalOuterIntegral through w0. Full self response, all three principals, lift and contact retained.
3. RHTower.ThetaCuspHawkingBMTemporalNormalizableOuterCurrent (74s):
 normalizableTemporalOuterIntegral = original ∫Ioo(T,0) ((R²-1)*continuedPhysicalTimeAction ... true).
 Decomposition theorem (T<0 essential): eventually punctured w0 original outer current integrable and integral=Aplus*compactPart(horizonCoordinate T)/D + oppositeOuterIntegral.
 Original outer residue=compactPart(w0)/physicalSlope. clearedTemporalDensity_fundamental_factor=K*originalnormalizable²; compactPart_fundamental_factor.
 physicalTemporalFundamentalRadialResidue=K*normFinitePart(w0)/physicalSlope.
 physicalTemporalFundamentalRadialResidue_ne_zero_iff (line187): residue≠0 iff K≠0, since original norm and slope nonzero.
4. RHTower.ThetaCuspHawkingBMTemporalNormalizableRadialJoin (36s):
 normalizableTemporalRadialFinitePart = normalizableHorizonFinitePart + originalOuterIntegral at tortoiseOf b.
 normalizableTemporalRadialCutoff = originalhorizoncutoff with three derived counterterms + originalOuterIntegral.
 physicalNormalizableTemporalCurrent_full_radial_restoration_and_residue (line25): actual q branch side a zang determine B>0, B≤half, c0,c1,d, and FOR EVERY 0<b≤B:
 - N_b(w0)+compactPart(b,w0)=K*normFinitePart(w0);
 - (u-w0)*fullRadialFinitePart tends to physicalTemporalFundamentalRadialResidue;
 - eventually punctured u original outer current integrable and original radial cutoff tends to fullRadialFinitePart.
Uses original norm exact common-cutoff join. Does NOT yet prove nonzero K or full angular/action comparison.

Two existing leaves updated, preserving original public theorem statements via thin wrappers:
- TemporalCurrentHorizonRestoration: new physicalTemporalCurrent_horizon_restoration_data retains ∃C≥0 actual uniform quadratic jet on same frequencyball and radius, plus old restoration/residue. Audit6.3s.
- TemporalNormalizableCurrentRestoration: new physicalNormalizableTemporalCurrent_horizon_restoration_data retains same incoming jet with c0,c1 and normalizable d; old theorem unchanged. Audit58s.
This solves previously hidden existential jet witnesses. No second independent endpoint coefficient choice.

## Build/check discipline
All six leaves scratch-checked by lake env lean, then EXACT lake build Module against cached deps in /tmp/hb-audit-0912f. No owned dependency/full/umbrella builds, no resource limit increases, no axioms checks or mathematical computations. Each exact audit only two Lake jobs. Sources plus five artifacts installed safely. All four new imports wired. scripts/formal_tools.py lint PASSED (only pre-existing large-file warnings). Previous seven unreachable-module lint failures are resolved.

Another agent's normalworkspace build PID64727 temporarily removed dependency oleans/ileans. Not started/killed by this work. Immutable cached audit snapshot used until external work completed. Combined import check with concurrent RadialPackage and normalizablehorizon PASSED; prior suspected tortoiseOf_continuousAt namespace clash does NOT block imports.
Concurrent TemporalCurrentRadialLaurent source read; discarded untested duplicate incomingradial draft and built missing opposite outer / normalizable join instead.

All owned Lean/Lake/search processes completed. Scratch files, search JSONs, lint output, audit package and helper removed. No owned processes remained in final ps check. Frontier and universal STATUS untouched. Updated only route card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md and named Lean leaves + RHTower imports.

## Next hard obstacle and positive analytical conjecture
Nonvanishing of actual K / joint survival of physical branch/side family. Remaining factors include original source moment and physicalSelfSourceCoefficient (fourLambda product) plus actual angular pairing. Full angular/action identification, Hawking-clock extinction, RH remain open.

New concrete source-moment reduction candidate recorded on route card, NOT yet Lean-proved:
r=sqrt(1-z), W(r)=(1-r)^w*(1+r)^(2s).
A=(5s²+15s+4)/4.
B=s(s-1)*((s+2)(2s+3)-(w+1)(w+2)/2)/4.
I_n=FP∫0..1 r^n W(r).
M=2a²(A I2+B I4).
d=2s-w, e=w+2s+2.
Derivative of r^n(1-r)^(w+1)(1+r)^(2s+1) gives expected:
d I0-e I1=-1;
n I_(n-1)+d I_n-(n+e)I_(n+1)=0 for n≥1.
I2=((e+d²)I0+d)/(e(e+1)).
I4=((d⁴+(6e+8)d²+3e(e+2))I0+d(d²+5e+8))/(e(e+1)(e+2)(e+3)).
I0=2^(w+2s+1)*FP∫0..half t^w(1-t)^(2s).
FIRST OBLIGATION: transport actual fixed source counterterm under r substitution, and prove recurrence for THAT finite part. Difference between transported leading counterterms should be O(epsilon^(Re w+2)); physical Re w>-2. Don't substitute complete Beta or discard half interval/boundary term.
At matching branch/side: s=2w+1 or2w+2, so W=phi5(r)^w*(1+r)^(2k), phi5=(1-r)(1+r)^4, derivative=(1+r)^3(3-5r). Complementary physical pairings s=-2w-5 or-2w-4. Potential approach: coupled branch/side contiguous relations showing at least one source moment survives, rather than assuming every scalar nonzero.

Corpus searches this turn broad moment, beta, OR quintic/Catalan/Raney/period; deep endpoint/source factorization and deep Mellin/incompleteBeta/IBP mechanism searches. Inspected candidates/sourcearguments/proofideas/ingredientsets. Last deep search PARTIAL (unfinished auxiliary queries), snapshot ~57067files/735514declarations, mostly pending compiler metadata, semanticcoverage unmeasured.
Useful newly inspected source: ThetaCuspHawkingSelfDualGeneralMellinVertex, explicit shifted-complete-Beta recurrence. It does not directly apply to physical half-interval finite part or negative Re parameters. Broader quintic/Catalan results unrelated. Fokas matrix proposed ingredientset didn't give currentendpoint identity.
Broad arXiv transmission/factorization searches no verified June–September2026 matches; opened hep-ph/0109045 but did not use it as premise. No computation.
