# Actual prime-chamber differential system and odd positivity propagation

GOAL ACTIVE: RH neither proved nor disproved. This goal turn made verified progress: 22 public theorems +8 definitions in four finished leaves. No subagents, computations, commits, full/umbrella builds. Prior chain: mem:rh/fixed-exponential-pole-rh-criterion-2026-09-06; prior atom classification: mem:rh/odd-prime-cutoff-and-signed-budget-2026-09-06.

## Full proof chain / open core
Actual all-aperture |C(a)|≤A(a) → square-root bound for P(T)=∫0..T(exp t−ψ(exp t)) → bounded actual unit-Riesz resolvent → mathlib RH, converse closed. NEW full-source propagation inside fixed integer cutoffs: for 2≤a≤b, floor exp(2a)=floor exp(2b), nonnegative actual odd energies at a,b imply strictly positive actual odd energy at every a<c<b. Nonnegativity on entire closed interval iff signs at endpoints. This is NOT actual endpoint positivity. Changed-cutoff boundary handoff, endpoint signs, even sign, and radius<2 remain outside this comparison. Other RH routes unchanged/open.

## Finished files and exact content
All formal/GaloisForLFunctions/RHTower, namespace RHTower, wired after OddPrimeBudget in RHTower.lean.

1 CCMRestrictedWeilPoleBoundaryPrimitives.lean:154lines,4publictheorems,3defs.
L(t)=ccmGammaPoleBoundaryLog(t)=−log(1−exp(−t)). Integrability at0 from admitted screw halfmoment for L(2t), scaling toL(t). Public intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul and intervalIntegrable_ccmGammaPoleBoundaryLog, domain0<T.
B0 extension ccmGammaPoleCrossBoundaryPrimitive(s)=∫0..2s L(t).
B1 extension ccmGammaPoleSelfBoundaryPrimitive(s)=exp(s)/2∫0..2s exp(−t)L(2t)+exp(−s)∫0..2s exp(t)[L(t)−L(2t)/2].
ccmGammaPoleCrossBoundaryMass_eq_primitive and ccmGammaPoleSelfBoundaryMass_eq_primitive identify actual physical masses at EVERY positive aperture. Uses exact B(R,S)=.5L(2R)+L(S)−.5L(2S), no positive-endpoint hypothesis for algebraic decomposition. Reflection/translation cancels doublelog inB0. Weighted translations exact.

2 CCMRestrictedWeilPoleBoundaryDifferential.lean:178lines,6pubtheorems,1def.
hasDerivAt_ccmGammaPoleBoundaryLog: L'=−1/(exp s−1), s>0.
hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive: B0'=2L(2s).
deriv_deriv_ccmGammaPoleCrossBoundaryPrimitive: B0''=−4/(exp(2s)−1).
ccmGammaPoleSelfBoundarySlope def retains two integral responses and both endpoint terms; hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive.
hasDerivAt_ccmGammaPoleSelfBoundarySlope: slope'=B1−4exp(−s)(1+exp(4s))/(exp(4s)−1).
deriv_deriv_ccmGammaPoleSelfBoundaryPrimitive_sub: B1''−B1=same negative rational-exponential forcing.
All ordinary real extensions allow derivatives on positive open domain without any derivative at singular lower endpoint. FTC at2s>0 only. Private left/right responses F,G satisfy F'=F+exp(−s)L(4s), G'=−G+2exp(s)[L(2s)−L(4s)/2]; second cancellation exact.

3 CCMRestrictedWeilPolePrimeChamber.lean:213lines,9pubtheorems,4defs.
ccmWeilPrimeChamberWeight a =W_a=Σ_{2≤n≤floor exp2a}Λn(1+1/n).
Freeze actual arithmetic at aperturea. Prime tent at variable s with same floor =T(a)+2(s−a)W_a. Two prime cumulatives fixed. Define ccmWeilPoleChamberDiagonal a s, ccmWeilPoleChamberCross a s, ccmWeilOddPoleChamber a s=2(Ach−Cch).
Exact actual identifications ccmWeilPoleDiagonal_eq_chamber_of_floor_eq, ccmWeilPoleCross_eq_chamber_of_floor_eq, ccmWeilOddPole_eq_chamber_of_floor_eq. Hypothesis floor(exp2b)=floor(exp2a); conclusion actual entry/energy atb equals corresponding frozen expression atb.
Public differentiableAt for allthreechamberfunctions at everys>0.
Set FA(s)=16cosh s−4exp(−s)−4exp(−s)(1+exp4s)/(exp4s−1), FC(s)=8cosh(2s)+4−4/(exp2s−1).
deriv_deriv_ccmWeilPoleChamberDiagonal_sub: Ach''−Ach=FA.
deriv_deriv_ccmWeilPoleChamberCross: Cch''=FC (universal second derivative; prime tent affine).
deriv_deriv_ccmWeilOddPoleChamber_sub: Ech''−Ech=2[FA−FC+Cch]. Prime dependence survives throughcrossentry, notdiscarded.
Private generic bulkA(αβδs)=αsinh s+βexp s+(2s+δ)exp(−s)+8s sinh s; derivative2−bulkA=−4exp(−s)+16cosh s. bulkC(αβs)=αs+2s²+4sinh²s+β; derivative2=8cosh2s+4. Explicit first slopes support fulljet proof.

4 CCMRestrictedWeilOddPrimeChamberComparison.lean:169lines,3pubtheorems,nodefs.
ccmWeilOddPoleChamber_shifted_second_neg (a b positive) samefloor,2≤b: derivative2ofchambera atb minusvalue<0. Actual proof: B0≤KB≤7 via log2≤1,π<4; κ=−γ−log2π<0 via γ>1/2,π>3;T≥0 ⇒ C≤2b²+4sinh²b+7. Also4/(exp2b−1)≤1, subtractedGammafraction≥0. b²≤2(coshb−1), hencecoshb≥3; hyperbolicidentitiesmakeforcingnegative. No numerical experiment, no RH premise.
Private second_nonneg_of_localMin follows corpus SuzukiInteriorExcursionSpectralTurningPoint.suzukiSecondDeriv_nonpos_of_isLocalMax inminimumorientation: contrarynegative2deriv+firstderiv0 ⇒localmax, combinewithlocalmin ⇒localconstancy ⇒2deriv0. Uses Mathlib DerivativeTest.
Private minimumprinciple: ContinuousOn f Icc, interior f''−f<0, endpoints≥0 ⇒nonnegativeIcc, thenstrictpositiveIoo. Compactminimum existence and local2derivtest givecontradictionatnonpositiveinteriormin.
ccmWeilOddPole_pos_between_same_cutoff: actualsourceendpointsigns propagate STRICTinside, lefta≥2, samefloor, a<c<b.
ccmWeilOddPole_nonneg_interval_iff_endpoints: exactactualsourceequivalence for a≤b,a≥2,samefloor. Integerfloor monotonicity guarantees every intermediate radius matchescutoff. Does NOT yet include next right wall wherefloorchanges!

## Cards and docs
Formalcard docs/drafts/pipeline/3-formalized/weil-pole-prime-chamber-comparison.md includesclosedpaperproof, exactformulas, limits,audit. Initial1-in-progresscard moved/replaced, nostalecopy.
Mainactivecard1-in-progress/weil-two-pole-compression-prime-error.md has closedintervalcomparison andliveobligation4 toextendthroughnextprimeentrywhereenteringatomenergyzero,thencontrolactualendpointvalues.
FrontierRouteO current-stateparagraph Full odd-source propagation inside a fixed prime cutoff; existingroutespreserved.
UniversalSTATUS existing Cannot propagate positivity from signs of newly entering prime terms entry strengthened withtrue full-energy comparison andremainingendpointgap. Failedshortcut5-failed/weil-odd-prime-permanent-entry-sign.md strengthenedpositive survivor withnewcomparisonlink; originalcutoff/budgetaudit separate.

## Verification and process state
Scratch /tmp/hgt-pole-chamber.mNv6O2/{API,Primitives,Differential,Chamber,Comparison,Axioms}.lean. All passed lake env lean foreground. Named leaf final builds passed ~7.8/11/8.6/10s via lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>. Onlynewneededleaves; nofull/umbrella build. Axioms scratch30declarations EXACT[propext,Classical.choice,Quot.sound]. Formal lintPASS(existinglargefilewarnings), gitdiff--checkPASS. Processinspection found NO LeanorLakeprocess. Researchindexrefreshed+newchamberdeclarationsfound withresearch'chamber odd' --moduleCCMRestrictedWeil. No liveownedprocess. Foreign treechanges present/preserved (other tasks modifiedHTGeometryetc).

## Next mathematical actions
1 Extend fixed-cutoff model to the next cutoff endpoint b=.5log(N+1): newatom self andcrossvalues0, so actualmatrix should equalincomingchambermodel even thoughfloorchanges. Needprove exact cumulative jumps andzero-entry cancellation oroperatorform equivalent. Then positivity inside eachclosedchamber could reduce to actual prime-entry endpoint signs plusbasea=2. Currenttheorem doesnotperformthat handoff.
2 ActualendpointsignsremainRH-bearing arithmeticproblem, andevenparitystillpartoftheproved RHcriterion. Do notpretendintervalpropagationclosesRH.
3 Read-onlyresearchfound one-sidedChebyshev RHtheorems in CCMSharpPrimeWindowSquareSampling / PrimeReduction and thegenericCCMUnitRieszVirialConnector. Onlysearchresults viewed for those currentturn; do NOTassume theyapply. Mathematicalcandidate: oddnonneg alone gives C≤A≤Kexp(a), henceone-sidedupperboundonlogChebyshevprimitive. WhetherthisalreadyforcesRH needsactualLandauconnector proof, not training-memoryclaim. Existingfixed-stateRouteU firstfailurelocalizationdoesnotapplyautomaticallytomovingpoles.

## Lean pitfalls
Functions/namespace signaturesverifiedTHISscratch. HasDerivAt.congr_of_eventuallyEq expects newfunction=ᶠ oldfunction; orientation matters. convert! hd using1 usually solvesfunctionequalityalready; onlycoefficientgoalremains, so extrarflbulletcauseserrors. Use simp only[id_eq] before ring whenproductscontain id s. Measurable L followsunfold+fun_prop; AEStronglyMeasurable fun_prop alone cannotdiscoverlog, use (by...:Measurable...).aestronglyMeasurable. GenericFTC helpertakesMeasurable f, uses hm.stronglyMeasurable.stronglyMeasurableAtFilter; ContinuousAt.stronglyMeasurableAtFilter requires continuityonanopenset, notonepoint. Integral_add/sub with functional .sub requires simplify Pi.sub_apply in intermediatetheorem; broadmul_add rewritesinside logarguments andbreaksmatching, usepointwiseouteridentity. Forrationalforcingnormalize exp4s andexp2s in nonzero hypothesesANDgoal, simp exp_add, exp_neg, ring_nf athypothesesgoalbeforefield_simp; otherwisefield_simpnormalizes denominators beyondcache. Writecomparisonoperatorswithspaces: unspaced ≤s and <m arecapturedbyimportednotation (<m=Matroidstrictminor). Standardγlowerboundis Real.one_half_lt_eulerMascheroniConstant,notnonnegname. Avoid rerunningpassedtestswithoutnewchange.