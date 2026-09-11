# FZZ-P higher cleared source, Gamma unit and actual jets — 2026-09-11

RH UNPROVED. User /goal active, no budget. No subagents. Cwd /Users/michael/Documents/code/hgt.

## Latest user instruction
User explicitly said “stop the #print axioms theatre”. Acknowledged. DO NOT RUN OR GENERATE ANY FURTHER #print axioms audits. This overrides earlier audit instructions. All later work uses mathematical scratch, targeted final leaf builds and formal lint only.

## Current state (authoritative)
All EIGHT GammaUnit/rational/actual-source jets are closed, promoted, wired, final leaf/lint passed. No process remains for that prior turn.
NEW active continuation now attacks original cubic finite-part extraction. See mem:rh/fzz_cubic_finite_part_extraction_2026_09_11 for current authoritative state. Three original local/plane remainder comparison statements passed scratch24294. Combined five statements including H_ab=64FP-6912pi and FP=-84pi are checking in session34749; poll that handle, not older ones. No new extraction repo leaf yet. Current scratch /tmp/fzzp_cubic_finite_part_value.lean. Goal active/RH unproved; marked extraction/normalization/phase/full Ward remain open. NO further #print axioms audits.

## Rules
One owned foreground Lean at a time. Development lake env lean /tmp/x.lean. Final lake build exact leaf only. No umbrella/full build. Wire completed modules. No computations/numerical experiments, no sorry/admit/axiom/opaque/unsafe. No more #print axioms. No commits/push/subagents. Preserve concurrent edits, including frontier/umbrella. Read before edits; >500line slices. In cwd formal/, DO NOT prepend formal/ to relative paths. Session init done previously; no applicable skill used.
Every turn state chain, hard gaps, progress, next mathematical attack. Commentary <=60s.
Search current whole corpus hybrid/deep/method + broad recent arXiv, not training recollection.
STATUS contains only audited route-independent Must/Cannot knowledge; current Gamma unit is route-specific, no new STATUS entry needed.

## Proof chain
Fixed theta/FZZ source -> complete integrated mixed replica-momentum Ward law in independent phase frame -> balanced external-Gamma vacuum-delay saturation -> linear replica passivity -> Re rho=1/2 -> RH.
Closed now: higher local fifth remainder, full six-term restoration, complete explicitly pole-cleared original source/Gamma equality on full domain and all cleared mixed jets, exact local rational*Gamma-unit factorization, unit flatness through order2.
Open: original unmarked/marked finite-part cutoff extraction; current exact cleared jet values being formalized; screening-count continuation, full physical normalization, nonzero modes/couplings, independent phase frame, full mixed Ward producer.
Keep Fourier p vs positive-delay Mellin s, reflected momentum product vs winding sum, effective vs physical coupling, worldsheet-position vs target-radial vs delay cutoffs distinct.

## TEN closed higher source/Gamma theorems
Module formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningGammaContinuation.lean (~616lines), umbrella wired.
249 fzzScreeningHigherClearedSource_symm
256 fzzScreeningHigherClearedSource_analytic_left
263 fzzScreeningHigherClearedSource_analytic_right
365 fzzScreeningHigherClearedSource_original
373 fzzScreeningHigherClearedSource_pole_values
535 fzzScreeningHigherPower_chamber
551 fzzScreeningHigherClearedSource_eq_gamma
560 fzzScreeningHigherPower_chart_iff
599 fzzScreeningHigherClearedSource_mixed_jet
608 fzzScreeningHigherClearedSource_cubic_mixed_jet
A(alpha)=(alpha+2)(alpha+4)(alpha+6).
ClearedRadial k0=(alpha+4)(alpha+6)R^(alpha+2), k1=(alpha+2)(alpha+6)R^(alpha+4), k2=(alpha+2)(alpha+4)R^(alpha+6), k>=3=Aalpha R^(alpha+2k+2)/(alpha+2k+2), R=1/2.
ClearedCounterterm=2pi sum k0..5 c_k(beta)*ClearedRadial(alpha,k).
H=Aalpha*Abeta*(I5(alpha,beta)+I5(beta,alpha)+originalExterior(alpha,beta))+Abeta*CTclear(alpha,beta)+Aalpha*CTclear(beta,alpha).
Clears before evaluating, not multiplying a totalized division at pole.
Gamma=64pi Gamma(-alpha/2-beta/2-1)Gamma(4+alpha/2)Gamma(4+beta/2)*invGamma(-alpha/2)*invGamma(-beta/2)*invGamma(2+alpha/2+beta/2).
Full D: alpha,beta>-8, alpha+beta<-2.
Onto chart A(u,v)=-8+14expu/(1+expu+expv), B symmetric; inverse log((alpha+8)/(-2-alpha-beta)).
Pole values H(-2,beta)=16pi Abeta; H(-4,beta)=-8pi c1beta Abeta; H(-6,beta)=16pi c2beta Abeta.
c1=beta²/4, c2=beta²(beta-2)²/64.
Proof: local analytic lifts+actual exterior; original Beta integral + three Gamma shifts each; first slice fixed -2<beta<0, second fixed alpha<-1 with beta anchor -1; reflection covers D. Local equality gives arbitrary mixed derivatives, not original FP values.
Checks: scratch24211 exit0 (removed3 unreachable ring before promotion); leaf18967 exit0 331s/8846jobs clean new leaf; global lint63883 exit0; last historical audit90541 completed before user ban, std3 only. DO NOT repeat.
Logs /tmp/fzzp-higher-cleared-source-scratch.log, /tmp/fzzp-higher-screening-gamma-build.log, -lint.log, historical -axioms.log.

## FOUR closed Gamma-unit/factorization theorems
Module formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningGammaUnit.lean, umbrella wired after GammaContinuation.
fzzScreeningHigherGammaUnit_mixed_second_zero
fzzScreeningHigherGammaUnit_axis_jets
fzzScreeningHigherClearedGamma_cubic_factorization
fzzScreeningHigherClearedSource_cubic_factorization
a=alpha+6,b=beta+6,v=(a+b)/2.
L(t)=log Gamma(1+t)-log Gamma(1-t), odd; analytic for -1<t<1.
LogUnit=L(a/2)+L(b/2)-L(v), ExpUnit=exp(LogUnit).
U=Gamma(1-v)Gamma(1+a/2)Gamma(1+b/2)/(Gamma(1+v)Gamma(1-a/2)Gamma(1-b/2)).
U=ExpUnit for |a|,|b|<1/2 by positive Gamma.
L' even and L''0=0 from deriv_comp_neg. Unit axes identically1 locally; pure first/second jets0; mixed second0 via Ub(a,0)=(L'0-L'(a/2))/2.
Q=64pi*v*((v-1)(v-2)(v-3)(v-4))²/((1-a/2)(2-a/2)(1-b/2)(2-b/2)).
H(-6+a,-6+b)=Q(a,b)U(a,b) as actual source germs, including v=0.
Reciprocal recurrence all s uses Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (Gamma/Beta501), transfer Real via Gamma_ofReal and exact_mod_cast. Positive numerator shifts2/4.
Checks: scratch93001 exit0; targeted leaf3846 exit0 (8847jobs, tactic-style warnings); global lint5144 exit0. No axioms run. Logs /tmp/fzzp-higher-gamma-unit-scratch.log, -build.log, -lint.log.
The module has now been expanded to EIGHT closed public statements (the original four, two rational jets and two actual source jets). Combined scratch1315 and final leaf81155/global lint42385 passed. Do not repeat these checks without new proof changes. No extra umbrella import needed.

## TWO rational jets already clean scratch
/tmp/fzzp_higher_rational_jets.lean, session60966 exit0, log /tmp/fzzp-higher-rational-jets-scratch.log empty.
Public fzzScreeningHigherGammaRational_mixed_second = -12288pi.
Public fzzScreeningHigherGammaRational_mixed_third = 16176pi.
These are now promoted in the same GammaUnit repo module at lines367 and376, not a separate module.
Private decomposition P(t)=(t-1)(t-2)(t-3)(t-4), P1=4t³-30t²+70t-50, P2=12t²-60t+70.
F=tP²; F1=P²+2tPP1; F2=4PP1+2t(P1²+PP2).
D=(1-t/2)(2-t/2),D1=-3/2+t/2,G=1/D,G1=-D1/D².
Q=64pi F((a+b)/2)G(a)G(b).
B(a)=Q_b(a,0)=64pi G(a)*(F1(a/2)/4+3F(a/2)/8).
hB all |a|<1; hB1 at0=16176pi.
F0=0,F'0=576,F''0=-4800,F'''0=25080,G0=1/2,G'0=3/8,G''0=7/16.
All exact chain/product/quotient proofs, no numerical computation.

## TWO actual source jets CLOSED
fzzScreeningHigherClearedSource_cubic_second_value:
deriv (fun a => deriv (fun b => H(-6+a,-6+b))0)0=-12288pi.
fzzScreeningHigherClearedSource_cubic_third_value:
deriv(deriv(fun a=>deriv(fun b=>H(-6+a,-6+b))0))0=16176pi.
Combined scratch uses private unit lemmas because in same module. It promotes rational_right into rational_right_hasDeriv and keeps derivative wrapper.
W(a)=(L'0-L'(a/2))/2; W1=-L''(a/2)/4; W0=W10=0.
X(a)=Q(a,0),X0=0, explicit X1.
C=XW,C1=X1W+XW1. hC1 at0=0 from product derivative and zeros, using local analyticity to admit W1 derivative.
Factorization.curry_nhds gives nested germ. Actual U derivative on b-axis follows gamma_unit_eq_exp and log_unit_hasDeriv_right.
sourceRight(a)=H_b(-6+a,-6) = B(a)+C(a) as germs.
Then source second/third are B'0/B''0 since C'0=C''0=0.
Mathlib Filter.Eventually.curry_nhds source Topology/Constructions/SumProd341 verified.
Failed scratch31206 had newline-dot syntax and function notation mismatch. Scratch55352 reduced this to hC1 function/instance elaboration. The successful1315 proof explicitly changes the HasDerivAt target to the real lambda and applies h.congr_deriv. Explicit fun_add/fun_mul handles pointwise lambdas. All eight now built and linted; actual source values at lines450/460. No remaining proof error.
Do not claim original FP values from these alone.

## Next ORIGINAL finite-part extraction
Paper targets, NOT Lean proven:
H_ab=64FP-6912pi.
H_aab=128markedFP-96FP+10368pi.
With sourcejet values would give FP=-84pi, markedFP=-141pi/8, ratio47/224, STILL CONJECTURES until original cutoff bridge.
A(-6+a)=aB(a), B(a)=(a-4)(a-2)=8-6a+a² (different B notation from rational scratch).
Normalized source J=H/(B(a)B(b)) = ab*S(a,b)+2pi[b*c2(-6+b)*R^a+a*c2(-6+a)*R^b], with S original remainders+exterior+all noncollision finite radial terms.
Then J_ab=FP, J_aab=2markedFP. Clearing factor product derivatives give constants above: B0=8,B'0=-6,B''0=2,c2(-6)=36,c2'(-6)=-21.
Original local comparison target newly recorded:
full quintic angular coefficients at -6 = (1,9,36,-460,-405,-21).
Average integrable R5(-6,-6) differs from admitted cubic angular remainder by 460+405r²+21r⁴.
Thus proposed exact original half-disk comparison:
CubicLocalFP = integral_ball R5(-6,-6) -10993pi/64 +72pi log(1/2).
Reason integrated finite tail =8177pi/64, original primitive P(R)=-22+36logR times2pi.
Needs polar admission/Fubini and cutoff uniqueness, not assigning Gamma value.
Original CubicLocalFP defined FZZCigarCubicScreeningCutoff27; original zero cutoff163 and independent plane cutoff289.
HigherRestoration public Taylor circleAverage193; can adapt its polar indicator231-267 to admitted R5. Keep actual exterior.
Marked adds distinct original singular/regular logarithmic corrections.
Existing source-continuation PRIVATE exterior_analytic160 + fifth source analyticity already prove needed local regularity if extending there; avoid blind duplicate generic infrastructure.
Refined unmarked paper target: H_ab=64*Rsum+16*deriv(fun alpha=>ClearedCounterterm(alpha,-6))(-6), where Rsum=2I5+originalExterior. Six radial derivatives weighted by c=(-6) give CT'= -14449pi/8+576pi logR. Thus H_ab=64Rsum-28898pi+9216pi logR. Combined local comparison gives FP=Rsum-10993pi/32+144pi logR, hence H_ab=64FP-6912pi. No c2 derivative needed for unmarked extraction. Need exact separate analyticity of remainder/exterior and counterterms before product rules. Counterterm radial derivative values at -6: k0=-32, k1=-16, k2=-6+8logR, k3=1,k4=1/8,k5=1/48. These are paper targets, not new Lean declarations.
Original local polar admission can use public fzzScreeningFifthTaylor_uniform_remainder163 to bound r*R5(circle) by C*r on r in(0,1/2), then product L1 before Fubini. Read HigherRestoration202-230 for integrable majorant product/restrict argument and231-280 for indicator polar/angle transport. Public HigherAngular_three_remainder278 uses radius(1+expu)^-1; invert u=log((1-r)/r). Public cubic remainder integrability294 and explicit local cutoff limit already available. Mathlib Pochhammer.descPochhammer_succ_eval348 inspected for c0..c5 exact specialization. No new extraction scratch written yet.

## Current docs
Card docs/drafts/pipeline/1-in-progress/fzz-p-higher-screening-collisions.md: whole source10 finalized ~416; Gamma unit/source8 section ~449 finalized with scratch, final targeted build and lint passed. Exact Q/U/sourcejet values are proved; original FP/marked values and cutoff comparisons explicitly remain paper targets. Includes local10993pi/64 comparison, six radial derivative14449pi/8 target, current-corpus and recent-paper intake.
Frontier docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md: FZZ source10 paragraph~1682 followed by closed sourcejet8 paragraph. Concurrent edits move lines; use text anchors, preserve other work.
STATUS prior finite-boundary fact cites source10. No new route-independent fact from GammaUnit8; do not add route-specific formulas there.

## Searches completed
All tools terminal; inspect coverage, no absence claims.
1 /tmp/fzzp-higher-source-continuation-methods.json deep/all180 partial844002 no errors proposedunverified Gamma recurrence. All20+20 names inspected. Read SeamTwoLatticesArchimedeanResidue81.
2 /tmp/fzzp-higher-source-finite-jet-methods.json hybrid/all180 partial857720 semantic/refresh incomplete. All20+20. Read GammaDifferentialFE760 + AdS2RenormalizedScalarClockParity467.
3 /tmp/fzzp-higher-gamma-unit-methods.json deep/all180 partial869214 semantic/Qdrant deadlines. All20+20. Read SlepianKernelScaledFubini555-590 derivative parity, PrimeIsingTreeCentralMassFloorLaw171, ReflectedBiHeatFullWindowSingularFinitePart352-407, ThetaCuspFullReflectionSixthModularSeam135-178.
4 /tmp/fzzp-higher-mixed-product-methods.json deep/all180 partial873258 semantic/rerank runtime deadlines, no ingredient/proofidea. All20+20. Read HedenmalmCenterMixedLocalThreePoint1-108 and MixedFourthJetCusp1-94 (.congr_deriv, explicit product rules), ThetaCuspHawkingBMMixedCorrectedSource1-108, SignedReflectionParity126-153 (entire premise NOT used).
5 /tmp/fzzp-original-cutoff-jet-methods.json deep180 partial873783 no errors, semanticindex/source refresh incomplete. All20candidate+20method names and generated proofidea/ingredient inspected. Proposed finite gap pole definitions from LocalExtensionQuadraticRateRigidity34-45 do NOT transfer to original cutoff (actual source20-72 read). SelbergScatteringCuspSubtraction45-80 retains principal subtraction but no cubic bridge. Reads original CubicScreeningCutoff1-200,289-313 and CubicMarked1-100. Existing lower FZZCigarContinuedScreeningMark1-185 signed-exponential original-mark derivative mechanism inspected; high regular mark needs full Taylor derivative and original cutoff.
Broad arXiv words: resonance,sewing,residue,monodromy,fusion,coaction,factorization,cocycle,transgression,renormalization. Some empty/old.
Opened 2608.12816 revisedAug29 overview, no source/Ward theorem; 2006.02257 revised2022 loopgroup Xray simple-surfaces geometric premises not matched.
Opened actual https://arxiv.org/html/2609.07277v1, submittedSept7: Araki entropy RG bounds. Stochastically positive KMS, sharp-time K in L^(2+epsilon), exp integrable, multiscale curvature assumptions. Not matched to fixed FZZ/phase, entropy bound alone not saturation. No imported premise. Documented.

## Prior closed work, do not redo
mem:rh/fzz_higher_screening_taylor_2026_09_11 eight local fifth-remainder/lift analytic statements.
mem:rh/fzz_higher_screening_restoration_2026_09_11 seven full six-term restoration statements.
mem:rh/fzz_higher_marked_angular_2026_09_11 higher angular and original marked/unmarked independent cutoff limits.
All wired and historically built/linted. No new audits requested.
