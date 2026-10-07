# WP07 actual polynomial Poisson quarter equation — 2026-10-07

Goal ACTIVE, WP07 remains OPEN. Current turn PROGRESS, classical BRIDGE / REDISCOVERED. Previous checkpoint `mem:research/weil-work-07-poisson-smooth-2026-10-07`; earlier exact actual Maass packet in `mem:research/weil-work-07-maass-defect-2026-10-07`.

## Rules and scope
Reapply hgtl7 EVERY turn. Corpus/current primary sources, exact bold conjecture + competitor, attack verdict, paper proof before Lean, formal checks, anti-theatre5 + anti-laziness4 posted, continue. No numerical computations, full/umbrella build, resource hacks, commit/push. One foreground Lean process at a time; final direct `lake --old env lean <module>` from cwd formal (root cwd cannot resolve imports). Own WP07 card/results and WeilWorkHigherDenominator*.lean. Minimal umbrella imports authorized by user, preserve concurrent edits. No subagents authorized. update_plan unavailable, card holds plan. Architecture/testing docs absent. Serena list_memories(topic) empty, explicit reads work; Lean symbol support unavailable. Resolve filenames with rg --files, not namespace guesses.

## New checked modules (namespace RHTower.WeilHigherDenominator)
1. formal/GaloisForLFunctions/RHTower/WeilWorkHigherDenominatorWeightedQuarter.lean, ~119 lines. Imports WeightedIntegral and MaassAxisUniqueContinuation. Public def compactParameterDir v F p := compactParameterPartial F p v. V open, K compact subsetV, gamma continuous intoK, fixed real integrable weightw. F:CxC->C jointC∞ on upperxV.
Public five:
- contDiffOn_compactParameterDir: directional family C∞joint.
- compactParameterDir_eq_dirD: exact actual fiber directional derivative.
- dirD_weighted_compact_parameter: actual dirD integral = integral weighted partial.
- dirD_dirD_weighted_compact_parameter: mixed actual second directional derivative integral = integral second fiber derivative.
- quarterDefect_weighted_compact_parameter: actual quarter operator commutes with integral.
Private partial_smooth uses fderiv_of_isOpen m=infty then clm_comp. ContinuousLinearMap.integral_apply with weighted integrability moves evaluation. dirD_congr on open upper pays second derivative; integrable first/second joint families follow compactbounds. Quarter weight is spatially fixed under t-integral.

2. formal/GaloisForLFunctions/RHTower/WeilWorkHigherDenominatorPoissonQuarter.lean, ~191 lines. Imports WeightedQuarter, PoissonSmooth, MaassConverseAutomorphy. Public four:
- quarterDefect_comp_real_translate: real translation preserves quarter PDE, using existing holomorphic Laplacian chain rule with derivative1 and unchanged imaginary part.
- contDiffOn_projectivePoissonMode: fulljoint kernel A(z,c)=sqrt(Imz)*projectivePoissonKernel z c, C∞ upperxpuncturedC.
- quarterDefect_projectivePoissonMode(c:C)(hz:zinupper): everyc givesPDE, even0 givesidentically0. No cnonzero premise needed here (joint smoothness stillpunctured).
- quarterDefect_polynomialPolarMode(hρ0:0<ρ.re)(hρ1:ρ.re<1)(P:C[X])(hz:zinupper): exact actual polynomial mode quarterDefect0.
Private quarter_congr, smooth_real_translate; sqrtHeight_constTerm identifies sqrt(y)=constTerm0 1; sqrtHeight_invS identifies constTerm0 1(invS z)=sqrt(y)/normz. Kernel c.im=0 is inverseabs(c.re)*constTerm0 1; otherwise r=c.re/c.im, kernel= inverseabs(c.im)*constTerm0 1(invS(z+r)). Existing quarterDefect_comp_invS plus realtranslation provePDE. Integrate fullkernel againstreal/imagfixedweights W=P(logabs t)*polarKernelρI. Exact publicfactorization identifiesintegralwithactualmode; quarterlinearity closes. All logarithmic orders retained.

Two owned old modules changed ONLY to expose previously private helpers:
- WeightedIntegral.weighted_parameter_integrable nowpublic (under same include vars, sourceproofunchanged).
- PoissonSmooth.polynomial_polarKernel_projective nowpublic (exactfixedaxisfactorization, sourceproofunchanged).

All FOUR modules final targeted foreground direct `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkHigherDenominatorNAME.olean GaloisForLFunctions/RHTower/WeilWorkHigherDenominatorNAME.lean` exit0/no diagnostics. WeightedIntegral rebuilt afterexposure; WeightedQuarter finalpassafterfix; PoissonSmooth thenPoissonQuarter sequential. Scratch final audit elevenpublic (9new+2exposed) exit0, axioms onlypropext/Classical.choice/Quot.sound. Publiccapstonetypeprinted andAPI probespass. New imports near7118–7119 inRHTower. Scopedwhitespace andforbidden scansclear. Lint exit1 EXACT7 unrelatedunreachable: RHTower WeilWorkDeficitRestrictedXiDensity, WeilWorkSingularArithmeticCauchyReflection; HTGeometry ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. NoWP07error.
All owned builds/search/lint TERMINAL. Scratchcleanup /tmp/wp07-quarter-search.json, /tmp/wp07-analytic-search.json, /tmp/wp07-quarter-names.lean, /tmp/wp07-quarter-final-audit.lean, /tmp/wp07-quarter-lint.log done afterrecord. Leave .oleans. Cardtop/nextentry/log, RESULT,PROOF,EVIDENCE updated. Anti-theatre5/laziness4 posted. No newscienceclaim.

## Lean implementation lessons this turn
- Do not `open Topology` in modules also opening MaassAxisContinuation; upper becomes ambiguous with Topology.upper.
- `laplacian_holomorphic_comp` needs explicit `(g:=fun w:C=>w+(r:C))(z:=z)`; inference otherwise chooses wrongcurriedaddition.
- `dsimp only [Function.comp_def] at hL` before rewriting compositional Laplacian aslambda.
- Change laplacian target explicitly to dirD1dirD1 + dirDI dirDI before simp hquarter; simp transparency will notidentifydefinitionsautomatically.
- Integral.congr_ae pointwise goals retain beta-redexlambdaapplications. `dsimp only` before `congr1` orrw.
- Explicit integrability/ContDiffOn types with lambda `(W t).re/.im` avoid rw mismatch with inferred RCLike.re/im and Pi.add/Pi.smul.
- Actual integrability scalar API is `Integrable.smul c hf`, NOT hf.const_smul. finalscratch verified.
- `simp only [smul_comm]` caused recursion limit; fixed using explicit `smul_comm (quarterWeight z) (w t) (F(z,gamma t))`, no limitsraised.
- Complex normalgebra needs `(c.im:C)!=0` fromofReal_ne_zero.mpr; field_simp[ha'] closed thewholegoal, sofollowing ringwasextraneous.
- ContDiff real rpow implicitexponentneeded `(p:=(1/2:R))`. ofRealCLM composition resolved by convert thenext/simp [Real.sqrt_eq_rpow].

## Current actual-data frontier
C1 nontrivial completecubicdatum -> infinitelymany deficitsordE<ordxi (ONE xi divisor). Competitor finite-deficitnontrivialdatum. Verdict SURVIVES PRELIMINARY ATTACK; no scientificnoveltyestablished. Positive-lineardeficitstrengtheningalsoopen. NoEulerproduct/multiplicativity/coeffgrowth/zetaRH/simplicitypremisesinserted. C1alone NOTfullWP07; infinitebranchremains.
Existing degreeThree_infiniteDeficits_or_maassDefect gives originalcubicdata infinite support OR exactP,H,eps,Q with U(ix)-epsU(i/x)=sumrho rootsP x^(1/2-rho)Qrho(logx), allstrictstrip andnonzeroQ. U=MaassBesselSeries.maassFun(g*mu)(epsa)(epsb), B1=E/(2xi s^2),a=B1(1),b=B1'(1); endpointsalreadycancelled; nofactor1/4. Completedatum eps+ viaCentralExclusion. AxisPolynomial realizesanyQ byactualpolynomialmode. MaassAxisUniqueContinuation.lean:259 eq_zero_of_axis requires C∞,quarterPDE,evenness,zeroaxis,horizontalrealanalyticity. C∞/PDE/evennessforactualmodes PAID. Next horizontalanalyticity, thenmovingboundary andspatialmodularidentities. FiniteBoundary eliminatesinteriorpackets; afterpolesvanish reuseMultiplicity divisor-containmentrigidity. DoNOTrebuilddegree2classification.

## NEXT horizontal analyticity: paper proof COMPLETE in PROOF.md; Lean notstarted
Fixy>0,D={w:C:abs(Imw)<y/2},V=puncturedC. q(w,c)=(w*c.im+c.re)^2+(y*c.im)^2. Re q=(Rew*c.im+c.re)^2+(y^2-Imw^2)c.im^2>0. Forc.im0, c.re!=0; otherwise secondpositive. H=q^(-1/2:C) and H1=-c.im*(w*c.im+c.re)*q^(-3/2:C) jointlycontinuousonDxV and HasDerivAt H H1 inw. Right-halfplane implies slitPlane, so principalcomplexpowerbranchconditionpaid.
Add complex hasDerivAt_weighted_compact_parameter to OWN WeightedIntegral, reusing private parameter_local_bound/parameter_fiber_continuous and publicweighted_parameter_integrable. Inputs ContinuousOn F,F1 UxV and forallx/cpointwise HasDerivAt fiber. localboundF1 gives derivative boundnormw*C, measurableweightedfibers and integrabilityF fromsamecompactargument. Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le returns conjunction (integrable derivative AND HasDerivAt); take .2. C∞realtheorem alone does NOTpayholomorphy.
ApplyrealandimagweightsW0integrable toH. sqrt(y)*(J_ReW+I*J_ImW) holomorphiconD. Atrealx, q is ofReal(projectivePoissonDenom(x+iy)c), Complex.ofReal_cpow identifiesbranchwithrealK. Public polynomial_polarKernel_projective identifiesactualmode. DifferentiableOn.analyticAt(openmemnhds), then existing MaassBesselSeries.analyticAt_ofReal_comp (MaassConverseAutomorphy:96) gives AnalyticAtR realrestriction; equalitygivesAnalyticOnNhdR horizontallineuniv.
VerifiedbySOURCEREADS thisturn (must /tmpLeanprobe beforeuse): ParametricIntegral.lean:288 theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le; Pow/Deriv.lean:218 HasDerivAt.cpow_const takes h0:f xinslitPlane, derivative c*f x^(c-1)*f'; Pow/Continuity.lean:132 ContinuousOn.cpow_const hf (forallains,f ainslitPlane); Complex.Basic.lean:637 slitPlane={z|0<z.re OR z.im!=0}; Pow/Real.lean:282 Complex.ofReal_cpow(hx:0<=x)(y:R):ofReal(x^y)=(x:C)^(y:C); Analytic/Constructions.lean:818 AnalyticAt.restrictScalars; existing Maass analyticAt_ofReal_comp wrapsrestrict+ofRealCLM.analyticAt.

Movingboundarypaperplan retained: W=abs(t)^-rho P(logabs t), x->x0>0,y->0+. SubtractW(x) on|t-x|<=eta away0, localLipschitzremainder bounded, exteriorcommonintegrablemajorant. Integral=2W(x)arsinh(eta/y)+O(1) uniformlyx; /logy -> -2W(x0). Modularimag y/|cz+d|² logs differbounded, sqrtfactorcontinuous. Fixedx1boundarytheorem NOTenough.

## Search/source audit
Deepquery Poisson kernel quarter eigenfunction derivative weighted integral analytic: exit0 partialtrue, semanticunavailable, backgroundrefreshincomplete, rerankdeadline. 68464filesinventorycomplete; compilercompiled_snapshot43,error2,not_applicable11080,pending51986,stale2660,stale_snapshot38,umbrella_source_only1,unavailable2654. All20candidate20source1ingredient0ideasinspected. ProposedharmonicPoissonreceiversnotquarter. Additionaldeepanalytic integral complex parameter dominated derivative: partialtrue, coveragependinggeneration1279981,rerankdeadline,20candidate20source0ingredient0ideasread; segmentintegration/L2Cauchydifferentrequirements. Noabsenceclaim.
Currentprimary https://people.mpim-bonn.mpg.de/zagier/files/tex/PeriodFunctions4MaassWaveForms/pfmw-coh-subm-feb13.pdf section2.3(2.30),Theorem2.1 confirmsclassicalparent. https://arxiv.org/html/1910.02821v5 theorem3.1/3.3 lemma3.5 andhttps://arxiv.org/html/1809.06586 parent: twists/coeffbounds remainunpaid. PDEparameterherefixed1/2;rho labelsboundaryhomogeneity,notPDEeigenparameter.
