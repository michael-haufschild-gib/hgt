# APT critical kernel checkpoint, 2026-10-19

Active unbudgeted goal: 100 significant novel native APT contributions from attachment `/Users/michael/.codex/attachments/4185f2f3-69a7-4408-a6e5-51260ec1f59e/pasted-text-1.txt` (read earlier). Accepted 0/100. Goal active: do not mark complete/blocked/paused, meaningful progress continues. Latest user: use corpus research tool, do not miss existing work. Extensively obeyed. User forbids hgtl7, numerical experiments/computations (ordinary exact Lean proof arithmetic allowed), axioms/unsafe/sorries, heartbeat increases, full builds, commits/pushes. README read-only. No subagents. One owned foreground Lean/build at a time; never launch another while current owned build runs. Preserve foreign worktree writers. Session init/manual/memories done; architecture/testing docs absent. Serena lacks Lean symbol support; rg/apply_patch fallback documented.

## Immediate live job: recover before starting Lean
- Owned targeted build session **30090**, shell PID30588, lake PID**30596**:
  `lake build GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeContinuousKernel`
  cwd formal, log `/tmp/apt_critical_prime_continuous_kernel_build.log`, status same stem.
  This leaf target is rebuilding a long pre-existing dependency chain (17870 jobs total, most replayed). Last observed progress17755/17870. No errors observed yet. Many existing dependency builds take~100s amid concurrent work. It is NOT an umbrella/full build. Do not launch another Lean/check or mutate current target before it exits. Do not dump its huge warning-replay log; inspect error lines, completion and small tail.
- Every corpus search, index, lint job below has finished and been screened. No other owned jobs live.

## Completed support leaves: do not retest unchanged
1. `formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeCumulativeCharge.lean`248lines11public, umbrella imported.
H_N=sum1<=m<=N A(m)/m^3: zero iffN<=1, negative iff2<=N<=4, positive iffN>=5, H_N>log2/150 forN>=5. Odd-prime charge=p logp, |A(m)|<=m logm, absolute cubic summability, uniform absolute cumulative bound, convergence, positive limit margin. Scratch/target115s/directactual/all11axioms/index/catalog checks passed. Only propext, Classical.choice, Quot.sound. Logs/status0 `/tmp/apt_critical_cumulative_charge{,_build,_actual,_actual_axioms,_index}`.
2. `FactorialCriticalPrimeKernelDensity.lean`339lines17public, umbrella imported. Gamma(u)=u^(-2)*(1-cos(2*pi*u/12)); D(u)=Gamma(u)H_floor(u); P=HTGeometry.realL1Periodization D; Rraw=(P(t)+P(1-t))/2. Proved Qperiodic/reflection, J_m=m*integral_(u>m)Gamma Q forpositive m, closed-tail floor series exact at ALLu, integrabilityD andD*Q, complete actual translated prime form=(4/pi^4)integral_R DQ=(4/pi^4)integral_Ioc01 P Q=(4/pi^4)integral_Ioc01 Rraw Q. Uses realL1Periodization zero Fourier coefficient and existing Fubini tools. All scratch/target16s/directactual/17axioms/indexcatalog checks passed standard3axioms. Logs/status0 `/tmp/apt_critical_prime_kernel_density{,_build,_actual,_actual_axioms,_index}`.
Historical lint for these superseded by latest below. All completed scratch sources for those two leaves and old fragments DELETED; logs/searchJSON retained.
Prior translated package4leaves+2wrappers18exports fullyaudited at `docs/drafts/pipeline/3-formalized/apt-critical-translated-prime-form-2026-10-19.md`. Preserve; no repeat checks.

## Newly installed continuous leaf, audit PENDING BUILD
`formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeContinuousKernel.lean`,187lines8public; umbrella import added immediately after KernelDensity.
Scratch `/tmp/apt_critical_prime_continuous_kernel.lean` passed exit0 empty log after adding `dsimp only` before two rewrites. First failure only beta reductions; all API probes compiled. New actual source is scratch minus APIexample plus moduledoc.
B=sum |A|/m^3; K(t)=sum_k H_(k+1)Gamma(k+1+t), t in[0,1]. Uniform majorant2B/(k+1)^2 gives continuousOn_tsum via existing HTGeometry.summable_inv_sq_shift. Split integer sum via tsum_of_nat_of_neg_add_one; negative indices and index0 vanish, floor(j+t)=j on0<t<1, soP=K there. Rcont=(K(t)+K(1-t))/2 continuous onclosedcell, matching endpointvalues, agreesRraw interior. Integral_Ioc_eq_integral_Ioo transfers exact complete-source formula.
Public8:
- factorialCriticalPrimeCellKernel41
- continuousOn_factorialCriticalPrimeCellKernel97
- factorialCriticalPrimePeriodizedKernel_eq_cell117
- factorialCriticalPrimeContinuousRealKernel148
- continuousOn_factorialCriticalPrimeContinuousRealKernel152
- factorialCriticalPrimeContinuousRealKernel_endpoints161
- factorialCriticalPrimeRealKernel_eq_continuous167
- factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral174.
After build completes run actual-file `lake env lean <actualfile>` then actual-import axiom file already PREPARED `/tmp/apt_critical_prime_continuous_kernel_actual_axioms.lean` (8#print lines), not run yet. Inspect all8standardaxioms. Clean those completedscratch sources afterward.
Index refreshed exit0; all8publicentries individually verified in **formal/LEAN_API.md**, rows689512-689519 (positions canmove). `/tmp/apt_critical_prime_continuous_kernel_index.log/status0`.
Latest authoritative `lint --check-generated` status1,381largefilewarnings, ONEforeign BVIunreachable module **CofinalMobiusMagnitudeObservablesAndGradient**. NoAPTerror orstalegeneratederror. `/tmp/apt_critical_prime_continuous_kernel_lint.log/status1`. Preserve foreign module. Global gate NOTGREEN. Scoped whitespace/forbiddenmarker/heartbeat checks passed. Do not rerununchangedlint justto chaseforeignwork.

## Staged but NOT RUN next Lean scratch
`/tmp/apt_critical_prime_kernel_mass.lean` ~200lines imports built KernelDensity + HTGeometry.BandLimitedPositiveConfiguration. DO NOT run until livebuild and continuousactual/axiom checks finish. Source alreadyread/created, noactualleaf installed yet.
APIexample then private kernelMassSinc u=sincSq((1/12)*u); integrability and integral12; private cosine orthogonality=if i=j then12 else0 using existing scaledFourier vanishing. Existing Qcosineexpansion collapseswholeline mass12E, evenness + integral_comp_abs giveshalf6E. Public proposed3:
- factorialCriticalPrimeKernelWeight_eq_sincSq (u>0): Gamma=(pi^2/72)sincSq(u/12), via cos_two_mul/sinc_of_ne_zero/rpow.
- integrableOn_factorialCriticalPrimeKernelWeight_pattern onIoi0.
- factorialCriticalPrimeKernelWeight_pattern_mass: integral_Ioi0 Gamma Q=(pi^2/12)sum b_j^2.
No compile result yet. Likely places todebug fromactualerrors: universe metavars inAPIprobe, rw kernelMassSincunderintegral, integrable_re Complex/RCLikecoercions, castsanddsimp. Do not assume errors.
Second UNRUNscratch `/tmp/apt_critical_prime_negative_budget.lean` importsMathlib and has8exactproofexamples: finite rational meanbudget, curvaturebudget<1/50, finiteHsum coefficient<=1, abs(x-y)<=x+y-8xy on[0,1/4], four Taylor-arithmetic bounds forJ2,J3,J5,J6 using157/50<pi<22/7 andsqrt3<=7/4. These are exact paper-certificate checks, not numerical experiments. Run once permitted; inspect allresults, cleanupwhenrecorded. They prove NOanalyticpremises orkernel sign by themselves.

## Active card and new substantive candidate
`docs/drafts/pipeline/1-in-progress/apt-critical-prime-kernel-signature-2026-10-19.md` now~500lines contains allpaperproofs/search/auditlogs and detailed proposed **uniform NEGATIVE coercivity** route. Cumulativeboundary andkernelrepresentation stepschecked; actualsign/coercivity remains OPEN,0accepted. No fullWeil/RHclaim. Do not treat J_mindependently or isolatedRrawintegernegativeaswitness; continuousrepresentative essential. Ifobstructionproved, strongestpositive survivor mustaudited/formalizedbeforeretirement.

New analytical plan (not proved/credited yet):
- For singletonQ=1, show J2>=10/9; J3,J5<=4/3; J6,J7,J13,J14,J15,J17,J18,J19<=7/6; J9,J10,J11<=1; Jm<=11/10 for m>=20.
- Let theta=pi*m/6. Existing sine-square current yields Jm=1-cos(theta)+theta*(pi/2-integral_0^theta sinc). Existing sineTaylorupperdegree5/lowerdegree7 give smallm2,3,5,6 via rationalpi bounds.
- Proposed Laplace formula Jm=1+integral_t>0 exp(-t)*(theta*t*sin(theta)-t^2*cos(theta))/(t^2+theta^2). Derive 1/v²=integral_t>0 t exp(-vt), Fubini(absintegralbound1), existingcomplexexp integral onv>1. NumeratorCauchy gives |Jm-1|<=1/theta. Sign-sensitive bounds give listedm7..19 without Tayloratlargeangles. Needsformalproof.
- A odd-prime=p logp; odd A9=12log3,A15=3log3+5log5; A(2q)=A(q)-2log2 foroddq; multiples4zero. Logpowerbounds relative log2: log3<=8/5log2,log5<=7/3log2,log7<=17/6log2,log11<=7/2log2,log13<=15/4log2,log17<=25/6log2,log19<=13/3log2,2/3<=log2<=3/4.
- |A(m)|<=m logm gives tail>=20 majorant(11/10)sum logm/m³ <=(11/10)*(log19+1/2)/(2*19²) <=(671/86640)log2 byintegralcomparison. Needproveall.
- Finitepositivebudget in card/scratch is <=5/36-1/300. Negative2term<=-(5/36)log2; thus intended meanR<=-log2/300.
- Stronger survivor: proveuniform|Hj|<=3/8 andsumj1..12|Hj|<=1. Odd/evenchargeidentity =>Hinf<=(9/8)sumoddq>=3 logq/q²-log2/4. Oddlattice integralcomparison gives series<=5log3/18+1/6, henceHinf<=3/8; finiteHfromsign/monotonicity. Finite12Hsum exactlogcombination budget in scratch.
- a=pi/6; gamma=integral_v0^a(a-v)cos(vu); |gamma''|<=a4/12 globallypositiveu; also<=a²/u²+4a/u³+12/u4. Splitj<=12/j>=13 gives reflectedsummandcurvaturebudget T<=pi4/15552+(pi²+pi+1)/1152<1/50.
- Avoid unnecessary infinite-series derivative proof: each reflectedsummand f_j(t) has symmetryandcurvaturebound |Hj|Gj, so |f_j(t)-f_j(s)|<=|Hj|Gj/2*|(t-.5)²-(s-.5)²|. Sum usingT. Withx,yin[0,1/4], |x-y|<=x+y-8xy; integral in s<=1/6. Therefore|R(t)-meanR|<=T/12<1/600. Combine mean<=-log2/300 andlog2>=2/3 toaim **R(t)<=-log2/2000**, hencecompleteprimeform<=-log2/(500*pi4)*E. Noactualsignclaimuntilallproofschecked! This wouldbe strongerpositivecontent (coercivityofoppositesign),notmerelyonecounterexample.

## Corpus reuse found and source inspected
Allsearches launched documentedresearch directly, nohelp/sourceprep. Semanticcoverageunmeasured, noabsence/noveltyinference. Cardtracksfullscreens andexplicitlynotesbroadunexhaustedqueries.
- HTGeometry/BandLimitedPositiveDensity.lean206lines: sincSq35=sinc(pi*y)^2; integrable91; integral_cexp_mul_sincSq177=triangle(w), zerooutside195; integralsincSq199=1. Definitions/appropriateproofssource-read. ReuseFourierinversion.
- HTGeometry/BandLimitedPositiveConfiguration.lean353lines: integral_cexp_mul_sincSq_scaled_eq_zero305: eps>0,eps<=|s| -> integral exp(i*s*y)*sincSq(eps/(2pi)*y)=0. Source305-320andscaledintegrabilityread. Exact sincSq_scaled lexical1hit, exactsincSq13hitsallchecked.
- FejerLatticeVanishing294lines: fourier_triangleFn191, latticevanishing278; relevantbodiesread, differentlatticesum.
- LamzouriSincAffineMinorant34lines sourceallread: anchoredGramminorant, notmassformula. SincBackgroundDetectionWindow sincSqCoeff42 andhasSum45 are sinhpowercoefficients, source32-73read, notourweight.
- RHTower/SoninSineTraceCurrent111lines fullyread: `integral_sinc_eq_square_current`21, `tendsto_integral_sinc_atTop`91. Applicablefiniteidentity yieldsJformula; no duplicateIBPneeded. SoninSincTailMellin sourceall78read: complexbandindicator Mellintail, notsignedscalarbound.
- RHTower/MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP: namespaceRHTower; source1-38,120-183,443-470read. Existing `sin_le_self_sub_cube_div_six_add_pow_five_div_one_twenty_of_nonneg`120; `self_sub_cube_add_pow_five_sub_pow_seven_le_sin_of_nonneg`164; `two_panel_log_two_lower`449 proves69313/100000<=log2. Sourceproofsread; notyetAPIprobedinnewapplication.
- Mathlib ImproperIntegrals: `integrableOn_exp_mul_complex_Ioi`64, `integral_exp_mul_complex_Ioi`88 gives-exp(a*c)/a, Rea<0. Source56-96read. Exactnamehybridrecoveredprimitive; misleadinglexical--moduleMathlib0hitsNOTabsence.
- HTGeometry/MonomialLaplaceComplex183lines: `integrableOn_natPow_mul_cexp`148 (statementnotfullbodyread), `integral_Ioi_pow_mul_cexp`168 givesj!/c^(j+1) forRe c>0. Source1-62,162-endread; headersallseen. Suppliesmoments1,2. WaveTraceLaplace311headersseen, bodyNOTread; sinLaplaceformulaavailable90,138. ThetaRenewalPhaseSlope486source1-110read: integral_exp_mul_ccos79fixesdamping1/4; usesgeneralMathlibprimitive, notpreferredforourvariable-rateproof.
- Mathlib Pi/Bounds: namesverifiedsourceheadersReal.pi_gt_d2(3.14),pi_gt_d4(3.1415),pi_lt_d4(3.1416),pi_gt_three. APIprobespending. Gamma/Basic464 Real.integral_rpow_mul_exp_neg_mul_Ioi source452-472read; realrateformulaalternative.
- Existingperiodizationexactlex25fullypaginated earlierrecoveredrealL1Periodization325-379 andnowusedcompletedKernelDensity. SymmetricHalfEndpointPeriodization compactcontinuous-evenG assumptiondoesnotdirectlymatchinfinitearithmeticjumps.

Recent complete20candidate+20source screens: `/tmp/apt-critical-kernel-sinc-pattern-api.json`, `...-oscillatory-tail-api.json` (+onebadproposedingredientchainmixingTHIMdyadictail), `...-symmetric-oscillation-api.json` (+onebadchainconfusingHessiansymmetrywithreflection), `...-laplace-exp-exact-api.json`, `...-negative-coercivity-prior.json` (+convergenceingredientdoesnotprovesign). sinc-tail-api andpage2 all34displayeddecl+40candidate+40sourcechecked; total40modulecapped, notexhaustiveclaim. Broadoscillationlex65,092, laplace-exp1127, cell-deviation1182: onlyreturned20screened, cardexplicitlynoteslimits; noabsenceclaims. Exactcosine8,sincSq13,sincSq_scaled1 fullyscreened. AllresultJSONin/tmp, nojobsremain.

## Next actions order
1. Recoverbuild30090 result (do notreplace/cancelunnecessarily). Ifpass runcontinuousactualfile thenactual8axiomfile; recordaudits, cleansources. Index/lintalreadydoneasabove.
2. Runnewmassscratch once; fixactualerrors sequentially. Onceclean installsmallnewFactorialCriticalPrimeKernelMassleaf, umbrellaimport, targetedbuild/directactual/3axioms/indexlint; nofullbuild.
3. Runexactnegativebudget8examples; fixpapererrorsifany, recordasbookkeepingonly.
4. Continueactualnative signproofviaexisting sineTaylor/current andLaplace/Fubini; validateeverypremiseandthenuniformcurvatureproof. Do notcountsupportlemmasasnewsignificantcontributions.

Generalpitfalls: beta-reduce before rw inlambda integralcongruences; finitecastsuseNat.cast_one; Int.natCast_zero incontinuousscratch DIDcompile, donotchangeunnecessarily. #axiomsalways/tmp, nevereditactualtreeforit. Use smalllogtails/errors only. Longtasksurvivesviaactivecardandthismemory, notfinalstatus.
