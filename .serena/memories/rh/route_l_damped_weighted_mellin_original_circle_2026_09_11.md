# C44 closed: same-source weighted L1, literal Mellin formula, all original circle coefficients

Goal: unconditional closed Lean RH proof via Route L. RH UNPROVED; goal ACTIVE. No new goal/status completion. User forbids #print axioms (none run), numerical computation, full/umbrella builds. One foreground Lean process per agent; scratch lake env lean, lake build leaf only final audit. No subagents authorized/spawned. Shared workspace preserve other edits. Root /Users/michael/Documents/code/hgt; Lean cwd formal.

Chain: complete original Green/BV source -> fixed physical-reader agreement -> conormal vanishing -> RH. Retain original prime/native Tate depth/multiplicity/nonzero Xi leading coefficient/horizontal anchor/original Gamma normalization. Never assume physical agreement, stationarity, radial balance, isometry, or critical-line placement to produce it.

## C44 COMPLETED AND VALIDATED
Module formal/GaloisForLFunctions/RHTower/DeningerDampedWeightedSourceBoundary.lean: 607 lines, 42 public theorems +11 defs +1 abbrev =54 public decls,6private helpers. Namespace RHTower. Wired exactly once after C43 at RHTower.lean3118. Card moved from 1-in-progress to docs/drafts/pipeline/3-formalized/route-l-damped-weighted-source-boundary.md. Frontier Route L, STATUS new route-neutral entry near122, C43 andC42 cards updated. New C45 card docs/drafts/pipeline/1-in-progress/route-l-damped-full-mellin-jets.md. No commits/pushes.

Actual weighted L1 map is Schwartz toLp1 after C43 weightedSchwartz. Translation exact isometry onLp1. For H_cg=exp(ct)g, literal prime factor=(Id-u translation(L))(Id-v translation(-L)), u=exp(-(a+c)L),v=exp(-(a+1-c)L), repository translation(b) f(t)=f(t+b). Norm E<=exp(u+v)||f||, difference<=2(u+v)||f||. Prime summability on1-a<c<a. Exact source successor from C43 via new public weightedL2injective. Uniform prefix bound/summable increments -> actualLp1 Cauchy/convergence.

SAME source proof: half-density Lp2 convergence -> AE subsequence phi; weightedLp1 convergence alongphi -> AE subsubsequence psi; original finite weighted identity and uniqueness of pointwise limits. No assumption exponential multiplier globally bounded/continuous onLp2. Define g_a(t)=exp(-t/2)*C43HalfDensityLimit a t. exp(ct)g_a AEequals weightedLp1limit for everyadmittedc. This is actualsource representative, notquotientL1 orunrelatedchosenfunction.

Literal Mellin at Re(s)=c is Real.Lp.fourierTransformCLM ℝ ℂ evaluated at -s.im/(2pi). Thus actualintegrals integrable andfiniteactualMellins converge. Eulerproduct from riemannZeta_eulerProduct_hasProd (Re>1), invert with actualzeta nonzero, multiply bothfactors, original primesLE cofinal gives:
M(g_a)(s)=M(g0)(s)/(zeta(a+s)*zeta(a+1-s)), 1-a<Re(s)<a.
Original reflectedGaussian M(g0)=exp((s-1/2)^2/(4pi)). Source NOTdefinedbyEulerformula. EveryactualXi reading at a1 admitted/nonzero via existing xi_divisor_support_re_mem_open_unit (no critical-lineassumption).

At a2 bothweights0,1 admitted. g2 andexp(t)g2 integrable; actualtotalmass nonzero. EveryordinaryFourierreading nonzero. Existing HTGeometry.L1PeriodizationFourier supplies literal circle sum P_Lg(t)=sum_int g(t+jL), actualcircumferenceL=logp:
FourierCoeff_k(P_Lg2)=(1/L)*M(g2)(-2pi*i*k/L) !=0 foralloriginalp,forallintegerk.
P_Lg2 notAEzero onfullIoc0L. Also NO integrable h withh(t)-h(t+logp)=g2(t) AE, because integraltranslationdifference0 butmassnonzero. This disproves vanishingcircle/GreenL1admission for thisspecificinitialdampedsource andformalizesstrongpositive survivor(allcoefficients+exactMellinformula). RouteLnotretired. No completeGamma/BV boundary orfixedSonin equality provedthismodule.

## Main APIs/lines
DeningerWeightedSourceL1 31; deningerStrongLogWeightedL1LM52 andflow57; deningerStrongLogWeightedL2LM_injective116; deningerDampedOriginalPrimePrefix_source_step135; deningerWeightedPrimeStepWeight; deningerDampedWeightedL1Prefix; deningerDampedWeightedL1Limit; deningerDampedWeightedL1Prefix_tendsto.
AE compat: deningerDampedWeightedL1Prefix_halfDensity_ae; deningerDampedWeightedL1Limit_halfDensity_ae; deningerDampedLogSource; _weighted_ae; _weighted_memLp; _weighted_integrable; _aestronglyMeasurable; _mellin_integrable (zerothonly).
Mellin: deningerWeightedL1MellinCLM; _eq_integral; _source; deningerDampedLogSource_mellin_tendsto; deningerDampingOne_source_xi_admission.
Euler: deningerOriginalPrimePrefix_tendsto; deningerDampedPairedMultiplier_cpow; _hasProd; deningerDampedLogSource_mellin_eq495; _mellin_ne_zero511; deningerDampingOne_source_xi_ne_zero523.
Endpoints: deningerDampingTwo_source_endpoint_integrable530; _total_mass_ne_zero538; deningerDampedLogSource_fourier_eq545; deningerDampingTwo_source_fourier_ne_zero559; _primeCircle_coefficient565; _primeCircle_coefficient_ne_zero576; _primeCircle_not_ae_zero586; _no_integrable_primeGreen597.

## Validation, processes
Scratch /tmp/route_l_c44_weighted.lean check8 session69359 exit0 empty /tmp/route_l_c44_weighted_check8.log. Headercommentaddedafterbodycheck; scratch/moduleidentical andfinalleafcheckedwholemodule.
Final leaf session27299 exit0 /tmp/route_l_c44_weighted_build.log; ONLY C44 Built30s,11946graphjobs othersReplayed. DoNOTcatwholebuildlog (manyreplayedwarnings); filter Built/errors/completion.
Lint61282 exit0 /tmp/route_l_c44_weighted_lint.log; ordinarylargefilewarnings, formal lintpassed. Avoidcatwholelintlog; tail/filter.
Index58558 exit0 /tmp/route_l_c44_weighted_index.log: 3generatedAPIdocs,4changedsources; all54publicdecls verified in formal/LEAN_API.md, no collisions; diffcheckpasses;newcardlinksverified.
AllC44 Lean processes andsearch10382,97017 terminal. No ownedrunningLean orjobs. No needrepeatvalidation.

## Actual pitfalls solved
MemLp uses memLp_congr_ae, not .congr. ForjetAEStronglyMeasurable, rewriteexplicitfunctionequality first; convert generated irrelevant Real.measureSpace.toMeasurableSpace = Real.measurableSpace goal. Explicit heqjet=fun t=>exp(s*t)*g works.
HasProd modernSummationFilter wrapper: simpa only [HasProd,Finset.prod_inv_distrib,inv_inv] using Tendsto.inv₀. Add Function.comp_apply tosimplification ofHasProd.comp prefixes.
FourierCoeffOn andfourierCoeffOn_congr_ae are ROOT names, notReal namespace. Real.Lp.fourierTransformCLM isRealnamespace. InpublicfourierCoeffOn statement, logpositivewitness needs explicit (show (1:ℝ)<(p:ℕ) by exact_mod_cast p.property.one_lt); circumferencecannotinferfromfunctionargument alone.
Newtail fragment files exist /tmp/route_l_c44_{convergence_tail,compatibility_tail,euler_tail,periodization_tail,green_tail}. They maycontain OBSOLETE names; authoritative tree/scratch only. Neverreappendrawtails.

## Searches/papers C44
All20candidates+20sourcearguments andemptyideas/groups inspected: compatiblelimits /tmp/route_l_c44_compatible_limits_deep.json gen875672 semantic2355164/2355164 partialdeadline/filterjudge/source_refresh; earlierweightedMellin gen875564 carded; periodization /tmp/route_l_c44_periodization_mass_deep.json gen875888 semantic2355235/2355279 samepartial. Lastfound L1PeriodizationFourier coefficient method actualbodyreadandused. Abstractorbitenergy requiresstrongerpairings andnotadopted.
Broad single-wordarxiv threshold,sewing,gluing,interpolation: Alimoglu2609.10601 Sept7abstract(no transfer); Dong2608.09528 Aug10abstract(robotregistration,no transfer); Dimitric/Vuckovic/Zigic2609.06258v1 Sept5intro+Theorem3.4(smoothselectedderivativeboundsboundedspacing->allorderswithparameterloss,noGevreyassumptionimported); Evangelatos/Haiden2608.21201v1 Aug21intro+phasegapdiscussion(categoricalsupport, noRHtransfer). C44cardlinksandlimits. No papers usedasproofpremises.

## C45 NEXT: exact hard-obstacle attack, noLeanmoduleyet
Cardwrittenwithdependency-closedpapermechanismforfinitejetconvergence. Pickdelta>0 withc±=Re(s)±delta in1-a,a. Currentread Real.pow_div_factorial_le_exp fromMathlib/Analysis/Complex/Exponential.lean245–260 gives |t|^k <= (k!/delta^k)exp(delta|t|). Hence|t|^k exp(Re(s)t)<=C(exp(c-t)+exp(c+t)). C44weightedL1distancesofactualgN-ga tend0, so integratedjetnormdifference tends0. Thisprovesjetintegrability andactualjetintegralpassage. Formalizeexactinequality+Lp1differenceidentification; noallweightMeyerassumption.
Then localdominateddifferentiation onsmallerstrip ->actualcomplexMellinderivatives=literaljets; differentiateC44Eulerformula locally onlyAFTERsourceadmission. Retainoriginalmultiplicity/nonzeroXileadingcoefficient; no boundedmultiplicityassumption.
NextfullXi field forfixeda>1: onentireclosedunitstrip |A_p|<=(1+p^-a)^2,|A_p-1|<=3p^-a; summableprimebound ->uniformproduct/tails. Apply toactualGaussianXiDivisorL2 field; useC44literalvalues toidentifylimit; transportexistingGreen/provenance/originalGamma/nativeTate/fixedSonin maps. Needinspectexactjetrequirements permap. CurrentC39publicdeclarations located; wholebodies notreread thisturn. C39 deningerPairedPrimeGaussianXiField93,GreenPrimitive131,residue_normalization159,GreenProvenance166,norm182,finitephysical219,completed235.

C45researchDONE /tmp/route_l_c45_mellin_jets_deep.json, session97017exit0. All20candidates+20methods inspected,emptyideas/groups. gen875940 semantic2355400/2355414 partialdeadline/filterjudge/source_refresh. ExistingallweightMeyer/entiremoment hits requiretoo-strongpremises; doNOTadopt. CandidateDeningerMeyerBoundedMellinMajorant andoriginaljetdifferentiationbodycouldsupplylocalmethods. OriginalMellin.leanhas hasDerivAt_deningerMeyerStrongLogMellinJet258, hasDerivAt_integral...290, Differentiable406. Need inspectexactbodies thenadaptstripadmission. MathematicalC45statements notyet Leanverified.

Remembercomments <=60seconds, no oversizedSTATUSparagraphs/tooloutputs. Shellzsh unmatchedglob errors: use rg --files/--glob instead of guessedliteralglobpaths. No goalcompletion orblockedstatus.