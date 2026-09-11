# Route L C40 COMPLETE mathematical module; C41 next
Date2026-09-11. RH UNPROVED, unbounded goal ACTIVE. PreviousC39wasverifiedprogress.
Workspace /Users/michael/Documents/code/hgt, Lean cwd /Users/michael/Documents/code/hgt/formal.
User override: NEVER #print axioms or substitute axiom-print audits; noneused.
OneforegroundLeanprocess peragent, sequential scratch lake env lean, onlyfinalleaf lake build; nofull/umbrellabuilds, no numericexperiments. No subagentsauthorized. Sharedtreehasotheractiveagents; preserveunrelatedwork.

## Chain
Complete ORIGINAL Green/BV source → fixed cyclic/physical-reader agreement → conormal vanishing → RH.
C39 actualpairedGaussianfullXiHilbert→completedGreen→Tate→SoninreadoutequalsA_P(rho)*oldimage, A_Pnonzero.
C40 closes actualINFINITE-SOURCE limit test in ORIGINAL Meyer topology, nothalf-density orseparateStrongLogtopology.
CoreBV/fixed-readercomparisonstillOPEN. CompactescapeisnotRH andnotphysicalvanishing.

## Newmodule/card
formal/GaloisForLFunctions/RHTower/DeningerCofinalPrimeMeyerEscape.lean
201lines,12theorems+3defs=15decls. Imports:
DeningerPairedPrimeGaussianSoninTransport
DeningerTomographyProduct
DeningerMeyerStrictEmbedding
GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier.
WiredonceRHTower immediatelyafterC39.
Cardmovedto docs/drafts/pipeline/3-formalized/route-l-cofinal-green-source-limit.md
Oldinprogresspathdeleted; all4docsreferencesupdated (C39card,frontier,STATUS,C41card).
FrontierC40paragraphreplacesoldpaperpendingafterC39 near1108.
STATUSroute-neutralnewbullet115: stable measurements ≠convergence ofsources, actualcompactescape.

## Provenmath, literal APIs
33 def deningerOriginalMeyerMellinCLM(s:ℂ):DeningerMeyerSource→Lℂℂ
= continuous originalMeyer exponential weighting e^(Re(s)t) intoSchwartz
→SchwartzFourierCLE→evaluationat -Im(s)/(2π).
39 theorem ..._apply = LITERALdeningerMeyerStrongLogMellin of underlyingtoSourceSchwartzfunction.
No topologyidentification; oldMeyerStrictEmbedding alreadyproves weightedSchwartzmapcontinuousforanyREALweight.
Fourierkernelproof uses openMeasureTheory, rwSchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, integral_congr_ae, exp_add, push_cast, conv_rhs=>rw[←Complex.re_add_im s], field_simp[Real.pi_ne_zero],ring.

58 def deningerPairedPrimeMeyerSource(P:ListNat.Primes) originalMeyerfacade ofC39g_P viaExpSchwartzOfStrongLogDecay.
63 ..._mellin =actualMellin(g_P)(s).
69 ..._prime_kernel(P,p,hp∈P) originalcirclePerlogp(source)=0 viaC38strongGreenrange→ExpSchwartzdefect→periodizationrangeeqkernel.
86 ..._cofinal_limit_zero(P:Nat→ListPrime)(hP:∀p,eventuallyp∈P_n)(c:Nat→ℂ)(h)
(hlim:Tendsto c_n•sourceP_n atTop nhdsh):h=0.
ProofeachkerPerclosed, eventualmembership surviveslimit; cofinalprimetomography forceswholeSchwartzsource0, facadeinjective.
110 def deningerPairedPrimeMeyerXiNormalized(P,rho)=(literalMCLM rho sourceP)^-1 •sourceP.
115 ...Source_xi_ne_zero (C38).
121 ...XiNormalized_reading =1.
128 ...XiNormalized_not_tendsto(P,hP,rho,h):noMeyerlimit.
ContinuousMCLM passesnormalizedreading1 tolimit; previous theoremh0contradicts.
144 ...XiNormalized_escapes_compact(P,hP,rho,K,hK):eventuallysource∉K.
Compact+firstcountablespace givesconvergentsubsequence ifinfinitelymanymembers; StrictMonophi.tendsto_atTop preservescofinalP; previousno-limitcontradiction.
156 deningerOriginalPrimePrefix_cofinal(p):eventuallyp∈(GaloisForLFunctions.primesLE n).toList.
162 deningerNormalizedPrimePrefix_no_limit(rho):¬∃h,Tendsto EXPLICITallprimes≤nnormalizedsource to h. NOcofinalitypremise.
171 deningerNormalizedPrimePrefix_compact_escape(rho):∀compactK,eventuallyexplicitfamilyoutsideK.
180 deningerPairedPrimeMeyerXiNormalized_physical_readout(P,p,q,n):
fixedSonintransport(completedDifferential(c_Pq •C39actualprime/depthchain))
= oldGaussianGrade(q)^-1 •oldphysicalimage(q).
c_Pq inverseactualMellin; C39A_P*oldGrade factorcancelsA_PviaC38ne0. Retainsoriginalp,n,divisorcopyqandoldresiduenormalizer, notassumedcomparison.
Doesnotassertimagezero. Weakertopologiesanddampedapproxkernelsnotcovered.

## Validation
Scratch /tmp/route_l_cofinal_c40.lean byteidenticalmodule.
Initialwrongcwd(hgt) session56191exit1 unknownprefix, correctedimmediatelyin formal. No duplicateprocess.
Check2session45342 exit1 onlymissingopenMeasureTheory forintegral_congr_ae; kernelproofalreadychecked.
Check3session38915 exit1 onlyFouriercomplexcastring; allnewcompact/physicalproofschecked.
Check4session14778 exit0, oneunnecessary <;>warning. Removedsequencefocus andexamples.
FINALscratchsession19418exit0 EMPTY /tmp/route_l_cofinal_c40_finalcheck.log.
FINALleafsession33695exit0 /tmp/route_l_cofinal_c40_build.log:
ONLYnewleafBuilt193s,11942dependencygraphjobs; noundesiredumbrella.
OwnedPIDs15440,15480,16300,16369allgone.
Dup /tmp/route_l_cofinal_c40_dupcheck.log:15decl0collisions;importcount1,byteidentity,diffcheckpass.
Indexsession64276exit0 ..._index.log;3generateddocsupdated;0sourcechangedbecausebackgroundindexeralreadyrefreshed. ConfirmedmoduleinLEAN_API.
GLOBAL LINT session28149 EXIT1 ..._lint.log:
ONEUNRELATEDerror: ownedmoduleunreachable RHTower.ThetaCuspHawkingBMSourceDensityDual.
C40importpresent. Do NOTclaimlintpassed.
Thatunrelatednewfilewasbeingbuiltbyanotheragent inisolatedaudittemp:
livewhencheckedPID17253lake+17260lean, elapsed2:05,
temporarypath /private/var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/hb-source-density-dual-audit-ox12xsc2/...
Rootumbrella lackedimportatlastcheck. DON'Tkill/editit; rerunglobal lintonlyifnewwiringstatechanges. C40carddocumentsfailure.
NoownedLean/researchleft. No commits/pushes. C40mathcomplete;globalgateblockedbyconcurrentunrelatedwiring.
Do not markRHgoalcomplete/blocked.

## Research C40
All20candidate+20sourceargs+ingredients inspected each150sdeep/methodreport:
1 /tmp/route_l_cofinal_c40_continuity_deep.json session9725done
gen874781sem2352738/2353405 partialdeadline/filterjudge/source_refresh,ideas[],ingredients[].
2 ..._compact_deep.json session26821done gen874796sem2352770/2353445 samepartial,ideas[],ingredients[].
3 ..._tightness_deep.json session90201done gen874828sem2352929/2353562 partialsemantic/retrieval/source_refresh;generateddecay→Poissonsum suggestionnotapplicable.
4 ..._abel_residual_deep.json session22697done gen874835sem2352929/2353624 partialdeadline/coverage/source_refresh;dampedEuler→Abel suggestionnotadopted.
Do notreadliveJSONbeforeterminal; causedoneJSONDecodeError, waitedproperlythenread.
Broadarxivcompactness,condensation,boundary,escape,tightness;June–Sept2026 filtersreturnednoapplicablerecentpaper;directarxivsearchpagescachemiss;broaderqueriesreturnedoldpapers.Don'tinventrecentdates.
Primaryread https://arxiv.org/pdf/math/0201161 (DörflerFeichtingerGröchenig2002),Theorem2+proof(pp1–2):compactnessofclosedboundedL2famiffSTFTtightness. SplitscompactregionDCTfromuniformtail. NotMeyercompactness, noLeanpremise. C40cardcitesunder200words.
EarlierC39futurepaperresultsirrelevantnotrepeat.

## C41 NEXT: actual damped paired prime residual
CARD CREATED docs/drafts/pipeline/1-in-progress/route-l-damped-prime-green-residual.md.
NO C41 Leanfile/moduleyet.
ThisisnexttaskafterC40; retainfullRHgoal. Needattackmovingnormalizedremainder, not merelyasserta vanishingprefactor.
OriginalT_cg(t)=g(t-c), Jg=e^-t g(-t).
D_(L,a)=Id-exp(-aL)T_-L.
J D J=Id-exp(-(a+1)L)T_L (existingJflow law).
E_(L,a)=D J D J,commutingshiftproduct,Jcommutes.
LiteralMellin A_(L,a)(s)=(1-e^{-(a+s)L})(1-e^{-(a+1-s)L}).
a≥0,L>0,0<Re(s)<1 ⇒A≠0,reflectioninvariant.
AtORIGINALcircleperiodL:
Per_L(Eg)=r_(L,a) Per_Lg,
r=(1-e^-aL)(1-e^{-(a+1)L}).
Derivativea0=L(1-e^-L)>0.
Removeoneprimeoccurrencefromfinitecommutingproduct: sameexactresidualonENTIREremainingg. Repeatedprimek keepspower r^k.
NormalizedrecursionPer gP/MgPρ = (r/Aρ)*Per gRest/MgRestρ.
Vanishingr/a alone DOES NOT bound movingnormalizedrest.
CandidateinfiniteEuler1/[ζ(a+s)ζ(a+1-s)] needsliteralconvergence+domainadmission; notasserted. AsafinitepositiveparameterfamilyE_Pag0 isH butinfiniteproductmayleaveallweighttopologyeveninabsolutechamber.

IMPORTANT NEW CLOSED SCALAR PAPER PROOF:
For a>0,L>0,actualrho:
q=e^-aL,x=e^-Lσ,y=e^-L(1-σ),allin(0,1),xy=e^-L.
|Aρ|≥(1-qx)(1-qy) byreverse triangle andpositivity.
r=(1-q)(1-qxy).
(1-qx)(1-qy)-r = q(1-x)(1-y)>0.
Hence |r/Aρ|<1 withEXPLICITpositivegap.
Positivefinite-family survivor:repeatONEoriginalprimefactor k times,
normalizedPer=(r/A)^k timesoriginalnormalizedPer →0 inactualcircle,
Xi readingstill1; physicalnormalizedtransportunchangedifC39generalizedproperly.
ForcofinalMULTIPRIMEfamilyremainingoperatorscanamplifyothercirclecomponents;singleprimecontractiondoesnotclosewholecomparison.
Needformalizeexactsource+dampednormalization+contraction, thenATTACKmovingremainderwithactualestimates. Don'tjustdeclareanotherconditionalRHcriterion.

C41sourceanchorsread:
C38 DeningerFinitePrimeGreenDomainXiJets hasJ/flow andpairedMellin,
DeningerTomographyNonstrict.lean38periodizationSum_periodic;
43EscapeFamilya s h=exp(-as)*ExpShiftSource(-s)h;55exactPer escape at(t-s).
Namesseen in38proof: deningerPeriodizationSum_expShift, deningerPeriodizationSum_shift. Verifytheirdefs/signsbyrg/readbeforeuse.
Sieve/DampedEulerCorrection.lean24 dampedEulerFactor(t,p,s)=(1-t p^-s)/(1-p^-s),normbound28; DIFFERENTnormalizationnotactualpairedsource.
SoninCofinalMobiusGammaXiIncidence.lean readheader1–36 and181–238:
actualMöbiusFishercofinalSonintransportalreadyhandlesnoncompactsourceandGammaoverlap;
fixedEulerCofinalSigma s n=1+(s-1)/(n+1),fixedEulerCofinalDamping n=n,
fixedboundaryparam=s (s>1); notvanishinga. Do notconflatethisalreadyclosedmechanism.
Potentialold source comparison bridge C39search: FrankensteinRoutePCCMGammaSixMeyerTateSourceBridge.lean53 oldchain=Green*RoutePrawsource; notbodyreadyet.
Readfrontier'sOpenCore beforeanynewrouteclaim; exact cyclic-source-to-fixed-readeridentitystillmissing.
