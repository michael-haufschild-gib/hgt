# EDQ dilation-separated power growth — COMPLETE bridge, RH still OPEN

Persistent user goal ACTIVE; NOT achieved. This turn made substantial VERIFIED PROGRESS: stronger source-current lower growth and genuinely weaker sufficient upper target. Do not mark blocked for mathematical difficulty. Next turn starts full chain Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH, with concrete intended advance. Current continuation began with token total8,453,289.

## New leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionDilationPowerGrowth.lean, namespace RHTower.DeletionDilationGrowth, about400lines, 16PUBLIC THEOREMS,0defs,3privatehelpers. Imports EulerDeletionMobiusGramCancellation and EulerDeletionPowerSumRemainder. autoImplicitfalse. Read before modifying. EXACT public declarations:
18 rawPrefix_mul_cpow_tendsto: for0<Re(s)<1, rawPrefix(s,K)*K^(s-1)→1/(1-s).
40 rawPrefix_norm_div_rpow_tendsto: norm(rawPrefix)/K^(1-Re(s))→norm(1/(1-s))>0.
51 exists_rawPrefix_dilation_separation: ∃D,K0 naturals,D>=2,K0>=1,∀K>=K0,2norm(S(K))<=norm(S(DK)).
89 scalar_pair_energy_lower: for ANY x,y,h:ℂ with2normx<=normy,1/8<=norm(hx-1)^2+norm(hy-1)^2. No harmonic decay, phase assumption, zero premise.
111 exists_sourcePrefix_dilation_pair_lower: sameD,K0,allN,K≥K0 withDK<=N, actual prefix pair squaredsum>=1/8. Exact actual harmonic scalar never changed.
123 sum_prefix_lower_of_dilation_pairs: generic f>=0,abovepairlaw,N>=2D(K0+1) ⇒ N/(64D)<=sum_{1..N} f.
179 exists_sourcePrefix_square_sum_linear_lower: forstrip s,∃D>=2,eventuallyN N/(64D)<=sum_{k=1..N}norm(sourcePrefix N s k)^2.
206 weight_increment_lower: for1/2<σ<1 andn<N, a*(N+1)^(a-1)<=weight(n+1)-weight(n), a=2σ-1.
219 energyHead_lower_prefix_sum: sameweightfactor times completeprefixsquare sum <= actualenergyHead N s N.
236 exists_sourceCurrent_rpow_lower: EVERYright-halfactualzeroρ,∃C>0,eventuallyN C*N^(2Reρ-1)<=(sourceCurrent Nρ).re. ExplicitC=a/(128D).
276 exists_abs_sourceCurrent_rpow_lower: EVERYofflineρ,∃C>0,eventuallyN C*N^(2*abs(Reρ-1/2))<=abs(ReQ).
328 sourceCurrent_cofinally_subpower_iff: foractualρ, (∀e>0,∃B,∀K∃N>=K abs(ReQ_Nρ)<=B*N^e) iffReρ=1/2.
343 riemannHypothesis_iff_mobius_current_cofinally_subpower: exactglobalRHreceiver.
355 riemannHypothesis_of_cofinally_subpower_primitiveEnergy.
368 riemannHypothesis_of_cofinally_subpower_modular_norm.
380 riemannHypothesis_of_cofinally_subpower_cross: one-sidedSIGNEDcross ceiling suffices, noabsolute required.
Lastthreeassumptions: ∀e>0∃B∀K∃N>=K fullinput<=B*N^e. NO RHconverse for inputenergy/cross asserted.
AllN/e/zero-dependent constants/selectedcutoffs allowed in currentcriterion; no common subsequence or uniformityase→0 required.

## Why this is new useful progress
Previous logWindow argument neededH_N logarithmicdecay toretainunitdefect,and onlyprovedsuperlogarithmiccurrentescape. Now shape at separateddilations forces a pairdefect uniformly in ANYcomplexscalarh. Actualprefix=H_N*S_s(K)-1 throughoutK<=N. PairK,DK forK0<=K<=floorN/D,eachcoordinatecounted≤2,thereforelinearunweightedprefixenergy. Concaveweights turnit intoN^(2σ-1). ActualzeroGramdominateshead;reflectiongives2|σ-.5|.
Thus the missing upper producer is WEAKER than polynomial-log: cofinalsubpowerbounds suffice. Existingunconditionalfullsourceo(N/(logN)^q) stilldoesNOTreachthis; coexistwithanyfixedpowerN^a,a<1. No numericalexperiment warranted for visible deductions; NONErun. RHgoalunchangednotachieved.

## Proof details / traps
Kernelnamespace DIFFERENCE:
DeletionMixedRefinement.kernel s n=(n:ℂ)^(-s),rawPrefix=sum_{n< K}kernel(n+1).
DeletionChronologicalLimit.kernel s n=((n:ℝ)+1:ℂ)^(-s),usedsourcePrefix.
Private sourcePrefix_initial_raw closescasts bycongrsum,simp[two kernels]. Don't assumeonekerneldef.
Normalizedcomplexprefix derivedcenteredPowerPrefix limitζ pluskernel→0,multiplyK^(s-1)→0;cpow_add atK>=1 makesmainterm1/(1-s).
D chosenbyD^(1-σ)>=8 andeventualnormalizednormbetweenA/2 and2A,notD=2.
Genericpairbound triangle gives1<=2normu+normv, squarecomparisongives1/8.
CardcountR=N/D,K0<=R,usesNat.card_Icc. ImagesinjectiveviaNat.eq_of_mul_eq_mul_left.
Weightlower uses root rpow_one_add_le_one_add_mul_self withs=-1/(x+1),a∈[0,1],notderivatives. Privatehelper exact a*(x+1)^(a-1)<= (x+1)^a-x^a. Importantrealrpowdivisionnormalizationringidentitybeforelinarith.
Range/Iccsumconversion must be genericinf:cannotinductN usingsourcePrefix N becausefchangeswithN. Privateinline hshift(f)(M)inductsM.
Reflection: rw[hexp] at hbound BEFOREsimp[partner]; otherwise simpchangesr.rebeforeexponentpatternmatches.
No-cofinal-subpower contradiction picke=a/2, N^(a/2)*C→∞;multiplybyN^(a/2), rpow_add givesN^a.
Root rpow_one_add_le_one_add_mul_self is realBernoulli; Real.one_add_mul_self_le_rpow_one_add andReal.rpow_le_one_add_mul_self UNKNOWN. Finset.sum_Icc_eq_sum_range UNKNOWN. Probesfailedonlynamesnotassumed.
Lean domainhypotheses parameterdomainsareexplicit;noMertens/PNT/harmonicpremiseinactualsourcefloor.

## Validation COMPLETE — do not repeat
APIprobe41498exited1unknownnames(noactiveprocess). Scratch86712,7939,19732hadlocalelaborationerrorscorrected; intermediate25749provedpowerfloor; FINALscratch29585exit0EMPTYlog,includingall16.
Final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionDilationPowerGrowth process90952exit0,ONLYnewleafbuilt17s,13114cachedgraphjobs. Nootherleaf/full/umbrellabuild.
New-onlyaxiomsaudit23026exit0,ALL16exactlypropext/Classical.choice/Quot.sound. Noaddedaxioms,sorry/admit,opaque,unsafe,native_decide,numericalcert.
Formal lint96793exit0PASSED. ONEindexrefresh13changed0removed33149files404363decl3953gaps.
Scopedsource=scratch,blankdiagnostics,forbiddentokens/whitespace,exact16axiomrecords,stdaxiomsets,uniqueumbrellaimport,cardstage/linkspassed. AllownedhandlesDONE. ps basenamelean/lake +exactownedfilenames/modulesfoundnone.
Removed /tmp/edq_dilation.lean,_api.lean,_axioms.lean. Logsretained/tmp/edq_dilation.{api,scratch,build,axioms,lint,index}.log.
PriorCountertermleaf/cardleftunchangedandnotrebuilt/re-audited.

## Docs complete
Card docs/drafts/pipeline/3-formalized/edq-dilation-separated-power-growth.md; removedstage1card. Frozen[BRIDGE]paperproof,exactconstants,corpusnoveltyaudit,nocomputationdecision,allvalidationdocumented.
FrontierCURRENTstate: addeddilationpowerparagraphaftercurrentescape,updatedsummary,primitive/cross/global-saving/quotientparagraphs,EDQrow,androuteconclusions. Currentbestopenproducer=cofinalsubpower,oldlogcriteriaremaincorrectsufficient. Uniformperiodno-gologstatementsleftunchanged.
STATUS new MUST-TEST-SHARED-COEFFICIENTS-ACROSS-SCALES. ExistingMUST-COMPARE-THE-FULL-GROWTH-SCALES nowexplicitlynotesnearlinearsavingscan coexistwithfixedpositivepoweranddon'tgive subpower. Otherentriesleft.
Allconcurrentotheragentchangespreserved,nocommits/push.

## Other corpus reads this turn
MobiusMertensPrimeRemovalTentLaw1–220: oneprimefour-hingetransferexactnonnegativetent,minimalp2; coefficientprimefree difference; Mertenspartialsum equalsprime-freewindow(N/p,N]. Two-prime negative unit lobe inmoduleheader notlaterproofread. Differentadditiveconvolution source,doesnotproveEDQcofinalsubpower.
MobiusIntegerCuspConfinement onlydeclarationinventory,NOTreadproofs. Movingcuspexterior/localizationresults mayanalogize,but noactualEDQbound.
PoissonMuntzAbelMeanDefect onlydeclarationinventory,NOTreadproofs.
MobiusLaplaceMellinPlancherelBridge onlydeclarationinventory,NOTreadproofs; energyreceiverscontainpremises,doNOTassumeunconditionalcriticalenergy.
Corpussearchesharmoniccofinal/sign/oscillationfoundnoactualH_Ncofinalsmall/signchangeprovider. AvoidassumingH_Nchanges signinfinitelyoften; dilationargumentdeliberatelyremovedneed.
