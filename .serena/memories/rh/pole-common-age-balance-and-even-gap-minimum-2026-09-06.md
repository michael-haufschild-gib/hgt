# Actual common age loss, eventual opposite curvature, unique even minimum

GOAL ACTIVE: RH not proved/disproved. This turn PROGRESS:26pubtheorems+11defs,4finishedleaves,all37standardaxiomaudits. Prior `mem:rh/pole-prime-power-gaps-and-parity-entry-slopes-2026-09-06`. Noownedliveprocess, numerics, subagents, commits, full/umbrella builds. Sharedworktree foreignHTGeometryetc edits preserved.

## Current chain and actual open source
All-aperture |C|≤A → square-root logarithmicChebyshevprimitive → boundedactualunitRieszresolvent → mathlibRH, conversealreadyformal. Oddtail≥2 needsstart+genuineprimepowercheckpointvalues. NEW exactagingbalancebothparities,lateoddconcavity/evenconvexity,anduniqueACTUALevenminimumoneachclosedprimepowergap. SourceVALUE signsremainopen: oddcheckpoints,evenminimumvalues,remainingboundedranges. Do notclaimglobalRH,globalcurvatureacrossjumps,orfirstfailureatentry.

## Mathematical new knowledge
Forprimepowern, b=logn/2,t=s−b,λ=Λn. Existingactualatoms d=2λ(exp s/n−exp−s),c=λ(1+1/n)(2s−logn). DefineJodd=4λ(1−exp−b)²,JevenMagnitude=4λ(1+exp−b)²,V_n=8λexp−b(sinh t−t).
EXACT2(−d+c)=Jodd*t−V_n;2(−d−c)=−Jeven*t−V_n. SAMEpositivepost-entrylossbothparities. K(t)=sinh t−t=∫0..t sinh(t−u)u du;K≥0t≥0,positiveifft>0. OddalternativeGreenbalance2(−d+c)=Jodd*sinh t−4λ(1+1/n)K(t).
Sumvisible: Eodd=2(Asm−Csm)+Bodd−V; Eeven=2(Asm+Csm)−Beven−V; Bodd,Beven,V ALL≥0, V>0aftera>log2/2. ThusentrytangentsaloneUPPERboundenergy,strictafterfirstentry; notlowerpositivityproof. DoesNOTassertactualnegativeRHtest.
Sourcegateexactly V≤2(Asm−Csm)+Bodd and Beven+V≤2(Asm+Csm).

LetK_A=existingccmWeilPoleUniformDiagonalBound>0,|A|≤K_Aexp a. FA=16cosha−4exp−a−4exp−a(1+exp4a)/(exp4a−1); FC=8cosh2a+4−4/(exp2a−1). For a≥2:0≤FA≤16exp a,FC≥4exp2a. OrdinaryEodd''=2(A+FA−FC),Eeven''=2(A+FA+FC). Threshold R0=max2(log(K_A+17)) ⇒ expa≥K_A+17 ⇒Eodd''<0,Eeven''>0 inmatchingcutoffs. Acrossentireprimepowergap aboveR0, frozenfunctionsequalatallinteriorradiiandactualvaluesidentifyatbothendpoints:strictoddconcavity/strictevenconvexity. Compactness+strictconvexity⇒uniqueactualevenminimizerinclosedgap. Itsnonnegativityiffwholegapnonneg;ifinteriorincomingevenderivative0. Maybeatboundary,notassertedinterior.

## Finished modules (namespaceRHTower)
Underformal/GaloisForLFunctions/RHTower. All4wiredafterPoleEntrySlopes beforeThetaTiltLogDensity inRHTower.lean.
1 CCMRestrictedWeilPrimeAgeBalance.lean 131lines,9pubtheorems+4defs.
DefsccmWeilPoleAgeKernel,ccmWeilOddPrimeEntrySlope,ccmWeilEvenPrimeEntrySlopeMagnitude,ccmWeilPrimeAgeLoss.
ccmWeilPoleAgeKernel_nonneg,pos_iff,eq_green_integral. Greenantiderivative−u*cosh(t−u)−sinh(t−u),derivativeu*sinh(t−u),FTCnohypothesest.
ccmWeilOddPrimeAtom_eq_tangent_sub_age,ccmWeilEvenPrimeAtom_eq_tangent_sub_age,ccmWeilOddPrimeAtom_eq_green_balance (n≥2,anys).
ccmWeilPrimeEntrySlopes_nonneg alln;ccmWeilPrimeAgeLoss_nonneg afterentry;ccmWeilPrimeAgeLoss_pos genuineprimepowerstrictlyafterentry.
PrivatehalfLogexp/inv/diagonaldifferenceexact. Noasymptoticsorcomputation.

2 CCMRestrictedWeilPoleEntryAgeSource.lean128lines,5pubtheorems+3defs.
DefsBodd=ccmWeilOddEntryTangentBudget,Beven=ccmWeilEvenEntryTangentBudget,V=ccmWeilPrimeAgeBudget,alloriginalIcc2floorexp2a.
ccmWeilEntryAgeBudgets_nonneg triple.
ccmWeilOddPole_eq_entry_age_balance andEvenPole_eq_entry_age_balance ACTUALfullquadraticidentitiesasabove.
ccmWeilPrimeAgeBudget_pos ifa>log2/2 fromliteralprime2summand.
ccmWeilParity_nonneg_iff_entry_age_budgets exacttwocomparisonstatedabove.

3 CCMRestrictedWeilPoleParityCurvature.lean151lines,6pubtheorems+4defs.
DefsccmWeilPoleDiagonalForcing FA,ccmWeilPoleCrossForcing FC,ccmWeilEvenPoleChamber a s=2(Acha+Ccha),ccmWeilPoleCurvatureThreshold R0.
ccmWeilPoleForcing_bounds hs≥2:0≤FA∧FA≤16exp∧4exp2s≤FC. Ratioexp4s≥9⇒≤2;exp−s≤1,cosh≥1,cosh≤exp. Otherfraction≤4.
deriv_deriv_ccmWeilOddPoleChamber_eq forallpositives exact2(A+FA−FC),fromexisting shiftedodd equation.
ccmWeilOddPoleChamber_second_neg (a b)(hfmatchingcutoff)(hbR0≤b):ordinarysecond<0.
differentiableAt_ccmWeilEvenPoleChamber positiveall.
deriv_deriv_ccmWeilEvenPoleChamber_eq underthreshold+hf exact2(A+FA+FC). Even=odd+4cross. Oddsecond<0 andcrosssecond>0 implydifferentiabilityoftheirfirstderivativesviaMathlibdifferentiableAt_of_deriv_ne_zero. Firstderivativeevenidentityislocalpositive-domainEventuallyEq;deriveagain. Avoidedrebuildingprivatefirst-slopeleaf.
ccmWeilEvenPoleChamber_second_pos underthreshold+hf.

4 CCMRestrictedWeilPoleGapShape.lean161lines,6pubtheorems,nodefs.
ccmWeilPoleMatrix_eq_chamber_on_primePower_gap (a b c)(hcIcc)(hfree n≥2 noIsPrimePowwhenentryIoo): ACTUAL A(c)=Acha(c),C(c)=Ccha(c) pair,includingrightendpoint. DiagonalfiniteextraszeroΛorentryzero;crossfollowsprioractualoddidentityanddiagonalpair.
ccmWeilEvenPole_eq_chamber_on_primePower_gap:actualEvenQ(c)=Evench_a(c)wholeclosedgap.
ccmWeilPole_primePower_gap_strict_shape (a b)(haR0≤a)(hfree):StrictConcaveOn Icc oddch∧StrictConvexOn Icc evench. Interiorfunctionequalitywithcurrentcutoffthenordinarysecond sign,standardMathlibconvexderivativecriterionandcontinuity. Nodependenceongaplength.
exists_unique_ccmWeilEvenPole_gap_minimum:forhab,a≥R0,hfree,∃!c:positiveaperture,cIcc∧∀dIcc,actualEvenQ(c)≤actualEvenQ(d). ProvespointforACTUALquadratic,notjustamodel. Compactmin+sourcedomaintransportandStrictConvexOn.eq_of_isMinOn.
ccmWeilEvenPole_gap_nonneg_iff_minimum:givenactualminproperty,hcIcc,wholegapnonnegiffminvalue≥0 (receivernoextraRHassumption).
ccmWeilEvenPole_gap_minimum_stationary:hcIoo,hfree,hmin⇒deriv(Evench_a)c=0. UsesactualsourceidentificationthenIsMinOn.isLocalMin.

## Audits DONE
Scratch/tmp/hgt-pole-age-balance.3YaALh/{API,AtomBalance,SourceBalance,Curvature,GapShape,Axioms}.lean. Allproofscratchespassedforegroundlakeenvlean. FourfinalnamedleafbuildsPASS~7/10/11/12s. All37pubaxiomsEXACT[propext,Classical.choice,Quot.sound]. LintPASSexistinglargefilewarnings,gitdiffcheckPASS. Researchindexrefreshed and'even gap minimum'findsnewactualminsymbols. ProcessinspectionNOLean/Lake. Noliveownedhandle/numerics/Runpod/subagent/backgroundbuild/fullbuild/umbrella/commit.

## Docs DONE
New3-formalized/weil-pole-entry-age-balance.md fullpaperloop/atoms/Green/actualbudgets/ordinarycurvature/minimum/auditallfinished,26thms+11defs. Owntransient1-in-progresscarddeleted. Mainactiveweil-two-pole-compression-prime-error.md containsnewbalance+lateevenmin andvalue-signobligations. FrontierRouteO NEWcurrentparagraphExactaccumulatedlossandoppositegapshapes;existingotherroutecontentpreserved. UniversalSTATUSnewMustretainlossandMustdistinguishendpointvsminimumcontrol compactfacts. FailedpermanententrysigncardstrongestsurvivorstrengthenedwithoutclaimingactualnegativeRHtest. PriorprimepowergapformalcardCurrentfrontierlinksthisnewshape/valuegate.

## Next mathematical actions (not done)
PreferactualVALUEproducer overmoreequivalencebookkeeping. Atuniqueevenminimuminsidegap, exactEvenchderivative=0 canbeexpandedintoliteralprime/ageandGammaquantities. Fromnewbalance, expectedstationarity Seven'(a)=ΣJeven+8ΣΛnexp−b(cosh(a−b)−1),allfinitecutofffixed. Needverifyexplicitfirstderivative/formulateandseeifstationarityhelpsproveevenminimumVALUE≥0. No suchvalueboundproved. Endpointclassificationfromincomingderivativesigns (left/right/interior) couldsupplyprecisephysicaltestlocationsbutalonewon'tcloseRH. Oddvaluegate remainsgenuineprimepowercheckpoints,nowexactV≤Sodd+Bodd. SharedV,oppositeentrytangents mayallowcoupledsourcecomparison; genericpositiveimpulseboundsomitVandcannotbesignproducer.
GlobalallgapenumerationforevenandinitialboundedrangesnotclosedtoRHbynewmin theorem; existingRHcriterionstillrequiresalleven. Do notsilentlyclaimonlyprimepoweroddchecks+evendipswithoutcoveringinitialranges.

## Lean pitfalls
`rw [←halfLog_exp n hn]` acrosswholegoalrewrites ninsideRHSlog too, creatinglog(exp(log n)). Restrictrewrite`conv_lhs=>rw[...]`whendenominatoronlyneeded. FirstGreenantiderivativeuse`simp only[id_eq,Pi.neg_apply]`; FTCendpointdifference−t+sinht vs sinht−t usealgebrasimp. Multipleunfoldtacticnamesfailsifoneabsent,use`dsimp[defs]`foreachgoal. Negativesumtangent`-J*t`vs`-(J*t)` use`simpa only[neg_mul]`. Nat.le_floorlogboundneedsconcretetarget`showReal.log(2:ℝ)≤2*a.1`; le_ofproofalreadyLEno.lefield. `Real.exp_nat_mul b.1 2` use`simpa using`notblindrw(natcastsyntacticdoesn'tmatchliteral2). Forforcepositivityexplicitdenomhden>0needed. Atboundaryequalitylinarithmustincludehc.2 projection. MathlibstrictConcaveOn_of_deriv2_neg/strictConvexOn_of_deriv2_pos requirecontinuousOnandderiv^[2]signinterior; definitionalderivderivmatches. NoC²hypneededbecausestrictsecondderivativeimpliesrelevantdifferentiability.