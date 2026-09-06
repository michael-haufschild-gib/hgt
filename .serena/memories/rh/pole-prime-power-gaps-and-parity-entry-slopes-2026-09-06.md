# Actual prime-power gap criterion and opposite parity slopes

GOAL ACTIVE, RH not proved/disproved. This turn is PROGRESS: 19 public theorems +4 definitions in4finishedleaves. Previousturn: `mem:rh/pole-prime-entry-handoff-and-discrete-odd-criterion-2026-09-06`. No numerics, subagents, commits, full/umbrella builds. No liveownedprocess. Sharedtree includes unrelated ongoing HTGeometry edits; preserve.

## Current exact proof chain and missing sign
All-aperture |C(a)|≤A(a) → square-root P(T)=∫0..T(exp t−ψ(exp t)) → bounded actual unit-Riesz resolvent → mathlib RH, converse alreadyclosed. Priorinteger-entryoddcriterion is now strengthened: for any startinga≥2, all actual oddenergiesonc≥a are≥0 iffQodd(a)≥0 ANDQodd(log n/2)≥0at EVERY GENUINE PRIME POWER n withentry≥a. Allzero-Mangoldtintegercheckpointsremoved. Negative tailwitness iffnegativestart ORnegativeprimepowercheckpoint. Notfirstzero/firstfailurelocationclaim! NewRHcriterionretainsalleven,odd0<a≤2,oddprimepowerentriesabove2. Thoseactualsignsremainopen.

## Corpus origin / theorem mechanism
Read exact currentfrontier+universal and newpriorentrymodules. Searchfound SuzukiScrewDistributionalKernel.exists_affine_screwPrimeSum_Ioo. Itsactualstatement assumesavoidanceof ALLintegerloglocations; ourliteralMangoldtatomrepresentation strengthenssupportto genuineprimepowersandretainsmovingexponentialmatrix. No genericfixedstatetheoremisusedasactualsourcebridge. MathlibsupportArithmeticFunction.vonMangoldt_eq_zero_iff/pos_iff and finiteprimeexistence/findGreatest/find verifiedTHISscratch.

## Finished files namespaceRHTower
All formal/GaloisForLFunctions/RHTower, wiredafterOddIntegerEntryCriterion beforeThetaTiltLogDensity inRHTower.lean.

1 CCMRestrictedWeilPoleCutoffAtoms.lean (129lines;6pubtheorems+4defs)
Defs ccmWeilPoleDiagonalSmooth(s)=2κsinh s−exp s+(2s+1)exp(−s)+8s sinh s+B1primitive(s); ccmWeilPoleCrossSmooth(s)=κ2s+2s²+(2sinh s)²+B0primitive(s).
ccmWeilPolePrimeDiagonalAtom(n,s)=2Λn(exp s/n−exp(−s)); crossAtom=Λn(1+1/n)(2s−log n).
ccmWeilPoleChamberDiagonal_eq_sum_atoms and Cross_eq_sum_atoms: frozenmatrix=smoothsource−Σallvisibleliteralatoms. Privatepsi_sumconvertsChebyshevIcc0toIcc2 usingΛ0=Λ1=0.
ccmWeilPolePrimeAtoms_zero_of_not_primePow: bothatomsidenticallyzeroeverysifnnotprimepower. ccmWeilPolePrimeAtoms_zero_at_entry: bothzeroatentryn,usingexpb/n=exp−b.
ccmWeilPoleChamberDiagonal_succ_cutoff and Cross_succ_cutoff: ANYreferencea,b withfloorb=floora+1 havefrozenfunctiondifference−newatom atEVERYs. Thesearefullmatrixidentities,notjustatentry.

2 CCMRestrictedWeilOddPrimePowerGap.lean (190lines;4pubtheorems)
hfree explicit: ∀n≥2,a<log n/2<b→¬IsPrimePow n.
ccmWeilPoleChambers_eq_on_primePower_gap: a≤c<b andhfree ⇒ENTIREfrozenAfunctions at a,c equal ANDENTIRECfunctions equal. Newvisibleentries liein(a,c]⊂(a,b),hencezeroΛ. Finset.sum_subset exact.
ccmWeilOddPole_eq_chamber_on_primePower_gap: forc∈[a,b], actualQodd(c)=Ech_a(c). Atbnewnonzeroatomcanonlybeexactlyatentryandthuszero. Preservesbothboundarymasses/polars/allprimepowers.
ccmWeilOddPole_pos_between_primePower_entries:2≤a,a<c<b,hfree,actualendpointsQ≥0 ⇒actualQodd(c)>0.
ccmWeilOddPole_nonneg_primePower_gap_iff_endpoints:2≤a≤b,hfree ⇒actualQ≥0wholeIcc iffendpointpair≥0. NOgaplengthbound.
Proof usesfunctionequalitywithc'sownmodelthenexistingEch_c''−Ech_c<0atthepointc≥2. Frozenmodela continuousIcc. Privatecompactminimum/secondderivlemmasfollowpriorproof. Noassumedglobalactualdifferentiabilityatprimeentry.

3 CCMRestrictedWeilOddPrimePowerCriterion.lean (125lines;3pubtheorems)
ccmWeilOddPole_nonneg_tail_iff_primePower_entries (a)(ha≥2): tailnonneg iffstartnonneg+genuineprimepowercheckpointnonneg.
ConstructN=floor exp2c≥2 byexptangent. p=Nat.findGreatest IsPrimePow N, p≥2 because2prime; q=Nat.find leastq>Nprimepower,existsEuclidprimeaboveN. l=entryp≤c<r=entryq. Max/minexcludeeveryprimepowerinside(l,r). Applygapcriterion[l,r] ifa≤l, otherwise[a,r]. Nofinitecomputationalprimecertificate.
riemannHypothesis_iff_even_and_odd_primePower_entries: exactactualRH iffalleven ∧allodd≤2 ∧allprimepowerentryoddabove2. Usesexistingparitycriterionandnewtail.
ccmWeilOddPole_negative_tail_iff_primePower_entry: existentialnegativewitnesslocalizedtostartorprimepowerentry. Logicalnegationofequivalence; DOESNOTsayfirstzeroatentry.

4 CCMRestrictedWeilPoleEntrySlopes.lean (141lines;6pubtheorems)
Atentryb=log n/2,hasDerivAt_ccmWeilOddPole_entry_atom: derivativeof2(−d_n+c_n)=4Λn(1−exp−b)².
hasDerivAt_ccmWeilEvenPole_entry_atom: derivativeof2(−d_n−c_n)=−4Λn(1+exp−b)².
ccmWeilOddPole_entry_slope_pos_iff and ccmWeilEvenPole_entry_slope_neg_iff: strictrespective signiffIsPrimePow n (n≥2).
hasDerivAt_ccmWeilOddPoleChamber_succ_jump: derivativeofdifferenceEch_b−Ech_a foradjacentcutoffsatnewentryexactpositivecoefficient.
hasDerivAt_ccmWeilEvenPoleChamber_succ_jump: samefor2(Ach_b+Cch_b)−2(Ach_a+Cch_a),exactnegativecoefficient.
Privateentry_inverse1/n=exp(−b)² viaexp2b=n andexp_nat_mul. Atomderivativesexplicit. Thesearederivativesofentrycorrections/adjacentfrozenexpressions; globalenergyneednotbedifferentiableatnonzerojump. Oldoddprimecontributionstillreversessignlater(previousformalno-go),soentryslopeisnotpermanentsign.

## Validation DONE
Scratch /tmp/hgt-pole-prime-gaps.vZ58TE/{API,API2,Atoms,Gap,PrimeCriterion,Slopes,Axioms}.lean. Proofsallsuccessfirstpropercwdchecks; oneinitialrootcwdAPIcommandfailedmodulelookupthenfixed. Foregroundlakeenvlean only. NamedfinalleafbuildsPASS ~7.7/12/11/9.2s. All23publicdeclaxiomauditsEXACT[propext,Classical.choice,Quot.sound]. FormallintPASSexistinglargefilewarnings,gitdiff--checkPASS. ResearchindexrefreshedqueryprimePowergapretrievesnewnames. ProcesspscheckNOLean/Lake. Noownedliveprocess,numerics,Runpod,subagent,commit,backgroundbuild,umbrella/fullbuild.

## Docs DONE
New3-formalized/weil-pole-prime-power-gaps.md: dependencyclosedpaperproof,5conjectureloopsteps,atoms,gap,primepowercriterion,slopes,allfinalauditdone. Owntransient1-in-progress/weil-pole-prime-power-gaps.md deleted.
FrontierRouteO sectionrenamedFull odd-source comparison and genuineprime-powercheckpoints,statesstrongestcurrentcriterion+slopes+opensigns. Mainactive1-in-progress/weil-two-pole-compression-prime-error.md nowtargetsactualgenuineprimepowercheckpointsign,notintegerdiscretization. UniversalSTATUSoldCannotpropagateentrysign strengthenedwithpowergap+negativewitness; newMustdistinguishparityentryresponse exactformulas. Failedpermanententrysigncardstrongestsurvivorupdated. PriorformalentrycardCurrentfrontierlinksnewstrongersupportreduction.

## Next work (NOT done)
Actual prime-power endpoint signs are now main odd sourcegate,notmoreinertintegerbookkeeping. Opposite parity impulse law suggestsderiveexactglobalintegrating-factor/Greenbalanceforthecompleteoddfunction,retainingnegativebetween-entryforcingandpositiveMangoldtimpulses. No suchsignedaggregateestimateproved. Do notassumeupwardentryslopesimplytailpositiveorfirstzeroentry; bothwouldoverclaim. Couldcompareendpointvalues/slopejumpswithactualprime–Gamma budgetsO≤G+R; primeshigherpowersmustremainunlessseparatelyprovedremovable. Evenallandinitialoddrangealsoopen.
One-sidedChebyshevsourcebridgespreviouslyreadhaveupperboundsfordyadicThetaERRORINCREMENTS,notourintegratedP/poleenergy; noautomaticone-sidedRHconnector. Searchwholecorpusforactualsignedprimitive/oscillation/Greenidentitiesbeforeconjecturingnextproducer.

## Lean mechanics
Nat.findGreatest_spec hN Nat.prime_two.isPrimePow; Nat.le_findGreatest samegives2≤p; Nat.findGreatest_is_greatest hpn hnN excludesp<n≤N. Nat.find_min hex hnq excludesN<n<q. ExistenceNat.exists_infinite_primes(N+1). IsPrimePow.one_ltverified. new_entry_boundsusesNat.lt_of_floor_lt pluslogiffexp,givesa<log n/2≤c. Wholefunctionequalitiesallowrwunderderivtwice. UseDivExprsimp/ring andexp_nat_mul exact. Privategenericminimumcodeisduplicatedfrompriorleaf; ifcontinuedgeneralizationneedsreuse, factorproperlyratherthanaddingmorecopies. No proofnamesrecalledwithoutscratchverification.