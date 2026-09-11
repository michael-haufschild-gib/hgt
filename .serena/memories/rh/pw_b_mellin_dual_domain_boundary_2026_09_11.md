Goal ACTIVE, RH NOT PROVED. Iterations33–34 fully audited. No #print axioms; user forbids. One foreground ownedLeanprocess atatime, scratch lake env lean, targetedleaf lake build, nofullumbrella/numericalexperiments. NoownedLean/research/index/lintprocessrunning. Workspace /Users/michael/Documents/code/hgt, Leanformal.
Stableprevious memory rh/pw_b_full_original_current_adjoint_2026_09_11 nowhasobsoleteLIVEsection; thismemoryupdatesit.

Iteration33 priorclosed:
GammaAdjointGainTransposition33public, originalcompleteforwardresponse/fullgaintriangle→reciprocaltransposition;target46s.
GammaFullPairedAdjoint4public;target124s. Fullunconditionaloriginalsourcepairing:
g_z=M_z/Q, w=exp(-x-1/x)/x.
∫w conjg_z*(TiltCurrent_v/Q)
 =∫w g_v*conj(SameSourceCurrent_z(1/x)/Q(1/x))
 +∫w conjg_z*g_v*2logx.
All3integralsL1. Completefinitecutoff F=R+E+(C-L) retainedemptyincomingconstantloss. NooperatorclosureorXioccurrenceclaimed.
Bothsourcesexactscratchcopy/uniquewiring/all37indexed/lintPASS.
Stage3cards pw-b-gamma-adjoint-gain-transposition.md, pw-b-gamma-full-paired-adjoint.md.
Fulldetails prior memory.

Iteration34 NOWCOMPLETE:
File formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMellinDualDomain.lean
Exact /tmp/pwb-gamma-mellin-dual-domain.lean, 1publicdef7publictheorems ~104lines.
Imports GammaFullPairedAdjoint; exactcheckedbytespromotedandoneumbrellaimportafterFullPairedAdjoint.
Scratch session87043 exit0nodiagnostics (earlier47820/32135failedandterminal).
Targetsession59690 EXIT0,57s.
Index76087 EXIT0;all7publicnamescheckedAPI.
Lint68331 EXIT0 formalpassed,existinglargefilewarnings.
Logs /tmp/pwb-gamma-mellin-dual-domain-{check,build,index,lint}.txt;eachcorresponding -exit.txt0.
Ownedresearch8356 and62757 EXIT0. Noownedprocessrunning. Linkresolution, exactsource/wiring,scopeddiffcheckPASS.
Noaddedaxioms/sorry/opaque/unsafe, no#axiomprinting, nofullbuild.

Mathematicalattack andpositive survivor:
OriginalMellinkernel k_s(x)=(x:ℂ)^(s-1)Q(x) againstg.
Its EXACTsquareddualweight normk²/w=x^(2Re(s))*exp(-x+1/x).
Define pwGammaMellinDualDensity (a x:ℝ)=x^(2a)*exp(-x+1/x).
Foranyn:ℕ and0<x<1,
D_a(x)>=exp(-1)/n!*x^(2a-n).
Chooseexists_nat_gt(2a+1); divergentpowercomparisonprovesnotIntegrableOnD_a(Ioo0 1)forEVERYa.
ThereforetheliteralMellinkernelhasnonintegrablesquareddualdensityatEVERYcomplexs.
Positive survivors:
- exactliteraldualweightformula (allcomplexs,x>0)
- absoluteD_aadmissiononeveryIcc c d withc>0 (emptyallowed)
- completearithmeticfamily forallz, IntegrableOn (w*norm(M_z/Q)²)(Ioi0), fromnormofthealreadyadmittedcompleteP_z,z.
Thiskills ONLY proposedfiniteglobalweightedCauchy–Schwarzdualmassconstant.
DoesNOTyetproveeveryMellinreader/continuousextensionisunbounded; needRieszidentification/explicitnormalizedtests. DoesNOTprovefailureofsource-specificMellinintegral in itsadmittedhalfplane. NorestrictiononXi zerosderived.
Allsourcecoefficientsretained.

Exact7publicnames:
pwGammaMellinDualDensity_pos
pwGammaMellinDualDensity_lower
pwGammaMellinDualDensity_not_integrable
pwGammaMellinDualDensity_compact_admission
pwGammaMobiusGroundQuotient_weighted_square_integrable
pwGammaMellinDualDensity_source_eq
pwGammaMellinDualDensity_source_not_integrable

Proofpitfallsresolved:
- Powerintegrability lemma namespace intervalIntegral.integrableOn_Ioo_rpow_iff.
- Explicit IntegrableOn annotation before .norm.congr_fun avoidsAnd.congr_fun.
- dsimp only before norm_mul rewrites onbeta-lambda.
- simp only[Nat.cast_ofNat] afterReal.rpow_natCast/rpow_mul fornatural2vsreal2.
- pow_div_factorial_le_exp x⁻¹ hxinv n; simplify inv_pow,div_eq_mul_inv,mul_inv_rev,mul_one,one_mul,mul_comm.
- Exactkernel norm =x^(s.re-1/2)*exp(-x),thenrpow_add/mulandactualQ/wexponentialquotient.
Noasymptoticexpdependencyneeded.

Docs:
Stage3 pw-b-gamma-mellin-dual-domain.md (MOVEDfromstage1,linksupdated).
NARROWstage5 pw-b-global-mellin-dual-estimate.md recordsfailure, strongestpositive survivors/paper+Leanclosed,fullaudit,andunboundedreaderclaimscope.
Journal pw-b-source-orientation-attack.md iteration34 finalaudit.
Stage1reversiblepairing endsMellinevaluationsection.
Currentfrontier PW-Bopencore nowincludesexactdualobstruction whileadmittingallsourceweightednorms.
UniversalSTATUS newroute-independentMustentry: checkdualnormseparatelyfromsourceadmission; compactboundnotuniformendpointbound; generalcontinuousextensionclaimsneedduality/tests. NOrouteworklogentry.

Research:
docs/drafts/pipeline/1-in-progress/pw-b-gamma-mellin-dual-searches.json raw2deepqueries:
(1) Mellinsourcemeromorphicresiduedualeigenfunctionalcontinuationincidence:partial732050,errors[],proofideas[],proposeddualnumberresidue+unrelatedcontourmechanismnotapplicable. ActualMobiusMellinContinuationWallcandidatekeepsAnalyticOnNhdpremise.
(2) reciprocalexponentialMellinfunctionalinversedensityunbounded:partial732074,errors[],proofideas[];generatedMellininversion/SoninmechanismrequiresoriginalMellinadmission,verticalL1,band/rapiddecayhypotheses. TheseareNOTPWproofs.
Directactualcorpusfactorialboundandpowerintegrabilityprovefreshboundary.
BroadarXivintertwining:
2608.01485v1ElberLheem,primaryintro/Prop2.3.6read finiteclassicalgroupinducedreps;characterrestrictionsrequiredforantiinvolution,othercasesseparatereduction. NoPWsourceidentification.
2606.04383JiangWangWu abstractonlyGNS/KMSquantumMarkov;HTMLfailedso nodetailedprooftransfer.
Journalrecordslinks/limitations (<200wordspersource).
Previousiteration33raw4queriesinforward-gain-searchesJSON andSeptembertransportpapersrecorded.

RHchaincurrent:
PWsource→FEsigneddefect→FULLPAIREDSOURCEADJOINTclosed→justifiedphysicalcommonoperator-domain/closure→actualXioccurrenceinDIFFERENTfieldorweakrealization→independentfixed-gradeWardbalance→RH.
PairedK=A-B-2log candidate; NOTA-B-log.
Earlierrawandunit-ground-correctedpointwisescalarGammaansatz excludedALLz byoriginalcurrentvaluation. Neverrevive.
CurrentliteralMellinbridgeonlyRe(s)>-1/2,Re(z+s)>1; fullatomnormsumexactlastthreshold;actualendpointgivenlargezexcludesfurtheradmission; sourceweightnormdoesNOTextendMellindomain.
Next meaningfulmathematicalattack: explicitendpointcontrol/strongerorweakreader withsourceprovenanceanditsK-action beforeclaimingXiincidence. CouldstrengthennewdualdensityobstructiontoactualunboundedreaderusingRiesz/normalizedcompacttests, butthisisnotyetprovedandshouldnotbeclaimed. Needavoidspendingallworkonabstractdomainreceivers; actualXiincidence/independentbalancearehardproducer.
