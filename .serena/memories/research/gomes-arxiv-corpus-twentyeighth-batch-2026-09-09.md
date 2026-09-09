Batch28 COMPLETE; goal ACTIVE. Previous goal turn progress. Added46theorems/5modules/5definitions => cumulative1310theorems/139modules. All5 scratchclean,5 exacttargetbuilds passed,51declaxiomsaudited (only propext/Classical.choice/Quot.sound),51indexed,globalformal lintPASS,83previoussourcehashesunchanged,no ownLean/Lakeprocesses. Allforegroundsessions terminal, no pendinghandles. Artifacts /tmp/hgt-gomes/twentyeighth: progress.json, modules.json,totals.json,build-status.json,axiom-audit.json,corpus-search-audit.json,lint.log. Appended4importsHTGeometryumbrella and1HilbertMetricumbrella, nofull/umbrellabuilds. No commits/subagents/cards/docs.

Userfullgoalremainsunboundedallpaperapplications; nevermarkcompleteatbatchcheckpoint. Standardrules: researchsearchtool beforecode, onlyLean/sources; oneforeground LEAN_NUM_THREADS=1 lake env lean /tmp scratch or lake build exactmodule. No norm_num/decide/native_decide/#eval newcomputations; symbolicring/linarith etc. No extraaxioms or suppliedproofhypotheses. Arbitrarypolynomialdata andcompleteiffclassifications; positiveparameter/finiteprofiledata subtypes continueexistingpattern. Donotkillothersprocesses ormodifytheirfiles. Nextbestgoalturn progress.

SOURCE: general finite polynomial scalar tensor sector prompted by2509.25276v7§5.2 integercharges; normalizationkernel survivor from2607.24901v1§4. No claim literalgaugecategorytheoremtranscription. 2509.25276v7 withdrew earlier equivalence claim, neverrevive.
SeparateHilbertMetricbridge uses2404.10461 sharedgaugeconnectionidea. Reverifiedabstract primary https://arxiv.org/abs/2404.10461 (HTMLunversionedfailedcachemiss). Abstract explicitlyallfieldsunderagivengaugesymmetry shareconnection. Commentcitedsource. Newheaderexplicit2404and2509. Scalar tensor product=pointwisedensity multiplication, notproductmeasure.

MODULES:
All first4 namespace GaloisForLFunctions.HTGeometry.
1 GomesPolynomialExponentialTails (3theorems,0defs):
- gomesConstantExponential_not_integrable_atTop c : ¬IntegrableAtFilter(fun_ℝ=>exp c)atTop.
- gomesPolynomialExponential_linear_envelope_iff P :
  (existsc,c<0AND eventuallyatTop P.evalx≤c*x) iff0<P.natDegreeANDP.leadingCoeff<0.
- gomesPolynomialExponential_integrable_atTop_iff P:
  IntegrableAtFilter(dilatonWeightP)atTop iff0<natDegreePANDleadingCoeffP<0.
Sufficiency: P/x^natDegree→leadingCoeff usingmathlibsame-degreeratio. EventuallyP≤(lead/2)x^degree≤(lead/2)x forx≥1. ExpcomparisonviaIsBigO +exponentialtailintegrability.
Necessity: constantprofile ornonnegativeleadingcoefficient givespositiveconstexp lowerbound; tailconstantintegrability impossible.
ImportsGomesDilatonNormalizationTensor, Mathlib.Analysis.Polynomial.Basic, MeasureTheory.Integral.Asymptotics, Analysis.SpecialFunctions.ImproperIntegrals.

2 GomesPolynomialExponentialIntegrability (8theorems,0defs):
- reflection_integrability P: righttailweight(P.comp(-X)) ifflefttailweightP.
- tail_decay_iff P: righttailintegrable iffTendsto(evalP)atTopatBot.
- integrable_iff P: Integrable(weightP) iff0<P.natDegreeANDEvenP.natDegreeANDleadP<0.
- integrable_decay_iff P: Integrable(weightP) iff evalP→-∞ atboth+∞and-∞.
- gomesDilatonMeasure_finite_iff_integrable P: IsFiniteMeasure rawP iffIntegrableweightP.
- finite_polynomial_iff P: rawfinite iffpositiveevendegree andnegativeleading.
- infinite_polynomial_iff P: rawmass∞ iffNOTthatcriterion.
- gomesDilatonMassNormalized_polynomial_probability_iff P: IsProbabilitynormP iffthatcriterion.
Proof reflection withIntegrableOn.comp_neg_Iic/Ici, localcontinuity; leadingCoeff(Pcomp(-X))=leadP*(-1)^degree andNat.even_or_odd.
Allconstant/zero/odd/even/arbitrarycoeff casesclosed.

3 GomesFinitePolynomialTensorSector (11theorems,2defs):
gomesFinitePolynomialProfiles:AddSubsemigroup ℝ[X], carrier={P|IsFiniteMeasure(rawP)}.
Closureprovedusingintegrable_decay_iff +Tendsto.atBot_add_atBot ateachend (no degreecase split).
abbrev GomesFinitePolynomialProfile := ↥gomesFinitePolynomialProfiles.
_mem_iff coefficientcriterion.
_zero_not_mem, _no_dual P, _no_tensor_failure (nopairoffinitepolynomialinputswithinfiniteproduct).
For P,Q,R:GomesFinitePolynomialProfile:
_probability normP honestprobability.
_normalized_tensor renormalizedReweightP Q =norm(P+Q).
_tensor_probability.
_normalized_eq_iff normP=normQ iffexistsc,P=Q+Cc.
_tensor_cancel norm(P+R)=norm(Q+R) iffnormP=normQ.
_tensor_changes_law norm(P+Q)≠normP (no finitenormalizedidentity).
_tensor_associative renormalizedReweight(P+Q)R =renormalizedReweightP(Q+R).
Finiteclosure nowgeneral, notjustGaussian/quartic.

4 GomesPolynomialTensorChargeSector (11theorems,1def):
gomesPolynomialTensorLogWeight P n:=C(n:ℝ)*P.
_add,_neg.
_finite_iff Pn: finite rawcharged iff0<degreeP AND EvendegreeP AND(n:ℝ)*leadP<0.
_exists_finite_iff P: existfiniteintegercharge iff0<degreeP ANDEvendegreeP. Leadnonzeroforpositive degree;choose+1forneglead,-1forposlead.
_no_finite_dual,_no_tensor_failure,_not_all_finite.
_probability_iff samecriterion.
_measure_tensor literalwithDensity chargeaddition.
_gaussian and_quartic exactbridges oldtensorlogb n fromP=oldgeneratorb.
Positiveeven generators havefinitehalf-lattice oppositeleadingsign;odd/constantgeneratorshavenone.

5 formal/GaloisForLFunctions/HilbertMetric/GomesReflectedQuarticTensor.lean, namespace HilbertMetric (13theorems,2defs):
imports existing SecondLevelConcavityFifthRootNoGo, newFinitePolynomialTensorSector, GomesQuarticChargedConnection.
gomesQuarticKernelMeasure:=volume.withDensity(ofReal quarticGaussianKernel).
gomesQuarticReflectedMeasure:=volume.withDensity(ofReal quarticGaussianReflectedProfile).
OldkernelF=exp(-x^4), oldreflectedP=exp(-2x^4).
_density bridges F=weight(gomesQuarticLogWeight1),reflected=weight(gomesQuarticLogWeight2).
KernelMeasure_eq=rawH1.
ReflectedMeasure_eq=raw(H1+H1).
Bothfinite (originalquarticfinitecriterion, thennewgeneralsubsemigroupclosure).
ReflectedMeasure_tensor=KernelMeasure.withDensity(ofReal(F(-x))).
Reflected_connection: driftH2=(2:ℂ)•driftH1.
Kernel_ground_density norm²(gomesQuarticChargeGroundState positiveone)=oldkernelF.
Kernel_ground_line actualHamH1kernel exactscalarlineofthatstate.
Kernel_and_reflected_probability bothliteralinverse-mass-scaledmeasuresprobability.
Kernel_reflected_probability_distinct fromnewfinite-sector tensorchangeslaw.
gomesQuarticCurvatureFailure_with_tensor_geometry:
 bothmeasuresfinite AND existsnonzeroSchwartzψ withHamH1ψ0AND∀x||ψx||²=F x AND oldfifthRootDividedDropCurvatureNumerator oldreflected(1/2)<0.
Reusesalreadyclosednegativecurvaturetheorem; no newcomputationalproofofit.
Interpretation: finitegauge/tensordensitystructureandexactgroundstatecoexistwithpriorcurvaturefailure, soaddedconditionsdon'trepairit. No attempttoretirespecificRHroute/card.

CURRENT LEAN API LESSONS (TailApi.lean clean verifiednames):
- Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q hdeg : P.eval/Q.eval→P.lead/Q.lead.
- degree_eq_natDegree hp,degree_X_pow,leadingCoeff_X_pow,natDegree_C_mul scalar_ne_zero.
- isEquivalent notneeded; ratio +eventually_lt_const +le_self_pow₀ hx1 degree_ne_zero.
- Rootle_self_pow failsforℝ (needsMulLeftMono); usele_self_pow₀.
- tendsto_atBot_mono' requires explicitfilter FIRST: tendsto_atBot_mono' atTop hb ht.
- Continuous.stronglyMeasurableAtFilter needs explicit μ andfilter; e.g hc.stronglyMeasurableAtFilter volume atTop.
- Real.volume_Ici hasimplicitendpoint; use Real.volume_Ici withoutapplyinga.
- integrableOn_Ici_iff_integrableOn_Ioi hasdefaultproofarg, so use Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h (field.mprfails).
- eq_C_of_natDegree_eq_zero h :P=C(P.coeff0). Never simp[hp] recursively: it rewritesP insidecoeffP indefinitely. Use congrArg(evalx) hp then simp[eval_C]atthatfact.
- Polynomial.C_coeff_zero nonexistent; coeff_C_zero works.
- IntegrableOn.comp_neg_Iic takesintegrabilityonIci(-c),outputscomposedf(-x)onIic c; comp_neg_Ici viceversa. Forreflectionsetc=-a andsimpneg_neg.
- When simp doesn'teta-expand standalone dilatonWeightP, changegoal toexplicitfunx=>exp(P.evalx); then simpa. finitewithDensity integrabilityproofneededtrailingrfl aftersimp.
- AddSubsemigroup constructorcarrier membershipmust change toIsFiniteMeasure at hP hQ andgoal BEFORE rw.
- Filter.Tendsto.atBot_add_atBot doesexist (generatedto_additive fromatBot_mul_atBot).
- Nat.even_or_odd;Even.neg_one_pow/Odd.neg_one_pow; reflectiondegree simp[natDegree_comp,natDegree_neg,natDegree_X,mul_one].
- Positivesubtype1 elaboration inHilbertMetric needed ⟨(1:ℝ),by change(0:ℝ)<1;exactzero_lt_one⟩. Plainzero_lt_one orbyexactwasstuck NeZero1 metavariables. Combinedexistentialuseslocal a:Set.Ioi0, thenexplicit groundstatehelpersa; avoidsheartbeat200kdefeqtimeout.
- Measurabilityproofvia composedcontinuousfunctions needed simp[Function.comp_def,Pi.pow_apply,id_eq].
- SchwartzMap.smul_apply deprecated; root smul_apply aloneworks.

SEARCH/READ provenance:
Corpusqueries polynomial exponential integrable18 allreviewed;polynomial leading integrable2;finite tensor Gomes17;dilaton integrable3. Broad evenleading137 refinedtoLocalizedPerturbationHyperbolicity lines120-164 (signhelpers,notimported). No exp-of-polynomial integrabilityresult inmathlib rg.
polynomial charge Gomes19;finite polynomial Gomes7;quartic reflected Gomes0. Newgenericinteg/charges notduplicate.
Read HilbertMetric.SecondLevelConcavityFifthRootNoGo lines1-35,224-272,185-198 (negativeproof onlyexistingreuse);symbolslist. Read existing quarticnorm²signature inDilatonEinastoMoments21-26.
Don't readcards/docs orrepeatalreadyreadsource.
Next candidates: actualquotientoffinitenormalizedlaws ascommutativecancellativesemigroup; orconstructexp(P/2)SchwartzMapforgeneralfinitepolynomialprofile, extendingmeasurefinite iffnonzeroSchwartzgroundbeyondGaussian/quartic. Ifselected buildmissinginfra insteadpivot. Searchfirst. Goalactive.