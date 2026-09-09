# Gomes arXiv corpus experiment — batch31 complete; goal ACTIVE

Unbounded usergoal continues. Previous turn made verifiedprogress; nevermarkcompleteatbatchcheckpoint.
Papers2607.24901,2509.25276,2404.10461. Explicitly experimental scalar tensor/connection/half-density reconstruction; notliteralclaimsaboutfullgaugecategory.2509.25276v7 withdrewv1-v6equivalence;neverreviveit.
PriorAPIs: mem:research/gomes-arxiv-corpus-thirtieth-batch-2026-09-09 and mem:research/gomes-arxiv-corpus-twentyninth-batch-2026-09-09.

## Verified totals
Batch31:43theorems/6modules/7defs =>1437theorems/156modules cumulative.
Artifacts /tmp/hgt-gomes/thirtyfirst.
All6 clean scratchchecks,all6 exactforegroundbuilds,all50declsaxiomaudited withonlypropext/Classical.choice/Quot.sound,all50indexed,globalformallintPASS,99priorhashesunchanged,noownLean/Lakeprocesses.
All6 appendedtoGaloisForLFunctions/HTGeometry.lean;numbrellabuild.
build-status/totals/counts/axiom-audit/process-audit/prior-source-audit/progress JSONs recordevidence.
Targetbuildsreplayed unrelatedLabeledBoundarySimplex94unnecessarySimpa warning;newmodulesclean.
No commits/subagents/fullbuild/devserver.

## Persistent rules
DirectLeanonly,nocards/docs. Corpussearch scripts/formal_tools.py research before newcode.
No computations/norm_num/decide/native_decide/holes/addedaxioms. Symbolicring/linear_combination/nlinarith andstructuralproofsused.
OneforegroundLeanata time:LEAN_NUM_THREADS=1 lake env lean scratch;lake build exactmoduleonlyneededoleans/finalaudit.WaitterminalbeforeanotherLean;timeoutnotcompletion.
Preserveunrelatedsources/processes.Keepbriefmeaningfulchatupdates<=60sec.Storeprogress/tmpacrosscompaction.
GoalACTIVE;nodowngradedsuccessorcompletionclaim.

## Main new result
Forfinitepolynomiallog-profiles degree<=d, rawmoments0..d recovereverycoefficient.
Normalizedmoments1..d recoverexactlyconstant-log-amplitudeclass,sharedconnection,canonicalnormalizedprofile,projectivegroundline,andentireSchwartzHamiltonian/scalarpotential.
Noanalyticcontinuation/all-momentassumptionneededforfiniteprofileidentification.
A finite momentrecord isinjective onboundedrawprofiles;normalizedrecordhasexactconnectionequivalencekernel.
No claimofstability/numericalinverse/surjectivityorfiniteobservabilityofALLL2vectors.

## Six newmodules, namespaceGaloisForLFunctions.HTGeometry
1.GomesPolynomialExpSeparation
- gomesPolynomialSeparationDensity H K x :=
 (H.evalx-K.evalx)*(dilatonWeightHx-dilatonWeightKx).
- _nonneg forallH K x.
- _zero_iff: density0↔H.evalx=K.evalx.
- _continuous,_symm (functions).
- _integrable P Q (finiteprofiledata), fromtwo polynomial-amplitudeintegrals.
- gomesPolynomialSeparation P Q :=∫x densityP.valQ.valx (volume).
- _nonneg,_zero_iff (E=0↔P=Q),_pos_iff(E>0↔P≠Q),_symm.
9theorems/2defs. Strictmonotonicexp,continuousa.e-zero=>everywherezero usingvolumeopenpositive. Itisaseparationfunctional, notclaimedmetric.

2.GomesPolynomialFiniteMomentIntegration
- gomesPolynomialMeasure_polynomial_integrable P A :Integrable A.eval rawP.
- gomesPolynomialMeasure_integral_polynomial P A:
 ∫A.eval rawP=∫A.evalx*exp(P.evalx)volume.
- gomesPolynomialMeasure_integral_eval_prefix P d
 (A:{A:ℝ[X]//A.natDegree<=d}):
 ∫A.evalrawP=Σn∈range(d+1),A.coeffn*(∫x^nrawP).
- gomesPolynomialMeasure_prefix_polynomial_iff P Q d:
 (∀n<=d,momentrawP n=momentrawQ n)↔
 ∀A:{A//degree<=d},∫ArawP=∫ArawQ.
- gomesPolynomialSeparation_integral_difference P Q:
 E(P,Q)=∫(P-Q).evalrawP-∫(P-Q).evalrawQ.
5theorems.

3.GomesPolynomialFiniteMomentReconstruction
- gomesPolynomialSeparation_eq_moment_sum P Q:
 E=Σn∈range(maxdegPdegQ+1),(P-Q).coeffn*(momentP n-momentQ n).
- gomesPolynomialMomentPairing_pos_iff:abovefinitesum>0↔P≠Q.
- gomesPolynomialMeasure_finite_moments_reconstruct P Q:
 (∀n,n<=maxdegPdegQ→momentrawP n=momentrawQ n)↔P=Q.
- gomesPolynomialMeasure_distinguishing_finite_moment:
 P≠Q↔∃n<=maxdegree,momentsdiffer.
- abbrev GomesBoundedPolynomialProfile d :=
 {P:GomesFinitePolynomialProfile//P.val.natDegree<=d}.
- gomesBoundedPolynomialMomentRecord d P:Fin(d+1)→ℝ,
 n↦∫x^n.val rawP.val.val.
- _injective d.
5theorems/2defs(abbrevincluded).

4.GomesFinitePolynomialNormalizedProfile
- gomesPolynomialNormalizationShift P :=
 Real.log ((rawPmass)^-1).toReal.
- gomesFinitePolynomialNormalizedProfile P :=
 gomesFinitePolynomialTilt P 0 (NormalizationShiftP).
- _val =P.val+Cshift.
- gomesPolynomialNormalizationShift_exp:
 ofReal(exp shift)=rawPmass^-1.
- gomesFinitePolynomialNormalizedProfile_measure:
 raw(normalizeP)=massNormalizedP.
- _natDegree retainedexactly.
- _mass=1.
- gomesPolynomialNormalizationShift_normalized P :shift(normalizeP)=0.
- gomesFinitePolynomialNormalizedProfile_idempotent.
- _eq_iff P Q :normalizeP=normalizeQ↔normmeasureP=normmeasureQ.
- _connection:super(normalizeP)=superP.
9theorems/2defs.
PositivityofreciprocalmasstoReal usesfiniteP.property andrawmassnezero; noextrahypotheses.
Canonicalmodulebuildtook39sec;wasproperlywaited,nostaleprocesses.

5.GomesNormalizedFiniteMomentReconstruction
- gomesFinitePolynomialProfile_finite_moments_eq_iff P Q:
 normalizedprefix0..maxdegreeequal↔normP=normQ.
- _finite_moments_connection_iff:prefix↔superP=superQ.
- _finite_moments_ground_iff:prefix↔∃cℂ,c≠0∧groundP=c•groundQ.
- _positive_finite_moments_connection_iff:
 onlyn>0andn<=maxdegree needed;0thmomentdischargedbyactualprobabilityinstances.
- gomesBoundedPolynomialNormalizedRecord d P:Fin d→ℝ,
 n↦∫x^(n.val+1)normP.val.val.
- _eq_iff d P Q:recordsEq↔superP=superQ.
- _canonical_iff:recordsEq↔normalizeP=normalizeQ.
- gomesFinitePolynomialProfile_finite_moments_tensor_cancel P Q R:
 normalizedprefixforthesummedprofilesP+R,Q+R
 (cutoffmaxoftheirsummeddegrees)eq↔originalnormalizedprefixeq.
7theorems/1def.

6.GomesFinitePolynomialHamiltonianReconstruction
- gomesDilatonHamiltonian_potential_eq_iff H K:
 HamH=HamK↔dilatonPotentialH=dilatonPotentialK.
 ALLpolynomials,notonlyfinite. ForwardprobeactualgaussianSchwartznonzeroeverywhere.
- gomesFinitePolynomialHamiltonian_connection_iff P Q:
 HamP=HamQ↔superP=superQ.
 ForwardcommonHam=>groundP∈kernelHamQ=>samegroundline=>sameconnection.
 Reverseconstantlogshift=>sameHam.
- gomesFinitePolynomialPotential_connection_iff P Q.
- gomesFinitePolynomialHamiltonian_ground_iff P Q.
- gomesFinitePolynomialHamiltonian_canonical_iff P Q:
 HamEq↔normalizeP=normalizeQ.
- gomesFinitePolynomialProfile_finite_moments_hamiltonian_iff P Q:
 positive-orderprefix1..maxdegreeeq↔HamEq.
- _finite_moments_potential_iff:same↔potentialfunctionsEq.
- gomesBoundedPolynomialNormalizedRecord_hamiltonian_iff d P Q.
8theorems.

## Important verified API / source reads
PrefixApi.lean clean.
- Polynomial.eval_eq_sum_range' hn x:evalxA=Σi∈range n,A.coeffi*x^i,hn:natDegreeA<n.
- integral_finset_sum deprecated;useintegral_finsetSum.
- Polynomial.natDegree_add_C unconditional:natDegree(P+Cc)=natDegreeP.
- natDegree_sub_le P Q;natDegree_X_pow_le n.
- Continuous.ae_eq_iff_eq (μEXPLICIT) hf hg:
 a.eequal↔functionsequal whenμ.IsOpenPosMeasure.
- IntegralwithDensitycongrgoalhadlambdaapplications;rwcouldnotfindtoRealterm.
 Insert explicit change to (ofRealweight).toReal•Aeval=Aeval*expPeval before rw.
- integral_eq_zero_iff_of_nonneg hf hfi.
- ENNReal.ofReal_toReal hneTop;toReal_pos hne0 hneTop.
- ExactdilatonHamiltonianCLM_apply H ψ x:
 HamHψx=-deriv(derivψ)x+(dilatonPotentialHx:ℂ)*ψx.
 ReadDilatonSchwartzHamiltonian62–69.
- ReadGomesDilatonConnectionReconstruction26–35 (gaussianprobeproof) and71–74 (Hamconstant).
 gaussianSchwartz_apply thenComplex.ofReal_ne_zero.mpr(gaussReal_posx).ne'.
- gomesDilatonMeasure_constant H c:
 raw(H+Cc)=ofReal(exp c)•rawH. ReadMeasureReconstruction55–73.
- ExistingGomesDilatonDualShiftRigidity theoremnamessearched:
 dual_supercharge,dual_adjointCharge,dual_factorization,dual_potential,dual_hamiltonian_apply,
 dual_commutator_apply,dual_constant_shift_iff,secondDerivative_constant_iff,dual_quadratic_rigidity.
 DoNOTduplicate; bodiesnotreadthisbatch.
- Source/mathlibsearch justfound Polynomial.dvd_derivative_iff:
 P∣derivativeP↔derivativeP=0.
 Read .lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivative.lean748–769.
 Assumptions[SemiringR][NoZeroDivisorsR]. Usesdegree_derivative_lt.
 Nameexists/sourceverified; notyetscratchAPIchecked thisnewcandidate(thecurrentPrefixApi predatesthisdiscovery).

## Next selected conjecture / proof plan (do not pivot if infra missing)
Classify equality of ALLpolynomialdilatonpotentials/Hamiltonians,withoutfinite-massrestriction.
Expectedalternatives:
 H=K+Cc,
 OR H,K affinewithoppositeslopes (e.g.H=-K+Cc andH.natDegree<=1).
Finiteprofileuniquenessisthenonebranch;oppositeaffineslopeambiguityexplainswhyfiniteconditionmatters.

Best abstract core tobuildfirst:
ForrealpolynomialsU,V,
 U.derivative+U^2=V.derivative+V^2
 iff U=V OR (U=-V AND U.derivative=0).
SetD=U-V,S=U+V. EqualitygivesD'+D*S=0,soD|D'.
UseexistingPolynomial.dvd_derivative_iff toforceD'=0.
ThenD*S=0. IfD=0firstbranch.
ElseS=0;differentiateS=0andtogetherD'=0givesU'=0.
Allsymbolicring/linear_combination, no degreeinfrastructureactuallyneedednow.
InstantiateU=C(1/2)*H.derivative,V=C(1/2)*K.derivative; theirRiccatievaluationsaredilatonPotential.
Couldalsofirstproveweighted2D'+DS formforunscaledderivatives, butabstractscaleddriftavoidsfractionsin coreargument.
TranslateU'=0intoHaffineusingexistingsecondDerivative_constant_iff specializedzero,orstandardPolynomialderivativezeroclassification.
ThenapplynewgomesDilatonHamiltonian_potential_eq_iff toactualoperators.
Expectednontrivialpositiveclassification,notmerelycounterexamples.
Potentialextensions:globalcounterexamples showingnormalizedcollapsedrecords cannotrecoverHamiltonianoutsidefinite; exacttwo-pointfibersforconstantpotential.

Searches thisbatch:
- polynomial moment prefix9hits allreviewed;unrelatedatomic/finitequadraticmomenttests.
- exponential monotone integral11hits allreviewed;transportcouplings.
- normalized polynomial profile --moduleGomes12hits allreviewed;nonecanonicalrep.
- dilaton hamiltonian equality0;dilaton potential reconstruction0.
- hamiltonian potential --moduleDilaton2hits:dual_hamiltonian_apply andHamiltonian_energy.
- polynomial Riccati21hits fullyreviewedacross2pages;mostlyBesselobstructions,jetpolynomials,Jacobicompletions.
- Riccati uniqueness1hitBuresWasserstein.OperatorGeometricMean.gm_unique(operatorRiccati),notmatchingpolynomialfiberclassification.
SearchbeforewritingnewLeanagainasneeded.
