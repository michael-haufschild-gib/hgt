# Gomes arXiv corpus experiment — batch33 verified

GOAL ACTIVE, no budget. Checkpoint progress, never full goal completion. User wants as many closed mechanical applications/experiments from arXiv2607.24901,2509.25276,2404.10461 as possible. Continue next survivor. No docs/cards; only Lean + corpus search. No computation tactics/new axioms/holes. Data parameters and bundled finite profiles, global iff classifications. One foreground Lean process, wait terminal; use lake env lean scratch; only exact lake build module for dependencies/final audit, no full or umbrella builds. Append finished imports. No commit/push/subagents. Preserve others' files/processes. Session init/manual/skills already done; mission repeated thisturn. New AGENTS changed research search to hybrid/deep; see search section below.

## Authoritative verified checkpoint
/tmp/hgt-gomes/thirtythird/:41newtheorems,3defs,6modules; cumulative1521theorems/168modules. Prior1480/162. All6 scratch logs empty, exact foreground builds terminal0,source=scratch,44declarations axiomaudited only propext/Classical.choice/Quot.sound,44indexed,globalformal lintPASS,111prior sourcehashes unchanged. No own Lean/Lake processes. Last AxiomAudit session31070 terminalexit0. No live processes; progress.json live_session removed. All6imports wired into formal/GaloisForLFunctions/HTGeometry.lean. Exact artifacts build-status.json,counts.json,totals.json,axiom-audit.json,corpus-search-audit.json,prior-source-audit.json,process-audit.json,progress.json. Build replay only unrelated LabeledBoundarySimplex94unnecessarySimpa warning; global lint141preexistinglargefilewarnings,noerrors. No full builds.

## Discovery
Forced polynomial ODE Bprime=A*B+C c has exact dichotomy: Bconstant with A*B=-C c; or A=0 with Bprime=C c. Degree(Bprime-C c)<degreeB fornonconstantB, and B divides that difference, so it vanishes.
F(U)=Uprime+U². F(U)=F(V)+C k iff identical inputs with k0, two constant inputs with squared differencek, or opposite affine inputs U=-V with Uprime=C(k/2).
Dilaton potential profiles thus have trichotomy: same derivative with k0; two affine profiles; opposite quadratic profiles up to constants, Hsecond=C k.
Lifted to actual Schwartz Hamiltonians: shift is equality on every actual state. One everywhere nonzero Gaussian state detects the entire operator shift. Centered potential VHx-VH0 is exact invariant after discarding scalar energy origin.
Finite-mass P,Q cannot have nonzero energy shift. Centered potential still recovers connection, canonical normalized profile, ground line. Nonzero third derivative gives rigidity against arbitrary K, not merely finiteK.
Tensor cross term: V(H+K)=VH+VK+Hprime*Kprime/2. All affine probes remain blind to every pair of affine profiles after energy centering. In contrast, base centered potential and centered potential after H+X² determine the full first-order connection. Add H.eval0 to get an injective record on ALL real polynomials. This is an experimental scalar consequence of paper reconstruction/tensor ideas, not full gauge-category equivalence.

## APIs (namespace GaloisForLFunctions.HTGeometry)
Paths formal/GaloisForLFunctions/HTGeometry/<module>.lean.

1 GomesForcedPolynomialODE (4theorems), imports GomesPolynomialHamiltonianFibers:
- gomesPolynomialDerivative_forced_iff A B c:
 Bprime=A*B+C c ↔(Bprime=0∧A*B=-C c)∨(A=0∧Bprime=C c).
- _forced_profiles A B c:
 same equation↔(∃b,B=C b∧A*C b=-C c)∨(A=0∧∃b,B=C c*X+C b).
- _forced_nonconstant_iff (B:{B:ℝ[X]//Bprime≠0}) A c:
 equation↔A=0∧∃b,B.val=C c*X+C b.
- _forced_nonzero_coefficient_iff (A:{A:ℝ[X]//A≠0}) B c:
 equation↔∃b,B=C b∧A.val*C b=-C c.

2 GomesPolynomialRiccatiEnergyShifts (5theorems), imports above:
- gomesPolynomialDerivative_square_shift_iff U V k:
 (Uprime=Vprime∧U²=V²+C k)↔(U=V∧k=0)∨∃a b,U=C a∧V=C b∧a²=b²+k.
- gomesPolynomialRiccati_shifted_parts_iff U V k:
 F U=F V+C k↔(Uprime=Vprime∧U²=V²+C k)∨(U=-V∧(U-V)prime=C k).
- _shifted_iff U V k:
 F U=F V+C k↔(U=V∧k=0)∨(∃a b,U=C a∧V=C b∧a²=b²+k)∨(U=-V∧Uprime=C(k/2)).
- _shifted_profiles_iff U V k:
 same first2alternatives, last ∃a,U=C(k/2)*X+C a∧V=-U.
- _energy_shift_surjective k:∃U V,F U=F V+C k. Explicit U=C(k/2)X,V=-U.

3 GomesDilatonPotentialEnergyShifts (6theorems), imports above:
- gomesDilatonConnectionPolynomial_constant_iff H a:CPH=C a↔Hprime=C(2*a).
- _derivative_constant_iff H a:CPHprime=C a↔Hsecond=C(2*a).
- gomesDilatonPotential_shifted_polynomial_iff H K k:
 (∀x,VHx=VKx+k)↔potentialPolynomialH=potentialPolynomialK+C k.
- _shifted_derivatives_iff H K k:
 scalar shift↔(Hprime=Kprime∧k0)∨(∃a b,Hprime=C(2a)∧Kprime=C(2b)∧a²=b²+k)∨(Hprime=-Kprime∧Hsecond=C k).
- _shifted_profiles_iff H K k:
 scalar shift↔((∃c,H=K+C c)∧k0)∨(∃a b c d,H=C(2a)X+C b∧K=C(2c)X+C d∧a²=c²+k)∨∃a b c,H=C(k/2)X²+C a X+C b∧K=-H+C c.
- _energy_shift_surjective k:∃H K,∀x,VHx=VKx+k. Explicit oppositequadratics.

4 GomesSchwartzHamiltonianEnergyShifts (10theorems,2defs), imports above:
- def gomesDilatonEnergyShift H K k:Prop :=∀ψ:𝓢(ℝ,ℂ),HamHψ=HamKψ+(k:ℂ)•ψ.
- gomesDilatonEnergyShift_gaussian_potential_iff H K k:
 HamH gaussian=HamK gaussian+k•gaussian ↔∀x,VHx=VKx+k.
- _potential_iff H K k:shiftHKk↔∀x,VHx=VKx+k.
- _gaussian_iff H K k:shiftHKk↔oneGaussianStateEquality.
- _zero_iff H K:shiftHK0↔HamH=HamK (actualCLMequality).
- _profiles_iff H K k:exact same profiletrichotomy as module3.
- _symm_iff H K k:shiftHKk↔shiftKH(-k).
- _unique_iff H K a b:(shiftHKa∧shiftHKb)↔shiftHKa∧a=b.
- def gomesDilatonCenteredPotential H x:=VHx-VH0.
- gomesDilatonEnergyShift_centered_iff H K k:
 shiftHKk↔centerH=centerK∧k=VH0-VK0.
- gomesDilatonCenteredPotential_eq_iff H K:
 centerH=centerK↔∃k,shiftHKk.
- gomesDilatonEnergyShift_surjective k:∃H K,shiftHKk.

5 GomesFinitePolynomialEnergyRigidity (6theorems), imports above+GomesHamiltonianNormalizationBoundary:
- gomesFinitePolynomialEnergyShift_iff P Q k (P,Qfiniteprofiles):shiftP.val Q.val k↔superP=superQ∧k=0.
Proof affinecase contradicts finiteProfile_curvature_ne_zero. Oppositequadraticcase would make bothP and-P finite by affineTiltfiniteinvariance, contradict no_dual.
- gomesFinitePolynomialCenteredPotential_connection_iff P Q:centerP=centerQ↔superP=superQ.
- _canonical_iff P Q:centerP=centerQ↔gomesFinitePolynomialNormalizedProfileP=...Q.
- _ground_iff P Q:centerP=centerQ↔∃c:ℂ,c≠0∧groundP=c•groundQ.
- gomesDilatonEnergyShift_higher_curvature_iff (H:{H:ℝ[X]//Hthird≠0}) K k:
 shiftH.val K k↔(∃c,H.val=K+C c)∧k0.
- gomesDilatonCenteredPotential_higher_curvature_iff sameH K:
 centerH.val=centerK↔∃c,H.val=K+C c.

6 GomesCenteredHamiltonianTensorProbes (10theorems,1def), imports above:
- gomesDilatonPotential_tensor_add H K x:
 V(H+K)x=VHx+VKx+Hprime.evalx*Kprime.evalx/2.
- gomesDilatonCenteredPotential_tensor_add H K x:
 center(H+K)x=centerHx+centerKx+(Hprime.evalx*Kprime.evalx-Hprime.eval0*Kprime.eval0)/2.
- _constant H c:center(H+C c)=centerH.
- _affine a b:center(C a X+C b)=0 (functionzero).
- _affine_probes_blind a b c d r s:
 center((C a X+C b)+(C r X+C s))=center((C c X+C d)+(C r X+C s)).
- _quadratic_probe_iff H K:
 (centerH=centerK∧center(H+X²)=center(K+X²))↔superH=superK.
Proof obtain polynomial (Hprime-Kprime)*X=0 from pointwise centered cross terms; Xnezero and nozeroDivisors force derivativeEq.
- _all_tensor_contexts_iff H K:(∀R,center(H+R)=center(K+R))↔superH=superK.
- def gomesDilatonCenteredTensorRecord H:=(centerH,center(H+X²)), pairℝ→ℝfunctions.
- _eq_iff H K:recordEq↔∃c,H=K+C c.
- _origin_iff H K:(recordEq∧H.eval0=K.eval0)↔H=K.
- _augmented_injective:Injective(funH=>(recordH,H.eval0)).

## Search changes and evidence
New AGENTS default research hybrid; --mode deep includes candidate_lemmas/source_arguments/proof_ideas/ingredient_sets and coverage/freshness. Keep user Lean-only constraint: do not read prose/cards/research-note passages. Deep60s query 'polynomial derivative equals polynomial multiple plus constant Riccati constant difference degree divisibility' completed terminal0 but partial=True, unfinisheddeadline/source_refresh. Coverage55880files,24483pending, compiler mostlysource_only/pending, semantic5184/1302182. Returned20candidatelemmas+5sourcearguments allinspected, unrelated;proof_ideas/ingredient_sets empty. Do not claim exhaustive semantic search. Runtime is tool-ownedMLX, not Lean; do not kill it.
Supplemented with lexical searches + exhaustive sourcepatternrg. All30polynomialRiccati hits and55polynomial derivative constant hits reviewed. Existing ExpPolynomialRational rationalexponentialconstant,ProximityFirstOrderAutonomous degree>=2autonomousobstruction,DifferentialCharacteristicPseudoReduction degreeoneconstantderivative are related but notforcedODEclassification. Sourcepatternmatches onlyourpreviousresults, unrelatedRittcomposition, BesselrationalRiccati.
BroadRiccati lexical query returned710; initial100read, then narrowed mechanism query polynomialRiccati(all30) instead of claimingall710exhausted. Hamiltonianenergyshift9knownfinite-dimensional/gaugeorigintheorems, no dilatonclassification. Tensorpotentialenergy0, Gomespotentialtensor1unrelatedendpointmeasure; direct sourcegrep foundnogeneralV(H+K)formula. Newfinal44declarations indexed via --mode lexical; check_index.py modified to explicitlylexical, avoidinghybridbudget.
Nextquadraticfinite --moduleGomes returned1unrelatedFockWindowMass. Nextquadraticintegrable73namesallreviewed; mostlytransport/RHintegrablequadraticfamilies, integrable_exp_quadratic inBesselExteriorEnvelope is onlysimpleGaussian. For finitequadraticcriterion reuse existing general finite-polynomial coefficientcriterion instead of new integrability proof.

## APIs and working traps
ForcedOdeApi.lean clean terminal0. `have:=@Polynomial.Name` alone produced unresolveduniverseerrors; use `@Polynomial.Name.{0}`. Verified eq_zero_of_dvd_of_degree_lt,degree_derivative_lt,degree_sub_le,degree_C_le,eq_C_of_degree_le_zero,eq_C_of_derivative_eq_zero. Signatures in ForcedOdeApi.log, nonempty due#checks; audit checks absenceerror, notempty.
- degree_sub_lt means leading-term cancellation lemma, notgenericbound. Use `(degree_sub_le _ _).trans_lt (max_lt hder (degree_C_le.trans_lt hpos))`.
- ODE `Bprime=AB+Cc`,goalAB=-Cc orAB0 needs `linear_combination hd-h`, noth-hd.
- Current forcedODE+all6newmodules passedfirst fullscratchattempt; onlyAPI universefix required.
- `simp only[add_zero,funext_iff]` works for zero energyshift iff CLMequality afterpotentialbridge.
- Gaussianprobeproof: change stateevaluation smul to complexproduct; use dilatonHamiltonianCLM_apply twice; linear_combinationhx; cancel gaussianSchwartz_nezero via gaussReal_pos; exact_mod_cast. Reverse push_cast;ring.
- `simp only [pow_two,derivative_mul,derivative_X,one_mul,mul_one,eval_add,eval_X,add_zero,mul_zero] at ht` normalizesquadraticprobe cross term; nlinarith closes polynomialproductevaluation.
- Priorbatch pitfalls stillapply: eq_C_of_derivative_eq_zero selfreference useletc/rwonce, never simp[hc]; secondDerivative_constant_iff at0 requires `(by simpa using hz)` forHsecond=C0, notrawhzHsecond0.
- All audithelpers inherited batch32 with pathsupdated; finalize_batch priorpaththirtysecond; metadata removeslive_session afterterminal. Lintstring `formal lint passed`, lowercase. Filterpsoutput onlyownLean/Lake commands; never dumpunrelatedprocesscommandlines.

## Next conjecturing loop (goal remains fullscope)
1 For finiteP and arbitraryK, shiftP.val K k forces k<=0. Nonzero k<0 arises only whenP is finitequadratic andK oppositeupconstant. Prove exactfinitequadraticcriterion byremovingaffineterms withgomesPolynomialAffineTilt_finite_iff, then coefficientfinitecriterion onC(k/2)X². Verify natDegree_C_mul,natDegree_pow,leadingCoeffAPIs scratch. This yields entirecenteredpotentialfiber of finiteP: onefiniteconnectionclass, and exactlyoneextra infiniteoppositeclass inquadraticcase. Don't pivot overmissinginfrastructure.
2 Classify centeredpotentialfibersglobally fromenergytrichotomy: constantprofile shifts, allaffineprofilessharingzerocenteredpotential, and oppositequadraticpairs. Constructfaithfulcenteredenergyquotientifuseful; reconstructenergyoffset fromorigin.
3 ForcedODEpositive survivor: conjecture (∃B,Bprime=AB+C c) iff c=0 orAprime=0. c0→B0; Aconstantnonzero→constantparticularsolution;A0→CcX. Forcnonzero,forceddichotomyforcesAconstant. Uniqueexistence iffA≠0∧(c0∨Aprime0);A0affinesolutions havefreeintercept. Canlead topolynomialdifferentialoperator inversion via localnilpotence, withoutcomputationtactics.
4 Energycenteredtensor boundary isnowclosedpositive theorem. Potentialfurthergeneralization: exactclassificationforarbitrarycommonprobeR, notjustquadratic: connectionEq ORconstantprobe withbaseenergyEq ORaffineprobe/affineprofiles. Quadraticproofalreadyprovidesuniversalrestoration. Searchexistingbeforegeneralizing.

## Attribution
2607.24901v1 section4 reconstruction and2509.25276v7 section5.2 common-base tensorcomposition motivate scalarresults. Neverrevivev1-v6withdrawnequivalence.2404.10461geometry-first foundationalpaper. Sourcesreverifiedbatch32 https://arxiv.org/html/2607.24901v1#S4 and https://arxiv.org/html/2509.25276v7#S5.SS2. No fullgauge-categorytranscriptionclaim. Tensorherepointwise sameℝbase, notproductmeasure.
