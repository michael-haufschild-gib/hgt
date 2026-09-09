# Gomes arXiv corpus experiment — batch30 complete; goal ACTIVE

User's unbounded /goal continues. Previous turn made verified progress. Never mark complete at a batch checkpoint. Papers2607.24901,2509.25276,2404.10461. These are explicitly experimental scalar tensor/connection/half-density reconstruction applications; do not claim papers literally state these polynomial theorems. 2509.25276v7 withdrew v1-v6 equivalence; never revive it.
Previous APIs: mem:research/gomes-arxiv-corpus-twentyninth-batch-2026-09-09 and mem:research/gomes-arxiv-corpus-twentyeighth-batch-2026-09-09.

## Verified totals and evidence
Batch30:40theorems/5modules/5defs =>cumulative1394theorems/150modules.
Artifacts /tmp/hgt-gomes/thirtieth.
All5 scratchclean; all5 exact-module foreground builds; all45declaxiomaudit only propext/Classical.choice/Quot.sound; all45indexed; global formal lintPASS;94prior sourcehashesunchanged; no ownLean/Lakeprocesses.
Newmodules appended to GaloisForLFunctions/HTGeometry.lean, no umbrella build.
build-status.json,totals.json,axiom-audit.json,process-audit.json,prior-source-audit.json,counts.json,progress.json record evidence.
Builds of MomentReconstruction/Germ replayed unrelated existing LabeledBoundarySimplex.lean94 unnecessarySimpa warning; no newmodulewarnings orerrors.
No commits, subagents, fullbuilds or devserver.

## Rules
DirectLean only; no cards/docs. Corpussearch scripts/formal_tools.py research before newcode. No computations/hole/addedaxioms. One foreground Lean at a time, LEAN_NUM_THREADS=1 lake env lean scratch; lake build exactmodule only neededoleans/finalaudit. Wait process terminal before anotherLean. Preserveunrelatedsources/processes. Use/tmp progress.json acrosscompactions. Conciseupdates <=60sec. Do notendgoalatbatchcheckpoint.

## Five new modules, namespace GaloisForLFunctions.HTGeometry
1. GomesPolynomialAffineTilt
- gomesFinitePolynomialProfile_degree_gt_one P :1<P.val.natDegree.
- gomesFinitePolynomialPerturb P (Q:{Q:ℝ[X] // Q.natDegree<P.val.natDegree}):finiteprofile valP+Q. _natDegree,_leadingCoeff retainedexactly.
- gomesPolynomialAffineTilt H t c:=H+(C t*X+C c).
- gomesFinitePolynomialTilt P t c:finiteprofile, sameaffinetiltvalue.
- gomesPolynomialAffineTilt_add H s a t b: successiveparametersadd.
- _inverse H t c:tilt(tiltH t c)(-t)(-c)=H.
- _finite_iff H t c:finite rawtilt↔finite rawH forALLH.
- _schwartz_iff:∃fSchwartz=funtilexp ↔∃fSchwartz=expH.
- _ground_iff:nonzeroSchwartzkerneltilt↔nonzeroSchwartzkernelH.
- _probability_iff:probabilitynormalizedtilt↔probabilitynormalizedH.
9theorems/3defs. Natdegree>1 usesEven witness andnlinarith; noomega.

2. GomesPolynomialExponentialMoments
- gomesPolynomialMeasure_exp_integrable P t:Integrable(exp(t*x))rawP.
  useswithDensityintegrability andaffine-tilt rawintegrability; exactReal.exp_add.
- gomesPolynomialMeasure_entireExponentialMoments P:
 RHTower.HasEntireExponentialMoments(rawP).
- gomesPolynomialNormalized_finite H :IsFiniteMeasure(normH), ALLH.
- gomesPolynomialNormalized_exp_integrable H t, _entireExponentialMoments H.
  Infinite-mass input normalizeszero; zero has allmoments too! Keepthiscollapseexplicit.
- gomesPolynomialMeasure_exp_memLp_two P t, _pow_memLp_two P n.
- gomesPolynomialNormalized_exp_memLp_two H t, _pow_memLp_two H n.
UsesexistingRHTowerentiremomentconsumers.9theorems.

3. GomesPolynomialMomentL2Completeness
For rawP withPfinite, and normalizedH forANYH:
- gomesPolynomialMeasure_L2_moment_integrable P (g:Lpℝ2rawP) n:
 Integrable(x^n*g x)rawP.
- _L2_moments_zero_iff P g:
 (∀n,∫x x^n*g x rawP=0)↔g=0.
- _L2_polynomial_dense P:
 (RHTower.realMonomialSpan rawP (entire P)).topologicalClosure=⊤.
- gomesPolynomialMeasureMomentMap P:Lpℝ2rawP→ₗ[ℝ](ℕ→ℝ),
 toFun g n=∫x x^n*g x rawP.
- gomesPolynomialMeasureMomentMap_injective P.
Normalizedanalogues replace stemgomesPolynomialMeasure withgomesPolynomialNormalized, binderH:ℝ[X],mu=normH. IncludesnormalizedMomentMapdefinition/injectivity.
8theorems/2defs; actuallinear/injectiveobservations, noaddedregularitypremises.
RawL2zeroiffusesexistingallmoment-rigidity withLp.stronglyMeasurable andLp.memLp, localfiniteinstance. map_add/map_smul usecoeFn_add/coeFn_smul a.e identities andintegrability.

4. GomesPolynomialMomentReconstruction
- gomesPolynomialMeasure_moments_reconstruct P Q:
 (∀n,∫x x^n rawP=∫x x^n rawQ)↔P=Q.
- gomesPolynomialNormalized_moments_eq_iff H K:
 allnormalizedmomentsequal↔normH=normK.
- _moments_reconstruction H K:
 same↔(∃c,H=K+Cc)∨(rawHmass∞∧rawKmass∞).
- gomesFinitePolynomialProfile_moments_constant_iff P Q:
 samefinitemoments↔constantdifference.
- _moments_connection_iff: same↔superP=superQ.
- _moments_ground_iff: same↔∃c:ℂ,c≠0∧groundP=c•groundQ.
- _moments_tensor_cancel P Q R:
 allmomentsnorm(P+R)=norm(Q+R)↔allmomentsnormP=normQ.
7theorems. ConsumesROOT HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window (NOTnestedGaloisForLFunctions.HTGeometry).

5. GomesPolynomialMomentGerm
- gomesPolynomialMeasure_complexMGF_entire P:
 AnalyticOnNhd ℂ (complexMGF id rawP)univ.
- gomesPolynomialNormalized_complexMGF_entire H: samefornormALLH.
- gomesPolynomialMeasure_complexMGF_germ_iff P Q z:
 (MGFrawP=ᶠ[𝓝z]MGFrawQ)↔P=Q.
- gomesPolynomialNormalized_complexMGF_germ_iff H K z:
 correspondingnormgerm↔normH=normK.
- _complexMGF_germ_reconstruction H K z: germ↔constantdiff ORbothrawmass∞.
- gomesFinitePolynomialProfile_complexMGF_germ_connection_iff P Q z:
 normgerm↔superP=superQ.
- _complexMGF_germ_ground_iff: normgerm↔projectivegroundequality.
Allsourcepoints z:ℂ, notjustzero.7theorems.
Usesentireanalyticidentity theorem eqOn_of_preconnected_of_eventuallyEq andMeasure.ext_of_complexMGF_id_eq. Exactanalyticgerm, notfiniteprecisionobservations.

## Existing source read this batch; do not repeat
RHTower/EntireExponentialMomentPolynomialDensity.lean:
lines1–23,159–236,237–end. Previousbatchread24–95;96–158notyetread.
- namespaceRHTower.
- HasEntireExponentialMoments mu:=integrableExpSet id mu=univ.
- ae_eq_zero_of_all_moments_of_entireExponentialMoments {mu}[finite] hmu {g} hgmeas hgMemLp hmom :g=ᵐ[mu]0.
- realMonomialSpan mu hmu :=spanℝ(range(realMonomialLp mu hmu)).
- realMonomialSpan_closure_eq_top mu [finite] hmu.
HardyStieltjesDeterminacy.lean lines18–29,51–106:
ROOTnamespaceHTGeometry.
measure_eq_of_moments_eq_of_bilateral_exponential_window
 {μν}[finiteμ][finiteν]
 (hμzero:0∈interior(integrableExpSet idμ))
 (hνzero:0∈interior(integrableExpSet idν))
 (hmom:∀n,∫x x^n μ=∫x x^n ν):μ=ν.
ExistingproofanalyticMGFstripuniqueness.
GomesDilatonMassNormalization.lean1–30,90–96 read:
 normalizedmassμ=μmass^-1•μ;
 gomesDilatonMassNormalized_zero_iff H :normH=0↔rawmass∞.
 gomesDilatonMassNormalized_eq_iff H K :normeq↔constantdiff∨bothmass∞.

## API pitfalls / verified
- integrableExpSet isdefinition {t|Integrable(exp(t*Xω))μ}. There is NO mem_integrableExpSet lemma. Use integrable_of_mem_integrableExpSet ordefeq.
- integrable_withDensity_iff_integrable_smul' hf hflt:
 Integrableg(μ.withDensityf)↔Integrable(funx=>(fx).toReal•gx)μ.
- Integrable.smul_measure h (hc:c≠∞) (cimplicit).
- not_lt.mp gives ∞≤mass, NOTmass=∞; usele_antisymm le_top (not_lt.mp...).
- Lp.coeFn_zero yields g0x=0x (zerofunction); rw[hx,mul_zero] failed because0xnotrewritten. rw[hx]; exact mul_zero _ succeeds.
- MemLp.mul' hf hφ usesφ*f, notf*φ; HolderTriple2,2,1 inferred.
- integral_const_mul (r)(f) has noIntegrablepremise.
- Lp.coeFn_add gk, coeFn_smul cg supplya.e identities.
- rootHTGeometry versusGaloisForLFunctions.HTGeometry collision: explicitly_root_.HTGeometry forHardytheorem.
- ComplexMGF analyticOnNhd on{z|z.re∈interior(expSet)}; simp[window=univ,interior_univ,Set.mem_univ,Set.setOf_true] yieldsentire.
- AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hU (hz:z∈U) hlocal :EqOnfgU.
- Measure.ext_of_complexMGF_id_eq hasbothfiniteinstances.
- TiltApi.lean checked allusedhelpernames andisclean.
- One researchcall accidentallyusedformal/ cwd (scriptnotthere); fixedtoroot. Avoid.
- Existingnewmodulebuildlogs canreplay unrelatedLabeledBoundarySimplex warning; nofileeditwarranted.

## NEXT SELECTED CONJECTURE (announced to user; pursue/build)
Bounded-degree polynomial log-densities may be identifiable by finite momentprefix up to
d=max(P.natDegree,Q.natDegree), rather thanallmoments. Raw moments n=0..d shouldrecoverP=Q; normalizedmoments shouldrecoverconstantdiff/connection.
This is a stronger statement for the finite-parameter profilefamily, not for arbitraryL2vectors.

Candidatepaperproof:
1. Integrand (P.evalx-Q.evalx)*(exp(P.evalx)-exp(Q.evalx))≥0 bystrictmonotonicexp; zero iffP.evalx=Q.evalx.
2. It is integrable byBatch29 gomesPolynomialAmplitude_integrable forfourpolynomial-amplitude/exponentialproducts.
3. Prefixmomentsequality throughd gives equality ofintegrals ofpolynomialP-Q againstrawP/rawQ, viafinitepolynomial expansion (buildmissingfinite-moment integrationinfrastructure).
4. Integralofnonnegativeintegrand=0; continuity andfullsupportvolume forcepointwisezero; polynomialfunext =>P=Q.
5. Normalizedversion: realize eachnormalizedlawasrawexp ofprofile shiftedbylognormalizationconstant. Differencepolynomialstilldeg≤d; applyraw argument andconcludeconstantdiff. Needbuildcanonicalnormalizedprofileifabsent; searchfirst.
Alternative strictconvexityofpartition/logpartition, butmonotoneproduct proofusesalreadybuiltinfrastructure.
Do NOT pivotbecauseinfrastructuremissing.

Initialsearches before next code:
- polynomial finite moments injective:1hitunrelatedSpectrumGenericity(power-sum finiteatomic).
- moment identifiability:1hitPowerSumTorelli.exists_powerSum_ne_of_ne (finiteatomic).
- broad exponential family276hits, refinedratherthanfullyreviewed.
  ReflectedExponentialFisher hasReflectedExponentialFamily structure fromsearchbutnotread; narrowedexponential family moment modulequery0hits. Do notclaimbroadexhaustiveaudit.
- polynomial moment germ4unrelatedhitsreviewed.
Searchspecificfinite-prefix/entropy/strictmonotonicity polynomialmoments before newLean.
