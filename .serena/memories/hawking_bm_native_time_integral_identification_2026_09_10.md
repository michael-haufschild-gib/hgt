# HB native Bochner time equation — 2026-09-10

## Goal and discipline
RH goal remains ACTIVE, unbounded and NOT achieved. No blocker. No subagents.
Full chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Ultimate hard target: 2 Omega(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV amplitudes and all onset/horizon/AdS/temporal/cusp currents.
NO Git commands (even reads), NO launch.sh, NO numerical computations. Frontier map READ ONLY. Analytical work only.
One foreground owned Lean/Lake process at a time. A session remains live until observed terminal output or authoritative missing handle + process gone. Scratch lake env lean; final audit lake build exact module only. No full/umbrella/dependency builds. Only new public axiom checks. Wire umbrella but never build it.
Corpus search direct documented research tool; spaces AND, --any OR, broad own terms and deep mechanism queries. Inspect declarations, candidate_lemmas, source_arguments/methods, proof_ideas, ingredient_sets, partial/compiler freshness. No search implementation/help unless actual failure. API names must be checked against toolchain in scratch.
Toolchain Lean4.32.2. No architecture/testing docs. Session init done. update_plan unavailable. No skills applied.
Prior memory hawking_bm_native_operator_identification_2026_09_10 contains previous operator step.

## New proved result, fully audited and installed
1. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeResidualAdmission.lean:
   Added ONLY public wrapper nativeJointResidualField_joint_continuous, line770, preserving all existing private construction. Joint continuity in real time × (real radius × upper half-plane).
2. NEW formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeTimeIntegralIdentification.lean, 243 lines:
   - nativeJointTimePrimitive_eq_bochner, line92:
     actual L2 literal primitive = integral_0^t ((t-u):C) • nativeJointResidual q s amplitude u.
     All Xi occurrences, arbitrary complex rate/amplitude, every real t.
   - causalCuspSourceVector_native_forcing_ae, line187:
     complete original physical source vector =ae literal nativeResidualStaticForcing at physicalRate.
   - nativeJointIntegratedForcing_eq_bochner, line210:
     actual L2 integrated forcing = integral_0^t ((t-u):C) • causalCuspSourceVector q branch a u.
   - nativeJointResidual_bochner_covariance_equation, line231:
     B U(t)+(1-B) P2 U(t)=B P2 F(t),
     B=formEmbeddingCovariance jointEmbedding,
     U=nativeJointResidual q (physicalRate q branch) a,
     F=causalCuspSourceVector q branch a.
No supplied native-response/forcing-identification premise. Actual three principal amplitudes, cutoff commutators, horizon factor and original product measure retained.

Proof:
- Generalized PRIVATE l2_integral_eq from NativePhysicalIdentification526–597 to arbitrary second-countable Borel spatial type and sigma-finite measure. Test against arbitrary L2 vector g. innerSL commutes with Bochner interval integral. Slice AE equality identifies literal representatives. Bound integral norm inner(g,u_t) <= ||g||²+||u_t||² gives time×space product integrability. Fubini swaps. Scalar pairing commutes with literal time integral. Negative times via interval reversal.
- Need literal residual joint continuity; it was private. Added public wrapper in original leaf; no duplicated long analytic construction.
- Literal forcing is jointly continuous via original squareResidual/cutoffCommutator continuousOn composed with coordinates, oddSource from timeReducedCoefficient, and radialResponse.
- principalNullResponse_physical_ae (FullNativeWave987) identifies principal physical representatives. principalCutoffRadialOp_ae (PrincipalCutoffTime22) supplies horizonCoordinate times physical coefficient on negative ray. l2SeparatedProduct_ae plus angular cutoffCommutator_memLp supplies product.
- horizonCoordinate x=1/cosh(x)^2 from actual radialUnit and cosh²−sinh²=1.
- On negative ray oddSource equals timeReducedCoefficient. Add main vector plus all three physical cutoff vectors.
- Apply generalized integral lemma to forcing, then substitute both exact identities into prior nativeJointResidual_covariance_equation.

## Audits — finished, do not repeat
- Complete admission and new module candidates passed lake env lean scratch.
- API scratch have := @Name with explicit universe zeros passed. Pure polymorphic have without universe args produces inference errors; names themselves existed.
- Exact final lake build NativeResidualAdmission: 2 jobs, 115s.
- Exact final lake build NativeTimeIntegralIdentification: 2 jobs, 136s.
- Exactly five new public #print axioms checks all: [propext, Classical.choice, Quot.sound].
- Sources + five artifacts each (.olean,.ilean,.trace,.olean.hash,.ilean.hash) installed byte-identically and reverified. No private/server artifacts generated.
- One umbrella import after NativeOperatorIdentification in formal/GaloisForLFunctions/RHTower.lean.
- Global scripts/formal_tools.py lint EXIT0, formal lint passed; existing large-file warnings. Prior five unreachable-module errors are gone due concurrent work; we did not modify those modules.
- 39 real relative links across 3 affected reports checked. Strip inline/fenced code when checking links; inline indicator[-T,T](x) is not a link.
- No frontier/STATUS edits. No numerical work, Git, launcher, umbrella build or dependency rebuild.

## Reports
Authoritative new: docs/drafts/pipeline/3-formalized/hb-native-time-integral-identification.md.
Updated current:
- docs/drafts/pipeline/1-in-progress/hb-native-cusp-inverse-identification.md, completed primitive subsection and end status.
- docs/drafts/pipeline/3-formalized/hb-native-operator-identification.md, remaining comparison and current lint.
Native/physical causal-response equality, complete current cancellation and RH remain UNPROVED.

## Next direct attack: physical bounded time equation, then uniqueness
Physical source/response APIs:
- ThetaCuspHawkingBMJointSourceForcedCausal:
  causalJointForcedResponse13 is undo fixed exponential shift times causalDatum.
  support16 a.e negative.
  weighted_memLp29: expRay(causalResponseShift+1) • U in L2(time).
  integrable37: absolute Laplace convergence for Re w>shift+1.
  laplace45, laplace_original56.
  operator74: actual Uhat in original jointEnergyOperator.domain and
    A Uhat+(w²−1)•Uhat=Fhat.
  It does NOT establish norm continuity of physical representative.
- ThetaCuspHawkingBMJointSourceCausalCuspSource:
  F26, continuous30, zero_nonpos35, laplace_integrable42, laplace58.
- Original A = inverse of B. Apply B to actual transformed operator equation:
  Uhat+(w²−1) B Uhat=B Fhat.
  Desired time equation: B U+(1-B)P2U=B P2F a.e.

POSITIVE SIMPLIFICATION FOUND THIS TURN:
Use weighted L1 Laplace uniqueness, avoiding separate weighted L2 bounds on every primitive.
For sigma>0, k(t)=t exp(-sigma t)1_(t>0) in L1. Damped P2f = k * damped f. Tonelli gives
  ||exp(-sigma t) P2f||_L1 <= sigma^(-2)||exp(-sigma t) f||_L1.
Complex Fubini gives Laplace(P2f)(w)=w^(-2)Laplace(f)(w).
Actual physical U and F already have required weighted L1 admission in common right half-plane.
Scalar L1 Fourier uniqueness ALREADY PROVED:
formal/GaloisForLFunctions/HTGeometry/FourierUniquenessL1.lean, 128 lines, read WHOLE.
Root namespace HTGeometry (NOT GaloisForLFunctions.HTGeometry).
  ae_eq_zero_of_fourierIntegral_eq_zero, line49:
    {g:R→C}, Integrable g, (∀x, Fourier g x=0) → g=ae0.
  ae_eq_of_fourierIntegral_eq, line111.
Proof mollifies by normalized bump, Fourier convolution, continuous inversion, then a.e approximate identity.
No need re-audit old axioms.

For Hilbert-vector probe removal WITHOUT global separability:
Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean359, READ statement:
  Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero:
    hf:Integrable f μ,
    (∀s, MeasurableSet s → μ s<∞ → integral_s f=0) → f=ae0.
For each finite-measure s, every inner product of integral_s f vanishes by scalar probe AE vanishing and innerSL integral interchange. Hence integral_s f=0, then vector f=ae0. This avoids common-null-set/separability assumptions.
These applications and P2 Laplace identity remain UNFORMALIZED, not completed claims.
Mathlib Fourier inversion alone only at continuity points; scalar existing FourierUniquenessL1 supplies missing a.e theorem.

Then local energy uniqueness (paper mechanism, not yet formalized):
Let u be locally integrable difference with Bu+(1−B)P2u=0 a.e. Integrate twice:
B P2u+(1−B)P4u=0 everywhere.
Z=P4u is C2 (C3), Z''=P2u, Z(0)=Z'(0)=0.
E=||J.adjoint Z'||²+||Z||²−||J.adjoint Z||², J=jointEmbedding.
Original J contractive => E>=0. Differentiate using exact bounded equation => E'=0.
E0=0 => J.adjoint Z'=0 => BZ'=0 => Z'=0 (B injective) => Z=0 => P2u=0 => Bu=0 a.e => u=0 a.e.
Use causal support for negative times; do not assume physical U continuous or U itself in unbounded operator domain.
Existing formEmbeddingCovariance_injective in HTGeometry/FriedrichsFormOperator41, original jointEmbedding_injective/dense already proved.
JointDomain53 A definition. closedDenseInverse source is HTGeometry/ClosedHyperplaneInverse.lean559+, not ClosedDenseInverse.lean.
KleinGordonExactConservation141–215 read: actual method HasDerivAt.inner C, bounded CLM derivative, RCLike.reCLM, self-adjoint cancellation, is_const_of_deriv_eq_zero. Its specialized KG hypotheses are not an applicable native theorem.

Local regularity search:
Mathlib/MeasureTheory/Function/LocallyIntegrable.lean351:
  MemLp.locallyIntegrable [IsLocallyFiniteMeasure μ] hp≥1.
HTGeometry/LocallyIntegrableLinearEvolution29 intervalIntegrable_of_locallyIntegrable,36 continuous_intervalPrimitive_of_locallyIntegrable.
Those corpus statements currently have NormedRing B + NormedAlgebra R B inherited (not applicable to arbitrary SpatialSpace directly). Reuse/genericize proof for Banach/Hilbert if needed. First 22–49 read.
Continuous primitive proof uses normed absolute-continuity interval integral on compact intervals.

## Search results and external checks
Own broad Bochner, LocallyIntegrable and deep representative/Fubini, covariance-energy, L1 Laplace uniqueness.
All JSON declaration/candidate/method/proof-idea/ingredient views inspected. Partial coverage, mostly source-only; actual Lean/source determines applicability.
Useful actual Fubini proof: private l2_integral_eq in NativePhysicalIdentification526.
Deep proposed collision-energy set irrelevant; discarded.
Deep L1 query proposed fourier_one_injective and fourier_one_value_injective. Source reads show these concern AddCircle characters (WienerCharge37, PrimeEndpointRadical296), not L1 Fourier uniqueness; discarded. rg fallback found actual FourierUniquenessL1.
Broad own arXiv regularization, duality, transposition attempts did not yield a verified recent applicable result; direct search URL cache misses. No external theorem used. Previous Kinra2609.09946 weak duality remains only method context, not premise.

## Efficient isolated build setup
Scratch root was /tmp/hb-native-time.x0r14wg3 (owned; cleanup before final).
Build closure from source imports of NativeOperatorIdentification + JointSourceForcedCausal: 4235 local cached modules. Symlink cached artifacts; no local dependency sources except amended/new leaves. 11 dependency package stubs with path-only manifest and symlinked existing cache. ClassFieldTheory cache is .lake/build/default/lib/lean, most .lake/build/lib/lean.
No Git package resolution.
Main lakefile:
[[lean_lib]] name=GaloisForLFunctions roots=[] globs=[]
PLUS explicit leaf library:
[[lean_lib]] name=nativeTimeAuditLeaf
roots=[full NativeResidualAdmission module, full NativeTimeIntegralIdentification module]
globs=same explicit modules.
Without explicit leaf globs, lake build exact module returns unknown target. Fixed; both actual final builds pass.
Use fresh scratch if needed; previous roots deleted.
No need rebuild existing completed leaves next turn; consume installed cache.

## Implementation details worth retaining
- Do NOT disable RCLike.innerProductSpace in the new L2 pairing/operator module: it removes required Complex inner-product instance. Earlier native continuity-only files disable it for performance, but generic L2 pairing needs it.
- coordinates namespace is D4BMGlobalAngularResponse.
- Long direct exact ((continuous...).comp...).sub... caused 200k-heartbeat defeq timeout. Separate h1,h2 then exact h1.sub h2 works. For principal coefficient continuity, explicit function equality then rw, not expensive convert.
- ae_eq_comp yields Function.comp expressions. simp only [Function.comp_apply] at h1 h2 h3 before pointwise rw. Change h3 to cutoffCommutatorVector equality explicitly.
- Lp.coeFn_fun_finsetSum Finset.univ already matches the finite sum. There is NO Finset.sum_univ theorem here.
- intervalIntegral.integral_symm a b states integral b..a = - integral a..b. Reverse args to rewrite a..b.
- API scratch have := @polymorphicName requires explicit universe .{0,...}; use small Mathlib imports for API checks to avoid huge corpus load.
- Source copies and final artifacts are verified before deleting scratch.

## Owned process status
All owned search, Lean/Lake and lint sessions observed TERMINAL. Last axiom session64023 EXIT0. Explicit ps confirmed its predecessor PIDs gone; final cleanup checks own scratch process paths. Five current search JSON files already removed. No other agent processes touched.
