# Actual modular transport of Maass curvature

- **ID:** selberg-actual-curvature-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Active Selberg research loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 34; [actual curvature measure](selberg-actual-curvature-measure.md).
- **Statement:** For every actual principal-congruence Maass source, its constructed regular curvature measure is invariant under SL(2,Z). The original regularized compact-test pairings are already invariant before taking limits.

## Goal and scope

Transport the actual retained curvature to modular geometry while keeping all possible concentration. This closes the measure-transport part of cycle 34. It does not establish a quotient total budget or Selberg's quarter bound. All source statements quantify over the original Maass object at any real eigenvalue; no lift, replacement source equation, regularity upgrade, or spectral inequality is assumed.

## Gates

- [x] 0 → 1: original source, precise actual measure and action.
- [x] 1 → 2: complete dependency-closed paper proof below, [PROVED HERE].
- [x] 2 → 3: full scratch/source checks, both final targeted builds, and all 16 public declaration axiom checks passed. Repository lint has one unrelated wiring failure recorded below.
- [ ] 3 → 4: independent novelty and publication audit.

## Complete paper proof [PROVED HERE]

Write H for the upper half-plane, D for the literal finite congruence trace density, rho_e = sqrt(D+e²), and k_e = curvatureWeight. Previous source proofs give C² regularity of rho_e on H, invariance of D and rho_e under every A in SL(2,Z), and

k_e = Delta(rho_e) + lambda D/(y² rho_e).

The prior complex-valued positive hyperbolic Laplacian covariance is proved at real C² regularity. Real-to-complex inclusion is a continuous real linear map. Its first directional derivative commutes with that inclusion by the linear chain rule. C² regularity gives an eventual equality of those first derivatives and C¹ regularity of the derivative field; taking its derivative gives the same statement for the second derivatives. Summing the two coordinate directions proves Delta_C(ofReal rho_e) = ofReal(Delta_R rho_e).

The upper-half-plane radius pulled back through ofComplex equals the original planar radius identically, because its density is already defined through ofComplex. Thus the existing positive Laplacian covariance applies to the complexified actual radius. Radius invariance identifies the pulled-back function with itself, and injectivity of real-to-complex inclusion gives

y(Az)² Delta(rho_e)(Az) = y(z)² Delta(rho_e)(z).

Define q_e(z) = y(z)² k_e(z), the actual density relative to hyperbolic volume. The exact source decomposition yields

q_e(z) = y(z)² Delta(rho_e)(z) + lambda D(z)/rho_e(z).

All terms on the right are invariant, so q_e(Az)=q_e(z). This retains the entire regularized remainder at zeros.

The literal chart pushforward of hyperbolic volume is planar volume restricted to H, weighted by y^(-2). This follows directly on each measurable set from UpperHalfPlane.volume_eq_lintegral and image/preimage identities. The withDensity Bochner change-of-variables formula consequently gives

integral_H y² F(z) dvol_H = integral_H F(z) dxdy

for every real planar F, in the library's total integral convention. For every compact continuous half-plane test g, its checked zero extension is compact and supported in H. Its original planar curvature pairing is genuinely integrable by the previous source theorem. The chart identity and y² cancellation identify that pairing with integral_H g q_e dvol_H.

A acts by a homeomorphism, so g_A(z)=g(Az) is again a compact continuous test. Hyperbolic volume invariance and q_e invariance give J_e(g_A)=J_e(g) for every positive regulator e. The previously checked, nontrivial regulator filter has J_e(g) tending to integral g dmu, where mu is the actual regular curvature measure. Uniqueness of limits therefore gives integral g_A dmu = integral g dmu.

The pushforward A_*mu is regular because A is a homeomorphism. Its compact-test integral is integral g_A dmu. The preceding equality and the actual continuous-test representation put A_*mu under the proved regular-measure uniqueness theorem; hence A_*mu=mu. Measure.map_apply gives mu(A^(-1)s)=mu(s) for every measurable set s, including any charged seam. The homeomorphism's integral_map theorem gives change of variables for all real integrals against mu.

## Source mechanisms and failed shortcut

- SelbergMaassCuspTransport.positive_laplacian_pullback: actual real C² covariance, not an assumed smooth action on an abstract eigenspace.
- ThetaCuspHawkingBMHalfPlaneGreen.map_volume_chart_eq and integral_volume_height_sq_chart: exact density cancellation, transferred to real integrals in a lightweight module.
- Current mathlib: compact tests composed with a homeomorphism's cocompact map; invariant-volume integral_smul_eq_self; regularity of homeomorphic pushforwards; compact-test measure uniqueness.
- ModularFundamentalDomainMeasure.isFundamentalDomain_fd proves disjointness only almost everywhere for hyperbolic volume, explicitly using zero area of the two vertical edges and unit circle. This does not supply zero curvature measure on those sets. Its direct transfer to mu is not justified. No false theorem about mu's boundary charge is asserted or retired.
- Positive survivor: exact invariance of the full actual curvature measure on measurable preimages, with concentration retained. This is the completed source theorem above.

## Discovery and next conjectures

All whole-corpus alternative searches used explicit --any. Covariance/Jacobian: 1187 declarations in 299 modules. Hyperbolic-integral/complexification: 151 in 96. Quotient-measure/boundary-concentration/partition/nodal-set: 144 in 51. Partition-of-unity/fundamental-domain/proper-action/local-finiteness/stabilizer: 4445 in 410. Atomlessness/potential/capacity/boundary-flux/growth: 406 in 120. These count indexed coverage, not inspection of every result.

Inspected mechanisms suggest testing continuous weighted partitions for a quotient budget rather than applying a boundary indicator to vague convergence. DeningerTransversePartition shows how exact partition sums preserve overlapping assembly, but its clopen product assumptions do not yet construct an actual modular partition. Bottcher.Brolin.RieszFlux.integral_ball_laplacian_eq_boundary_flux supplies a C² planar ball/flux identity. Together with the actual trace's radial-energy square completion, it suggests proving a uniform small-ball curvature bound and then excluding point atoms at elliptic stabilizers. Neither local mass growth, atomlessness, nor seam weighting is proved here. Atomlessness alone would not make seam curves null.

## Lean sources and verification

- formal/GaloisForLFunctions/RHTower/SelbergMaassCurvatureCovariance.lean: 5 public declarations.
- formal/GaloisForLFunctions/RHTower/SelbergMaassCurvatureTransport.lean: 11 public declarations.
- Both complete /tmp scratch files and needed source olean checks passed without warnings. Both modules are wired into RHTower.lean; no umbrella build is run.
- Serialized final builds passed, rebuilding only their named target: covariance (10s), transport (5.7s). Logs: /tmp/selberg_curvature_covariance34_build.log and /tmp/selberg_curvature_transport34_build.log. Both replayed an existing informational tactic suggestion from EvenL2LogUnitary; neither new module emitted a warning.
- /tmp/selberg_curvature_transport34_axioms.lean audits every public declaration. All 16 report only propext, Classical.choice, and Quot.sound; no added axioms or admitted proofs. Full log: /tmp/selberg_curvature_transport34_axioms.log.
- Generated indexes refreshed; all 16 declarations are present in /tmp/selberg_curvature_transport34_corpus_audit.json. Task-source/card/umbrella whitespace checks passed.
- **Repository lint failed only on unrelated, unwired HTGeometry.DilatonSchwartzTransform.** No Selberg error. Full stdout/stderr log: /tmp/selberg_curvature_transport34_lint.log. That concurrent module was not modified or wired speculatively.
- Every task-owned Lean/build handle is terminal. Final process inspection found another agent's lean /tmp/hgt-arxiv-applications/DilatonOperator.lean, which was left untouched; no task-owned process remains. No full/umbrella build, numerical experiment, task commit, or push.
