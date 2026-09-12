# HB original physical quadratic source conservation — 2026-09-12, 0912w

RH remains UNPROVED. Goal remains active, unbounded. Never mark complete from this producer. Read frontier map only; latest user instruction overrides goal's original update request. STATUS unchanged: discoveries are route-specific.

Full chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## New completed mathematical producer
Original physical quadratic Einstein source now has zero actual background covariant divergence. This is derived from the actual nonlinear Bianchi identity, actual mixed spatial/amplitude derivative interchange, and the original background and linear equations on a genuine exterior neighborhood. All physical regularity, symmetry and nondegeneracy are discharged. Output is the original full Taylor source, including factor 1/2, not a prescribed conserved source.

Main leaf: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuadraticConservation.lean
Namespace RHTower.D4BMQuadraticConservation:
- backgroundField is actual metric (x1,x3).
- physical_hessian_conservation, line43: for every ExteriorPoint p, XiZeroCopy q, branch b, scalar/vector amplitudes aS/aV and j, actual tensorDivergence of full Einstein Hessian is zero.
- physicalQuadraticSource = (1/2) smul actual hessianTensor.
- physicalQuadraticSource_eq, line73: exactly iteratedDeriv 2 (original D4BMActualMetricSource.source p physicalPerturbation i j) 0 / 2.
- physical_quadratic_source_conservation, line84: original physical quadratic source has zero background tensorDivergence, no supplied conservation or reconstruction hypotheses.

This closes the LOCAL quadratic-conservation conjecture. DOES NOT produce global causal inverse, common retarded/advanced domain, physical left-QNM incidence/nonzero coupling, or fixed-clock extinction. Original cyclic boundary/contact defect from 0912t–v remains attached throughout.

## Seven new leaves, all scratch checked, exact leaf audited, installed, umbrellas wired
1. HTGeometry/CoordinateEinsteinAffineSpatialVariation.lean (4.9s audit): amplitudeJet; affineSpatialEinstein = F'(q+e*p)[qx+e*px]; affineSpatialSlope; actual first and second amplitude derivatives. affineSpatialEinstein_second = F'''(q)[p,p,qx]+2F''(q)[p,px]. Genuine nondegenerate amplitude neighborhood, both varying factors retained.
2. HTGeometry/ComplexMetricJetDerivative.lean (15s): actual coordinateLine, jetSpace = complete actual twoJet, jetSpacePartial = actual spatial derivatives of all ordered jet slots. jetSpace_coordinateLine_hasDerivAt; jetSpace_differentiableAt; einsteinField_differentiableAt; einsteinField_coordDeriv. jetSpace_add_smul (C2), jetSpacePartial_add_smul (C3) from actual neighborhood equality and derivative uniqueness. hessian_coordinateLine_hasDerivAt specializes prior real-Hessian theorem to actual fields.
3. HTGeometry/ComplexMetricMixedEinsteinDerivative.lean (12s): affineField g h e; hessianField g h x i j = original Einstein secondVariation on actual jets. hessianField_differentiableAt, hessianField_coordDeriv, affineEinstein_coordDeriv, einstein_mixed_derivatives. Last theorem compares two amplitude derivatives of original actual spatial Einstein derivative with spatial derivative of actual Hessian.
4. HTGeometry/ComplexMetricEinsteinSourceVariation.lean (29s): linearField = F'(actual g jet)[actual h jet]; actual spatial differentiability and derivative. affineSource = literalEinstein(affineField g h e) Lambda, including actual cosmological term. affineSource_eq, affineSource_contDiffAt (any order), affineSource_hasDerivAt, affineSource_first, affineSource_second. Actual original source coefficients and spatial first variation, not formal derivative arrays.
5. HTGeometry/ComplexMetricEinsteinSpatialSource.lean (9.1s): spatialSource actual coordDeriv of affineSource, spatialSourceModel original full jet variation plus affine cosmological contribution. spatialSource_eq, spatialSource_eventuallyEq, C2 amplitude regularity, spatialSource_first and spatialSource_second. First derivative = spatial derivative of original linear cosmological source; second derivative = spatial derivative of original Hessian. Exact leaf audit listed 2001 jobs from cached Mathlib dependency traversal, but log built ONLY this new leaf.
6. HTGeometry/ComplexMetricQuadraticConservation.lean (11s): actual complex amplitude inverse and connection C2 regularity via original affine jet/Cramer formula; weighted_second via finite Leibniz. amplitudeDivergence expands actual inverse contraction and BOTH tensor-index connection actions, amplitudeDivergence_eq identifies original divergence. hessianTensor is the named actual matrix field. hessian_conservation line183 derives conservation assuming original E0/E1 equations on a spatial neighborhood plus actual C3/symmetry/nondegeneracy. tensorDivergence_const_smul on actual differentiable tensor fields retains quadratic normalization.
7. RHTower/ThetaCuspHawkingBMQuadraticConservation.lean (56s): physical closure described above, cached project closure3961 leaves, audit built ONLY new leaf (2 jobs).

All sources and matching five artifact types were installed from isolated successful audits. All seven umbrella imports added; no umbrella was built. scripts/formal_tools.py lint passed with existing large-file warnings. No #print axioms, computations, Git, launch.sh, heartbeat increases or subagents.

## Analytical proof and whole-chain consequences
Let E(e) be literal cosmological Einstein tensor, D(e) its original covariant divergence. Nonlinear Bianchi gives D(e)E(e)=0 near e0. Original E(0) and E'(0) vanish on genuine spatial neighborhood. Mixed derivative results ensure their spatial derivatives vanish too. Two amplitude derivatives of expanded D(e)E(e) leave only D(0)E''(0). E''(0)/2 is original Q. Both inverse metric and covariant index actions included. So D(0)Q=0.

Next hard producer: actual full causal metric solving original linearized tensor equation with this source, then its original physical boundary/left-mode pairing. Compare two construction mechanisms instead of assuming one uniquely possible:
A. Actual harmonic source projection → source Bianchi relations → realize complete radial reconstruction jets → common physical retarded/advanced boundary problem. Previous scalar-stream pointwise identities alone do not supply actual radial derivatives or full field. Original Q conservation is now available for projection, not assumed.
B. Derive gauge-fixed tensor wave operator from original linearized Einstein operator, construct its actual causal solution, then prove gauge constraint propagation from admissible data using source conservation. No producer or operator/domain identification yet established. Same original boundary/contact functional must survive either route.

Diagonal theorem covers each physical perturbation with both parity amplitudes. Mixed sources across different q/branches or finite mode sums need polarization/superposition extension if required; do not silently claim those from diagonal output. Existing D4BMFullLinearEquation.fieldSpace_add and source_first_add provide actual additivity. They were read this turn, no re-audit needed. Physical actual first-source zero theorem is D4BMLiteralCusp.physicalPerturbation_first_source_zero.

## Corpus/external research this turn
Direct search tool, broad/deep/method queries: spatial jet; differentiate affine response twice preserving source derivative; second derivative product vanishing; matrix inverse smooth; Peano; Taylor remainder; Lichnerowicz; gauge propagation. Inspected candidate_lemmas, source_arguments and ingredient_sets as well as declarations/coverage. Snapshot roughly57293 files/740691 declarations; compiler metadata largely source-only or pending, semantic coverage unavailable; several searches partial. No assertion of exhaustive absence.
- Spatial3 in ScalarJetSpatial3ConnectionTable means coordinate INDEX3, not third regularity. EisensteinActualThirdJet is a different actual Poincare field/convergence chamber. Actual literal C3 regularity was correct input.
- RHTower.complex_iteratedDeriv_mul_of_left_vanishing_below, ReflectedBiHeatMultiplicityTomography line87: finite Leibniz collapse for m. Method used with Mathlib iteratedDeriv_fun_mul in low-level geometry, avoiding upward RHTower dependency.
- Public SmoothMatrixDeterminantCalculus.contDiff_matrix_inv_apply is REAL/global; complex/local inverse lemmas elsewhere are private. Produced actual needed complex amplitude regularity directly.
- Peano search unhelpful; Taylor remainder deep search found HTGeometry.AnalyticSlopeFactor.eq_taylor_two_add_sq_mul and analyticAt_analyticSlope_two. Exact source double-zero factorization exposes stronger alternative: divide amplitude squared, extract conservation using only continuity of metric weights. This alternative is not an HB formal result yet; current finite Leibniz proof already has C2 weights.
- Lichnerowicz search no applicable hit; gauge propagation found Fokas–Lenells Hardy propagation of its own analytic slices/boundary corrections and unrelated gauge statements. Both partial filter/judge/decomposition. These do not identify the original metric tensor operator/domain; no absence claim.
- Broad arXiv transgression/observability searches. Read official abs/html https://arxiv.org/abs/2608.02928 and https://arxiv.org/html/2608.02928v1, Cristian Anghel, AKSZ Descent on Manifolds with Ordinary Corners (August2026). Method-only proposal: retain signed incidences of actual radial/temporal/cusp boundary faces and shared corner terms before limits. Paper has explicit mapping-space hypotheses; no AKSZ/gravity specialization supplied. No HB cancellation/extinction imported.

## Efficient Lean lessons
- hasDerivAt_pi.mpr exists; HasDerivAt.pi does not.
- For real derivatives of complex CLM-valued paths, use the small generic clm_apply_real helper/local IsScalarTower.continuousSMul instance, explicit HasFDerivAt E/F/scalar types, and infer intermediates. Direct huge finite-jet bilinear application caused whnf heartbeats; generic helper solved without increases.
- Final convert! handles inherited/direct scalar/norm/group structures. Plain simpa often fails despite printed identical types.
- When rewriting coordDeriv_add/mul, specify f/g explicitly rather than relying on inferred pointwise Pi operations.
- For iteratedDeriv2 use simp only [iteratedDeriv_succ,iteratedDeriv_zero]; rewriting succ expands one as well, leaving iteratedDeriv0 unless removed.
- Filter.EventuallyEq.deriv and .deriv.deriv_eq are real current names.
- Use named hessianTensor Field for matrix-valued target; raw curried lambda can trigger tactic instances-transparency type mismatches. Explicit S in tensorDivergence_const_smul avoids inferring raw scalar hessianField.
- For exterior neighborhood, IsOpen.mem_nhds returns filter-set membership; annotate as ∀ᶠ before .and. ContinuousAt.eventually_gt was unavailable in this import context.
- Identify actual source through D4BMLiteralConservation.sourceField_eq_literalEinstein. Avoid ring expanding original metric Einstein expression; use neg_mul/sub_eq_add_neg for cosmological sign.
- Exact final leaf stage copies only new source and hardlinks known cached dependency artifacts; no dependency source or umbrella builds. Direct Mathlib import may cause cached job traversal but verify build log actual built lines.

Card: docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md documents completed local conservation, proofs, alternative candidates and current global gap. Frontier/STATUS untouched. This turn's temporary paths use /tmp/hb-*0912w*; cleanup follows immediately after this memory. All owned Lean/Lake/search/lint processes have completed. Prior0912v files already cleaned; leave unrelated /tmp/selberg_* and other agents' processes untouched.

Predecessor: mem:hb_original_source_conservation_and_real_hessian_derivative_2026_09_12_0912v; earlier reconstruction mem:hb_sourced_reconstruction_and_modular_inverse_2026_09_12_0912u.
