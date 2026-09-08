# Actual regularized cusp decay and full modular curvature budget

- **ID:** selberg-full-curvature-budget-30
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 30](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** The actual regularized top current vanishes at the cusp; the full standard-area retained curvature is integrable and equals the positive weighted spectral mass.

## Scope

Every analytic condition is proved from the original Maass source. The full budget concerns every hypothetical exceptional eigenform and every fixed positive regulator. It does not assert existence of an exceptional eigenform, an exchange of the regulator limit with the remainder integral, or the quarter lower bound. Selberg remains unproved.

## Corpus discovery and conjecturing loop

Discovery used explicit OR searches with --any; unflagged multiple terms mean AND.

- Derivative limit, secant, convexity, integrable forcing, finite limit: 1637 declarations in 445 modules.
- Dominated integral, uniform cusp, inverse square, asymptotic slope, monotone derivative: 493 declarations in 217 modules.
- Uniform limit, integral decay, integrable tail, bounded average, inverse square: 596 declarations in 277 modules.
- Positive exhaustion, integral exhaustion, bounded integral, monotone domain, integrable majorant: 34 declarations in 32 modules.
- Broader exhaustion, monotoneConvergence, iUnion, integrableOn_union: 2856 declarations in 1381 modules.
- Geometric/arithmetic discovery for the next loop, using Cheeger, coarea, perimeter, isoperimetric, expander, quasirandom, holonomy, congruence: 3061 declarations in 541 modules.

These are index-coverage counts, not claims to have read every hit. Narrow phrase searches were broadened when they returned too little. Search logs are /tmp/selberg_regularized_cusp_discovery.json, /tmp/selberg_regularized_cusp_forcing_search.json, /tmp/selberg_cusp_uniform_tail_discovery.json, /tmp/selberg_full_curvature_exhaustion_discovery.json, /tmp/selberg_exhaustion_wide.json, and /tmp/selberg_curvature_budget_geometric_arithmetic_wide.json.

Read mechanisms included HTGeometry.LogDerivativeFromEnvelope's monotone-derivative secants, the actual SelbergMaassCuspDecay convex-secant proof, SelbergMaassTailEnergy's extension from a proved tail to all positive heights, UpperHalfPlaneExhaustion's actual compact source coverage, and mathlib's AECover integrability-from-bounded-integrals mechanism. The later FormationStokesFolnerSelection finite-packet Cheeger inequality retains a constant-divergence assumption and an edge-current bound; no Maass instance is asserted.

1. Conjecture: finite value limit plus actual lower curvature -C/y² forces actual derivative decay. Proved by corrected-derivative monotonicity and two unit secants.
2. Conjecture: the actual regularized horizontal mean satisfies that forcing bound. Proved, more strongly with absolute eigenvalue and no eigenvalue-sign restriction.
3. Conjecture: the literal centered Stokes top current tends to zero. Proved through actual averaging derivatives and source period one.
4. Conjecture: truncated standard-area balance extends to a genuinely integrable full-domain budget. Proved using original mass control, nonnegative remainder, and actual domain exhaustion.
5. Positive strengthening: original nonvanishing makes both weighted mass and retained curvature strictly positive for every hypothetical exceptional source. Proved.

## Dependency-closed paper proof

Let D be the squared norm of the actual finite congruence family and rho_e=sqrt(D+e²), e>0. Original source regularity makes rho_e C² in the upper half-plane, with unit horizontal period. Actual density decay at the cusp gives rho_e -> e uniformly in the real coordinate.

Define M_e(y)=integral_0^1 rho_e(x+iy) dx and V_e(y)=integral_0^1 partial_y rho_e(x+iy) dx. Differentiation of the compact integral uses the already-proved complex averaging theorem through the literal real-to-complex inclusion. It gives M_e'=V_e. C² regularity similarly differentiates V_e. The horizontal second derivative integrates to zero by source periodicity and FTC, so

V_e'(y)=integral_0^1 Delta rho_e(x+iy) dx.

The retained source equation is rho_e Delta rho_e=R_e-lambda D/y², with R_e>=0. Since D<=rho_e² and lambda D<=abs(lambda)D,

Delta rho_e >= -abs(lambda)rho_e/y².

Averaging gives V_e'>=-abs(lambda)M_e/y². Uniform cusp convergence gives M_e->e, hence eventually M_e<=e+1. Therefore V_e'>=-C/y² for C=abs(lambda)(e+1)>=0.

For the general real lemma, suppose u'=v, v'=a, a>=-C/y² on a positive ray, C>=0, and u->L. Then w(y)=v(y)-C/y is increasing. Forward and backward unit secants give, eventually,

u(y)-u(y-1)-C/(y-1) <= v(y) <= u(y+1)-u(y)+C/y.

Both sides tend to zero. Thus v->0. This uses actual curvature; a value limit alone is not treated as a derivative estimate. Applied to M_e, it proves V_e->0. Period-one symmetry of the actual current identifies V_e with the centered top boundary integral used in Stokes.

The literal full planar domain is

Omega={(x,y): -1/2<=x<=1/2 and sqrt(1-x²)<=y}.

The already-defined compact Omega_Y exhaust it. Each point has positive height, every truncation is measurable, and restricting full-domain area again to Omega_Y gives ordinary area on Omega_Y. These facts construct an actual AECover, rather than postulating an exhaustion.

Original core-plus-tail mass is finite and independent of the cutoff. Positivity of its tail bounds every core mass by the total mass at height one. Positivity and bounded truncated integrals prove integrability of D/y² over Omega. Since rho_e>=e,

0 <= D/(y² rho_e) <= D/(e y²).

This proves full-domain weighted-mass integrability at fixed e. The finite-height source identity is

integral_{Omega_Y} R_e/rho_e = top_e(Y)+lambda integral_{Omega_Y} D/(y² rho_e).

The right side tends to lambda integral_Omega D/(y² rho_e). The nonnegative left integrand is locally integrable. The exhaustion theorem therefore proves its full integrability and identifies its integral:

integral_Omega R_e/rho_e = lambda integral_Omega D/(y² rho_e).

The source equation then also proves full integrability of Delta rho_e, and its integral is zero.

Original source nonvanishing supplies a compact core with strictly positive trace mass. Division by the positive rho_e preserves the mass support. Inclusion of that core in Omega preserves positive support measure, so the full weighted mass is strictly positive. For an exceptional eigenvalue lambda>0, the exact budget makes the full retained curvature strictly positive as well.

No pointwise regulator limit is used. Cycle 28's exact nodal model remains a reason to retain concentration. The bound involving 1/e is a fixed-regulator integrability proof, not a uniform regulator bound.

## Lean modules and audit

- SelbergOneSidedCurvatureDecay: actual inverse-square correction and secant derivative decay.
- SelbergScalarHorizontalAverage: literal real averages, their first and second derivatives, and horizontal-periodic cancellation.
- SelbergMaassRegularizedCusp: all forcing, limits, periodicity, and the actual centered cusp current.
- SelbergMaassFullCurvatureBudget: actual full domain and exhaustion, genuine full integrability, exact budget, vanishing Laplacian integral, and strict positivity.

All complete scratch proofs and direct source checks passed. Four serialized final LEAN_NUM_THREADS=1 lake build <single-module> audits passed. The one-sided derivative module (1.9s), scalar horizontal average (4.7s), and actual cusp module (3.6s) rebuilt only their named target. The full-budget build rebuilt the needed SelbergMaassTraceMass dependency (4.4s) and its target (3.7s). Cached informational output from EvenL2LogUnitary was replayed; no new task-module warning occurred. No full or umbrella build ran.

Build logs: /tmp/selberg_one_sided_curvature_build.log, /tmp/selberg_scalar_horizontal_average_build.log, /tmp/selberg_regularized_cusp_build.log, /tmp/selberg_full_curvature_budget_build.log.

All 42 public definitions/theorems passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. No added axioms or admissions. The declaration list and parsed audit cover all four new modules: /tmp/selberg_full_curvature_declarations.txt, /tmp/selberg_full_curvature_axioms.lean, /tmp/selberg_full_curvature_axioms.log.

All four modules are wired into RHTower.lean and present in the refreshed index. The exact full_curvature_budget capstone is returned by the corpus audit (/tmp/selberg_full_curvature_capstone_index.json). Task source and research-card whitespace checks passed.

Repository-wide lint failed only on two unrelated untracked, unwired modules: RHTower.MobiusDivisorFibreCoareaVariance and HTGeometry.FokasLenellsContourSymmetry. Existing large-file warnings remain. Neither unrelated source was modified. Log: /tmp/selberg_full_curvature_lint.log. The prior cycle's FokasLenellsUniformizedFrame error is historical and did not occur in this audit.

Every task-owned Lean/build handle is terminal. Final process inspection found no Lean or Lake process. No commit or push was made by this task.

## Next source problem

Prove regulator-uniform integrability of sqrt(D)/y² using actual hyperbolic area and original source mass. Then identify the limit of total retained curvature without replacing it by the integral of its pointwise limit. A candidate compact-test identity retains the distributional Laplacian of sqrt(D) together with lambda sqrt(D)/y², including possible nodal charge. Every test-function boundary cancellation and limit passage needs proof.

The essential unsolved step remains a source-derived global quarter comparison. Neither this exact budget nor fixed-path variation supplies that lower bound by itself. Arithmetic transport or a weighted geometric inequality must be constructed for the actual congruence source, with all defects retained.
