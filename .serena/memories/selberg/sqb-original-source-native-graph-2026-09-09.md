# SQB: original native graph and exact entire forcing transport

## Goal and constraints
Active unbudgeted goal: unconditional closed Lean proof/falsification of RH via SQB. RH UNPROVED; goal not complete or blocked. Frontier map is READ ONLY, never edit it despite older goal objective. User insists broad OR corpus research, not only narrowly conjunctive searches. No numeric experiments or numeric proof inputs were used. One foreground Lean/Lake compiler per agent, source/scratch `lake env lean FILE`, final `lake build MODULE` only; no full or umbrella builds. Every spawned command handle this increment was collected. No subagents. Preserve other tasks' changes; no commits/push.

Current card: docs/drafts/pipeline/1-in-progress/sqb-native-source-resolvent-transport.md. Dependency-closed proof/audit: docs/drafts/pipeline/3-formalized/sqb-original-source-native-graph.md. Universal ledger has compact new route-independent requirement to justify actual operator domain and both graph limits with retained forcing. Frontier map unchanged.

## New exact result: 58 public declarations, five audited modules
All under formal/GaloisForLFunctions/RHTower, matching namespaces under RHTower.
1. SelbergScatteringSourceApproximation: 20 public, 223 lines, final sole-target build 4.8s.
2. SelbergScatteringSourceBounds: 10 public, 194 lines, final sole-target build 4.8s.
3. SelbergScatteringCutoffDerivatives: 7 public, 118 lines, final sole-target build 3.7s.
4. SelbergScatteringSourceGraph: 10 public, 217 lines, final sole-target build 8.4s.
5. SelbergScatteringForcingTransport: 11 public, final sole-target build 6.4s.
Each wired once into RHTower umbrella; do not rebuild umbrella. All complete scratch checks passed without diagnostics. Final preflight was `lake --no-build build MODULE`, then all Building/Built lines parsed to prove only named module compiled. All 58 public axiom reports standard-only propext/Classical.choice/Quot.sound; no added axioms or placeholders, unsafe/native_decide or numerical results. All public entries in refreshed corpus index. Full audit /tmp/sqb10_index_audit.json; logs /tmp/sqb10_{approx,bounds,cutoff_deriv,graph,transport}_build.log and /tmp/sqb10_{approx,aux,graph,transport}_axioms.log. Public full names in /tmp/sqb10_{approx,bounds,cutoff_deriv,graph,transport}_exports.json. Complete source scratch /tmp/sqb10_{approx,bounds,cutoff_deriv,graph,transport}.lean.
Final full lint `/tmp/sqb10_final_lint.log` FAILED ONLY for five unrelated untracked HTGeometry modules missing umbrella imports: FokasLenellsRawContourFifthTrace, FokasLenellsRawTwistEndpoints, FokasLenellsRawTwistKernels, FokasLenellsRawTwistPrimitives, FokasLenellsRawTwistScattering. Other-task modules left untouched. This is a recorded invocation, not assumed current forever.

## Source approximation and scaled multipliers
Let a_n=n+3 and beta_n(y)=smoothWeight(a_n,a_n,y). Existing SmoothWeight bounds all order-j derivatives by C_j/a_n^j, beta in [0,1], beta=1 below a, zero above 2a.
SourceApproximation uses CellGermExtension to glue actual globally modular cutoff. Parabolics preserve height; nonparabolic closed-cell overlaps have both heights<2, so cutoff germs both1 (a>=3). All seams and elliptic points retained. Modular cutoff has native CellCompact support via truncated_cell_compact(2a), globally bounded1, eventually1 every fixed point. sourceCore q n = cutoff * complete globalResidual q, genuine CoreField. sourceApproxDomain is actual native A-domain vector V_n with literal operator representative f_n-chartLaplacian f_n. `sourceApproxDomain_tendsto` proves V_n -> sourceVector V in native L2 norm via MeasureTheory.tendsto_lpBoundedMulCLM_apply. Eventually exact entire germs and operator values at each fixed cellpoint also proved, but not used as norm convergence without bounds.
SourceBounds derives weighted_value_vertical_bounded from actual value_hasFDerivAt: vertical derivative is a*value(u,nu,a-1,d) minus pi*(value(u,nu+1,a,d+1)+value(u,nu-1,a,d+1)). Full shifted family bound weighted_value_bounded covers all three. Complete scalar tail is 2*(both signed families), no truncation. Compact lower closed-cell smoothness + full upper-cell tail bound yield globalResidual_vertical_bounded and globalResidual_vertical_memLp. `sourceVerticalVector q` is actual D=y*d_y R in native L2; coe and closed-cell coordinate identity proved. `globalResidual_operator_on_fd` is exact R-chartLaplacian R=eR+original cutoffForcing on entire closed cell. `sourceOperatorTarget q = e • V + H`, with actual L2 representative R-chartLaplacian R; no domain assumption.
CutoffDerivatives defines delta_j,n(z)=(y^j * iteratedDeriv j beta_n y : complex). Uniform global bound 2^j C_j follows for y<=2a by scaling, above2a actual derivative zero. Every positive-order delta eventually zero fixedpoint. Actual `cutoffDerivativeOperator j n` = bounded L2 multiplier. `cutoffDerivativeOperator_tendsto_zero j hj f` proves strong convergence for every native f.

## Exact original native closed graph
SourceGraph retains full two-coordinate product using SelbergScatteringHeightConjugation.hyperbolicLaplacian_mul and D4BMCuspProjection.height_laplacian. Original/cutoff whole germs transfer through closed seams. `sourceCore_laplacian_on_fd`:
Delta f_n = beta_n Delta R + delta_2,n R + 2 delta_1,n D.
Original forcing H is zero above3, beta_n=1 below3, so beta_n H=H exactly for every n. `sourceApproxDomain_operator_eq` in actual native Space:
A V_n = e V_n + H - delta_2,n V - 2 delta_1,n D.
Both errors strongly ->0. `sourceApproxDomain_operator_tendsto`: actual A V_n -> Q=eV+H in native norm.
`nativeCovariance_sourceOperatorTarget`: BQ=V from continuity of bounded B=A^-1, B A V_n=V_n, uniqueness of independently proved two norm limits.
`sourceVector_mem_energyOperator_domain`: original V in actual A.domain (=range B), NO DOMAIN PREMISE.
`sourceNativeDomain q`: subtype carrying original V.
`sourceNativeDomain_operator`: A(original V)=Q.
`sourceNativeDomain_equation`: A V - e V = H.
`sourceVector_native_resolvent_equation`: V - e B V = B H.
This closes the formerly open native graph bridge; do NOT keep proposing it as missing.

## Exact full-Xi forcing transport
ForcingTransport proves `scatteringEnergy_nonreal q` from existing xi_scatteringEnergy_abs_im and xiResidualFloor_pos. Every actual Xi energy e=1+(rho/2)(1-rho/2) nonreal, including critical copies.
`sourceResolvent q : Space ->L[C] Space` = existing resolventCLM energyOperator_selfAdjoint nonreal, actual (A-e)^-1. Native-domain membership, exact inverse equation for any actual f, and norm bound ||R_e f||<=xiResidualFloor^-1 ||f|| all proved.
`sourceResolvent_original_forcing`: R_e H=V by injectivity of actual shifted operator, comparing original native-domain source and actual resolvent response. This closes ORIGINAL SOURCE IDENTIFICATION, not replacement by chosen response.
`entireForcingTransport q = (I-(2+xiEntireTarget q) • entireCovariance).comp (sourceResolvent q)` is actual bounded K_q.
`sourceResidual_eq_transported_forcing`: original G=K_q H.
`sourceDomainVector_transported_equation`: (T-mu)CV=K_q H.
`sourceUnitVector_transported_residual_norm`: ||(T-mu)U|| = ||C R_e H||^-1 ||K_q H||, U original unit domain source. Denominator positive from original V nonzero + C injective (`sourceCovariance_norm_pos`), with original source/forcing fully identified. No new vanishing or smallness theorem.
This uses composition of actual bounded resolvent and existing CFC C. A single scalar rational CFC representation h_e,mu(x)=x*(1-(2+mu)g(x))/(1-e*x) is NOT yet formalized; optional further tool, not a premise of current transport.

## Remaining RH task
Full chain remains original modular source -> actual entire operator -> independently proved occurrence at every FULL Xi parameter -> critical-line classifier -> RH.
Native graph and exact bounded forcing transport are now CLOSED. Missing: zero-specific occurrence/control of ||K_q H|| relative to ||C R_e H|| for suitable full-source construction, without adding RH-equivalent assumptions. H is proved nonzero, but this alone does not establish K_q H nonzero or zero. Original bilinear source pairing zero also cannot replace norm/forcing control. Current fixed corrected source unit vector is not asserted eigen or approximate eigen.
Possible next mathematical work must be corpus-grounded: analyze exact kernel/spectral fibers and original source tail or derive genuinely arithmetic comparison. Never declare whole SQB retired from a failure of one corrected source; no-go needs strongest positive survivor. Existing entire cusp packets have limiting residual equal zero iff critical, and supply no independent all-Xi occurrence.

## Broad searches and inspected infrastructure
OR approximation/dominated/exhaustion/convergence/gradient-tail: 4,905 declarations,2,252 modules (/tmp/sqb10_approx_broad.json).
OR jet/cusp-decay/tail-bound/derivative-bound: 21,318 declarations,3,663 modules (/tmp/sqb10_jet_broad.json).
OR resolvent/functional-calculus/spectral-multiplier/forcing-transport: 3,478 declarations,647 modules (/tmp/sqb10_transport_broad.json); 130 metadata matches filtered for CFC/nonreal/self-adjoint/inverse structure. Counts are metadata coverage, NOT claims to read every proof.
Actually inspected CellGermExtension, HTGeometry.SmoothWeight and L2MultiplierContinuity (MeasureTheory namespace), complete angular value derivatives/bounds, scalar coordinate derivative rules, full Laplacian product, height Laplacian, weightedDeriv and continuity, actual B/A inverse APIs, entire operator, CfcResidualTransport (real dslope factorization), SelfAdjointResolvent (all relevant full proof), ResolventCompactness first150 lines, original WeakResponse native operator.
Use rg across directories or rg --files; no huge shell globs. Lean symbol indexing unsupported by Serena here, so rg and reads used. New theorem mathlib names verified by scratch. Compiler caveats: complex ofReal casts of actual derivatives need explicit inner real annotation; sourceCore toLp coercion needs explicit change before rewriting; ContDiff apply projection takes actual continuous linear map.

Prior context: `mem:selberg/sqb-native-forcing-full-core-2026-09-09` (19 declarations, core and original H); `mem:selberg/sqb-original-modular-cusp-subtraction-2026-09-09` (original V,CV,G); `mem:selberg/sqb-full-source-cusp-norm-2026-09-09` (sharp complete cusp threshold).
