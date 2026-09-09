# SQB native forcing and full compact operator core

Active unbudgeted goal: unconditional closed Lean RH proof/falsification via SQB. RH UNPROVED; goal stays ACTIVE. This turn made verified progress, no blocker streak. Frontier map READ ONLY. No numerical experiments or numerical proof inputs. No agents spawned. No commits/push. All owned exec handles collected; no owned Lean/Lake process left.

Full chain: original modular source -> entire-transform operator -> independent occurrence for every full Xi parameter -> critical-line classifier -> RH. Prior state in `mem:selberg/sqb-original-modular-cusp-subtraction-2026-09-09` and `mem:selberg/sqb-full-source-cusp-norm-2026-09-09`.

## Completed this turn: 19 public declarations, two modules

1. `formal/GaloisForLFunctions/RHTower/SelbergScatteringCutoffForcing.lean`, namespace `RHTower.SelbergScatteringCutoffForcing`, 8 public + 2 private declarations. Imports SourceVector and CutoffPowerFlux.
- `cutoffForcing_eq_commutator q z hz`: literal original cutoffForcing = Lambda(rho-1) * cutoffCommutator (1-rho/2), at positive height. Derived from full source PDE, physicalScalar_principal and actual C2 const-mul Laplacian, not Fourier truncation.
- `cutoffForcing_memLp`: full original forcing in native L2(volume.restrict fd).
- `forcingVector`, `forcingVector_coe`: actual toLp class H and AE representative.
- `cutoffCommutator_complement_moment k`: cutoffPowerMoment (1-k) k = 2*k-1. Existing full boundary formula cancels bulk coefficient exactly.
- `forcingVector_ne_zero q`: H != 0 for EVERY actual Xi. H0 -> AE0 -> continuous pointwise0 on fd=closure(interior fd). Points iy for y in [1,4] lie in fd. Lambda(rho-1) nonzero -> full commutator0 -> complementary moment 2k-1=1-rho0, contradict Re rho<1.
- `scalar_forcing_integrable` and `scalar_forcing_pairing_zero`: full absolutely integrable BILINEAR (no conjugation) integral E_u H=0, despite H nonzero. Uses actual scalarCutoffPeriod calibration. Does NOT set H or transformed residual G to zero.
- Private coefficient_ne and forcing_continuous.

2. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullCoreOperator.lean`, 326 lines, namespace `RHTower.D4BMModularCore`, 11 public + 12 private declarations. Imports OperatorCore, ModularLaplacian, HTGeometry.CompactSmoothCutoff, Mathlib SmoothTransition.
- `CompactChartTest.orbit_summable`: full PSL2Z orbit of compact test summable by proper discontinuity (finite support).
- `CoreField.exists_planar_periodization`: EVERY original smooth modular quotient-compact core field f equals full periodize of some compact positive-height PlanarChartTest. No seam/elliptic exclusion.
  Construction: compact cell support K -> smooth planar chi=1 near coe''K, supported compactly inside UH (root namespace HTGeometry.exists_smooth_cutoff). b=(chi:complex)^2, p=full PSL2Z periodize b. Re p>=0. Re p>=1 wherever f!=0, after moving point to fd and invariance. d=p+(1-smoothTransition(2 Re p-1):real). Re d>0: for Re p<=1/2 eta=0, otherwise eta<=1. For Re p>=1, d=p. g=b*(f/d) on the plane using ofComplex, compact smooth: at positive height quotient smooth; outside support locally0. Full orbit sum g=p*f/d=f. All stabilizer multiplicities retained.
- `CoreField.planarTest`, `CoreField.planarTest_periodize`: choose constructed representative and exact function equality.
- `CoreField.mem_energyOperator_domain`: fieldVector f belongs original native Friedrichs A domain, via PlanarChartTest.operator theorem and exact coreField equality.
- `CompactChartTest.chartLaplacian_periodize`: literal Delta_H(full periodize g)=full periodize(Delta_H g). Proper discontinuity supplies one finite set containing all nonzero translates on a neighborhood; omitted terms locallyzero -> derivativeszero. Differentiate actual finite sum twice and use existing chartLaplacian_modular_pullback/germ locality. No interchanging uncontrolled infinite derivative sums.
- `PlanarChartTest.laplaceVector_coe`: original admitted laplaceVector represents literal chartLaplacian of full periodization AE.
- `CoreField.energyOperator_coe`: native A f represented by literal f-Delta_H f AE.
- `CoreField.laplacian`, `CoreField.laplacian_field`: literal Delta_H f itself belongs original CoreField (smooth, invariant, CellCompact), via periodization of compact planar Laplace test.
- `CoreField.energyOperator_apply`: A(fieldVector f)=fieldVector f-fieldVector f.laplacian.

These generic core results are fully proved on intrinsic CoreField inputs. They do NOT admit the noncompact original source V to A domain yet.

## Audits

Both complete scratches passed `lake env lean /tmp/sqb9_forcing.lean` and `/tmp/sqb9_core.lean`. Each final preflight `lake --no-build build MODULE` identified ONLY that new module stale; all Building lines parsed. Final `lake build MODULE` compiled only that module: forcing 4.2s, full core 6.5s. Both emitted no own warnings. Never full/umbrella build. Imports wired once in RHTower.lean (forcing after SourceVector; full core after OperatorCore).

All 19 public declarations audited with #print axioms from /tmp files: only propext, Classical.choice, Quot.sound. All present in refreshed index (33 total rows including 14 private). Own source files have no prohibited declarations or trailing whitespace. Git diff --check passed on modified existing umbrella and universal ledger.

Logs: `/tmp/sqb9_forcing_build.log`, `/tmp/sqb9_core_build.log`, `/tmp/sqb9_forcing_axioms.log`, `/tmp/sqb9_core_axioms.log`, `/tmp/sqb9_index_audit.json`, `/tmp/sqb9_search_index.log`, `/tmp/sqb9_lint.log`.
`/tmp/sqb9_forcing_exports.json` holds 8 SHORT names; `/tmp/sqb9_core_exports.json` holds 11 FULL names. One initial audit script assertion was a short/full-name mismatch, fixed; all19 checked successfully. No Lean defect.

Global formal lint CURRENTLY FAILED solely for unrelated UNTRACKED module `GaloisForLFunctions.HTGeometry.FokasLenellsRegularOrigin` missing umbrella reachability. Did NOT modify peer module/umbrella. Previous turn's different Fokas lint failure was externally resolved; this is new current live-file failure. Do not claim global lint passed. Can rerun if peer wiring changes, not repeatedly without evidence. All owned handles collected, last compiler was axiom session90017 exit0; final lint42521 exit1 collected. No owned process remained in ps check.

Code hashes after audit:
- SelbergScatteringCutoffForcing: 9ceccbd97af6161a196b80c2daf4bd9fcc5ca04e6253cc77dab491b0e712bc29
- ThetaCuspHawkingBMFullCoreOperator: c7f084c9a8a12eeb04eea7c23e0d553a05ca665ebf535c70ecac05cef49ebd22

## Current docs and next substantive work

In-progress card: `docs/drafts/pipeline/1-in-progress/sqb-native-source-resolvent-transport.md` (current state, full chain and explicit open work). Stage3 papers: `sqb-original-cutoff-forcing.md`, `sqb-full-modular-operator-core.md`. Universal STATUS gained route-independent requirement: a vanishing scalar pairing does not prove vanishing source vector; bilinear pairing cannot be read as squared Hilbert norm. Frontier map untouched.

Original corrected globally smooth modular residual R gives V in native L2, nonzero. C entire covariance, W=CV in T-domain, U=W/||W||, exact transformed G=V-(2+mu)CV. All from previous modules. H is now admitted original DIFFERENTIAL forcing, H nonzero and integral E H0. H is NOT G.

NEXT: construct actual compact modular approximants to R, prove convergence of BOTH values and original operator images. Then closedness A gives V in A.domain and (A-e)V=H, e=1+(rho/2)(1-rho/2), nonreal at every actual Xi. This yields (1-eB)V=BH, B=A^-1, permitting exact CFC transport to G. Even that transport will leave occurrence forcing-control unproved. Do not construct a separate inverse response and silently identify it with original V.

Concrete native cutoff plan (not coded): a=n+3, beta_n(y)=smoothWeight a a y. Equal1 y<=a, zero y>=2a, 0<=beta<=1. Cell expression beta_n(y)*R(z). At nonparabolic closed-cell overlaps both heights<2, beta=1 near overlap, so original modular R gives compatible germs. Parabolic shifts preserve height. Use existing cellGermExtension -> global smooth invariant f_n. On fd, f_n=beta_nR; truncated_cell_compact(2a) -> CellCompact -> CoreField. New full-core operator theorem now supplies exact A-domain action for f_n.

Value convergence follows beta_n ->1 and domination by original admitted R. Operator image convergence needs actual full weighted first-derivative tail estimates plus uniform y*beta'_n and y^2*beta''_n bounds; all errors on heights>=a. Full R high-cell is complete Fourier tail. Prove needed full tail gradients in L2 from corpus joint jet bounds; do not omit modes. Then dominated convergence / native graph norm. No scratch for these approximants yet.

## Broad corpus search evidence and useful APIs

User explicitly asked broad searches, not only ultra-specific AND queries. Used `research ... --any --per-module 0 --limit 100000 --explore 0 --json [--no-refresh]` with output redirected. Counts describe metadata coverage, not reading every proof.
- resolvents/commutators/spectral multipliers/source cancellation/scattering residues:245decl82mods `/tmp/sqb9_residual_broad.json`.
- operator domains/weak solutions/compact forcing/finite energy/energy completion/graph closure:438/127 `/tmp/sqb9_domain_broad.json`.
- cutoffs/graph approximation/compact exhaustion/modular partitions/Dirichlet unfolding/Friedrichs cores:80/39 `/tmp/sqb9_cutoff_broad.json`.
- frame derivatives/height cutoffs/rapid tails/gradient bounds/first jets/energy approximation:22/18 `/tmp/sqb9_gradient_broad.json`.
- SINGLE WORD OR `smoothTransition cutoff partition`:6143/1914 `/tmp/sqb9_exhaustion_broad.json`. Found reusable derivative bounds missed by phrase queries.
- OR `periodization Laplacian "formal adjoint" "test separation"`:911/258 `/tmp/sqb9_laplace_broad.json`. Found actual modular Laplacian covariance and existing compact normalization; inspected source bodies before construction.

Fully READ this turn `formal/GaloisForLFunctions/HTGeometry/SmoothWeight.lean` (~137lines), namespace GaloisForLFunctions.HTGeometry:
- `smoothWeight N H x=1-Real.smoothTransition(H^-1*(x-N))`.
- `smoothWeight_contDiff N H` alln.
- `smoothWeight_eq_one (hH:0<H) (hx:x<=N)`; `smoothWeight_eq_zero hH (hx:N+H<=x)`.
- `smoothWeight_nonneg N H x`, `smoothWeight_le_one N H x`.
- `exists_bound_iteratedDeriv_smoothTransition j`: global all-order bound.
- `exists_bound_iteratedDeriv_smoothWeight_uniform j`: exists C>=0, forall N H>0 x, |iteratedDeriv j (smoothWeight N H)x|<=C/H^j. PROOF actually read: smoothTransition allorder continuous, locallyconstant outside[0,1], compactbound; exact affine iterated chain rule.
- `exists_bound_iteratedDeriv_smoothWeight` fixedwindow variant.
Also read SmoothTransitionDerivBound, uniformfirstderiv Lambda and derivativezerooutside[0,1]. Prefer SmoothWeight for ready scaled cutoffs.

Key current files already read this turn, avoid rereading whole unnecessarily: HalfPlaneGreen (PlanarChartTest structure); GlobalChartTestSeparation (CompactChartTest.ofPlanar); GlobalChartTests; ModularEnergyDomain; GlobalDistributionEquation; OperatorCore; GlobalChartGreen; GlobalPlanarEquation; ChartCoordinates; ModularLaplacian; first48linesFullAngularAssembly; first100linesModularDirichletUnfolding; SmoothModularPeriodization; SelbergCompactPeriodization; SelbergLocalTestGreen; SmoothModularCore1-130; full cutoffs/flux/admission/source modules as documented previous memory.

Proof implementation lesson: inferred ContDiffAt.div/fun_inv could select complex scalar/output instances when composing through ofComplex. Give explicit `have hfz : ContDiffAt ℝ ∞ (f.field ∘ ofComplex) z` and similarly hdz; then explicitly type inverse ContDiffAt ℝ ∞ (fun w:ℂ => (d(ofComplex w))^-1) z, and multiply. `simpa only [a,Function.comp_apply,div_eq_mul_inv]` works. In finite derivative sums, explicitly provide `A := fun i v => f i (ofComplex v)` and local DifferentiableAt at plane w; simplify Function.comp_def. Use `sum_apply`, not deprecated ContinuousLinearMap.sum_apply. Within PlanarChartTest theorem names, qualify `D4BMModularCore.planarLaplacian` to avoid clash with PlanarChartTest.planarLaplacian.

Next turn must start with full proof chain and explain significant step. No agents unless explicitly authorized; one foreground compiler per agent; all new modules wired but no umbrella builds. Keep goal active and exact missing analytic/source occurrence obligations visible.