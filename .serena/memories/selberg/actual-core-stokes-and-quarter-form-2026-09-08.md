# Cycle 25 complete: actual standard-area core Green theorem and full Maass quarter form

Goal remains ACTIVE, unbudgeted, all-congruence Selberg 1/4 UNPROVED. Do not mark complete. User wants corpus-derived conjecture/proof/fail/pivot work, no training-data route judgments, no numerical experiments, no added axioms or assumed positivity.

## Durable cards
Parent: docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md. Cycle25 checked; cycle26 now planned.
Exact paper proof/audit: docs/drafts/pipeline/3-formalized/selberg-maass-core-stokes-and-quarter-form.md.
Prior: mem:selberg/integral-cusps-and-finite-congruence-trace-2026-09-08 and mem:selberg/actual-bessel-boundary-form-2026-09-08.

## Five finished modules, formal/GaloisForLFunctions/RHTower
All imports wired into RHTower.lean (around16235). Read existing sources before edits.
1. SelbergMaassTraceEnergy (209 lines): generic actual real directional dir, normSq_dir/normSq_second_dir, finite derivative sums, realLaplacian, actual maass_normSq_laplacian, gradientDensity and nonnegative proof, trace_laplacian, first/second current continuity, quarterDensity_eq_laplacian_mass.
2. SelbergMaassTraceBoundary (241): actual current and current_modular via reciprocal-square Möbius Jacobian, radial_inversion for every ℍ point, actual unitcircle inversion and arc current cancellation, translation/side current cancellation. Coordinate currentAt and actual vertical/horizontal derivative and continuity APIs.
3. SelbergMaassTraceStokes (163): arcHeight sqrt(1-x²), positivity/square; actual vertical/horizontal current FTC; literal pairedBulk and pairedTop, paired_stokes for every Y>0; pairedTop_eq_unit_current, unit_current_eq_sum_flux, paired_stokes_flux, paired_stokes_bessel_identity. The unit current identification uses real trace lifted to ℂ, prior periodIntegral_hasDerivAt, integral_complex_ofReal, and uniqueness against density_slice_mass_hasDerivAt.
4. SelbergModularDomainSlices (483): actual domain := cell∩{arcHeight x≤y}, cell=[-.5,.5]×[.5,Y]. Compactness and indicator Fubini give setIntegral_eq_vertical (Y≥1) and setIntegral_eq_horizontal for real F. Exact sideRadius geometry below y=1, full unitinterval slices above1, lower slices union of2 intervals overlap only in singleton. Slice integrability/support, horizontalSliceIntegral_eq_full/_eq_sides. Generic helpers depend on stated integrability; actual caller proves it from source. Imports TraceStokes+mathlib Prod+IntegrationByParts only.
5. SelbergMaassTraceArea (316): secondAt Nf v w (p:ℝ×ℝ), actual joint compact continuity/integrability, current_arc_continuousOn. horizontal_area_eq_arc uses horizontal Fubini, split arcFloor..1..Y, FTC, side cancellation, monotone circle change of variables. horizontal_area_eq_bottom uses inversion. vertical_area_eq_top_sub_bottom uses vertical Fubini+FTC. area_stokes_flux line219 proves STANDARD TWO-DIMENSIONAL area integral of ΔD =2∑actualflux. area_eq_pairedBulk line290 closes the former area/paired identification gap. coreMass, coreQuarter, core_mass_integrable, core_quarter_identity line258, coreMass_nonneg. core_cusp_quarter_identity line297 and core_boundary_upper_bound are final capstones.

## Exact mathematics
D=∑q |f_q|², G=∑q(|∂x f_q|²+|∂y f_q|²), actual C² congruence translates.
ΔD=2(G-λD/y²).
OmegaY standard modular planar core: |x|≤.5, sqrt(1-x²)≤y≤Y.
For Y≥1, ∫OmegaY ΔD=2∑q Jq(Y).
Mcore=∫OmegaY D/y², Qcore=∫OmegaY(G-D/(4y²)).
Qcore=∑Jq+(λ-.25)Mcore.
For λ∈(0,.25), T≥0,Y=expT:
Qcore(Y)+boundarySum(T)+squareSum(T)=(λ-.25)(Mcore(Y)+tailMass(Y)).
squareSum≥0 is prior actual convergent Fourier square remainder. Therefore core+boundary has an UPPER bound, not the missing lower bound.
No abstract core matrix, inverse, positivity, lift, eigen-equation for D, or vanished boundary cost assumed.

## Corpus evidence / next cycle
Whole-corpus Laplacian square query + read ThetaCuspHawkingBMSquareSourceDifferential.fullSquarePotential_laplacian supplied norm-square gradient forcing idea.
Paired boundary source idea: ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral.
NEW Stokes query found ThetaCuspHawkingBMEisensteinActualFirstStokesFubini; read geometry/Fubini sections659..1255 and circular argument1303..1508 plus Integral circle substitution731..793. Adapted SOURCE mechanics into real narrow helpers; DO NOT IMPORT these broad specialized modules.
Queries Dirichlet Neumann and Schur boundary, source reads HTGeometry/StokesCoronaSchurVanishing lines1..120 and SchurComplementKernel1..105 (latter imports Mathlib umbrella!) identify exact elimination mechanisms but require actual blocks/invertibility. Prior card already warns generic Schur wrapper is not progress toward source positivity.

Cycle26: prove strict positivity of total physical core+tail trace mass; attempt genuine source-derived nonnegative lower bound for Qcore+B using actual congruence boundary coupling/adverse Bessel channels. Must construct actual response and prove coercive eliminated complement; do not assume them. Test proposed estimates symbolically on explicit toy forms, prove/fail/pivot. A formal conditional implication 'if Qcore+B≥0 then Selberg' is not requested achievement. The actual area/core analytic interface is NOW finished; do not repeat it.

## Verification (all terminal)
Complete scratch and direct source checks passed without warnings; needed oleans created only by lake env lean -o.
Five sequential LEAN_NUM_THREADS=1 lake build <singlemodule> all passed, each built only its named target, cached dependency diagnostics replayed. No umbrella/full build.
Logs /tmp/selberg_trace_energy_build.log, _trace_boundary_build.log, _trace_stokes_build.log, /tmp/selberg_domain_slices_build.log, /tmp/selberg_trace_area_build.log.
94 PUBLIC definitions/theorems audited via lake env lean /tmp/selberg_core_quarter_axioms.lean. All94 reports present, no errors, only propext/Classical.choice/Quot.sound or none. Logs /tmp/selberg_core_quarter_axioms.log, declarations list /tmp/selberg_core_quarter_declarations.txt.
Index refreshed, corpus returns area_stokes_flux and core_cusp_quarter_identity. Source whitespace and tracked diffcheck pass.
LATEST global lint FAILED ONLY 5 unrelated UNTRACKED UNWIRED HTGeometry: FokasLenellsJumpGeometry, FokasLenellsSingularPhase, InwardPlaneDisplacementReturn, InwardPlanePrescribedStream, PolyatomicSpectralRank. Log /tmp/selberg_core_quarter_lint.log, indexlog /tmp/selberg_core_quarter_index.log. No new Selberg errors. Do not assert global lint pass from old records. Do not modify/wire unrelated work.
All task-owned Lean/build handles terminal; no remaining task Lean processes. NO task commit/push. Other agents may commit shared files; Energy/Boundary became tracked clean during turn without task commit.

## Process lessons
ONE task-owned foreground Lean invocation at a time; await handle terminal before next. Set LEAN_NUM_THREADS=1 on final targeted Lake audits; inspect actual workers. No big research imports. #print axioms scratch only. No extra computational/numerical tests.
Lean rewriting often fails on unreduced lambdas; use dsimp only before rw or literal change.
Specify x:=x for currentAt_arc_cancellation: otherwise arcHeight square rewriting can infer wrong x.
Specify f in intervalIntegral.integral_comp_neg (fun x=>currentAt ... x Y).
OfComplex lemma returns an equality of ℍ objects; coe identity use by rw[ofComplex_apply_of_im_pos(...)] not direct exact.
Use Complex.continuous_ofReal.comp; Continuous.ofReal does not exist here.
Use current setIntegral_union₀, not deprecated integral_union_ae.
All current source/scratch names are verified against this toolchain.