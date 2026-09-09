# HB compact physical response equation — installed and audited

RH UNPROVED. Goal ACTIVE. Frontier map READ ONLY; preexisting concurrent changes preserved. No numerical experiment, agent, full build or umbrella build ran. Full chain: theta cusp -> Xi occurrence -> complete original source -> original outgoing response and physical adjoint residue -> independent Hawking-clock extinction -> RH.

## Completed results — DO NOT re-audit

Seven canonical leaves, prefix GaloisForLFunctions.RHTower.ThetaCuspHawkingBM:

- JointCoreTestData: CoreField.completed_green for any actual full compact modular core and completed angular energy field, using existing planarTest full modular periodization. RadialCore.differentiate, angularWeighted and exact radial vector identities.

- JointCoreTransposition: joint_angular_green on original completed joint graph, joint_radial_second_green, jointWaveSolution_transposed, actual jointWaveResponse_transposed.

- JointCoreOperator: jointCoreDifferential, exact form identity and jointEnergyOperator_core actual domain/action via J.adjoint and original covariance inverse.

- CuspCutoffProfile: baseCuspCutoff(y)=1-smoothTransition(y-2), scaledCuspCutoff N y=base(y/N). Exact first and second derivatives; common uniform bound on |y chi_N'|, |y² chi_N''|, for every real N (including zero under Lean division).

- ModularCuspCutoff: actual cell-germ extension, for N>=1 invariant, smooth, real, modulus<=1, CellCompact support y<=3N. modularCuspCutoff_eventually_one: every fixed cell point's complete germ eventually constant one along N=n+1.

- PhysicalCoreCutoff: physicalScalar_modular at ACTUAL parameter (r-1)/2, using ALREADY EXISTING physicalScalar_invert, periodicity and SL2Z S/T generation. physicalTestField=conj(full physical scalar). physicalCoreCutoff r n is a constructed original CoreField. Full germ eventually stabilizes; native core Laplacian eventually equals physical-test Laplacian pointwise.

- PhysicalCorePairingLimit: physicalCoreCutoff_inner literal cutoff integral; physicalCoreCutoff_inner_tendsto for height-admitted U and any radial Hilbert h. physicalCuspResponse_compact_test_limit supplies weighted admission internally for actual complete cusp response. completeCuspResponse_compact_equation supplies exact full original equation for constructed tests.

36 public theorems + 8 definitions; 623 Lean lines. All scratch lake env lean checks passed. Seven individual lake build exactmodule audits warning-free with cached dependencies. One scratch #print axioms checked ONLY the 44 new public declarations: each exactly propext, Classical.choice, Quot.sound. Installed 7 sources and 14 olean/ilean artifacts with 21 SHA256 equality checks; wired each leaf exactly once after BMPhysicalWeightedResponse in RHTower.lean. Index refreshed once. scripts/formal_tools.py lint --check-generated EXIT0, existing large-file warnings only. git diff --check passed. All process handles terminal; no owned Lean/Lake processes remain. Private /tmp/hb-projected-equation.__ny8tkc and marker /tmp/hb-projected-equation-current REMOVED.

## Exact mathematical state

For actual U=J jointWaveResponse(w,F), original radial core f and FULL compact modular core g:

<f'' tensor g,U> + <sech(t)^2 f tensor Delta_H g,U> - w²<f tensor g,U> = -<f tensor g,F>.

Test-first Hilbert convention is conjugate linear in first argument. Full source retained. Actual original operator action on f tensor g is f tensor g - f'' tensor g - sech² f tensor Delta_H g; domain membership proved.

For g_n=chi_(n+1)*conj(E_r), lim_n <h tensor g_n,U>=<h,P_r(yU)> for any radial Hilbert h, with weighted admission supplied internally on 3/2<Re w<2, Im w!=0 for actual complete source response. Previous response norm proof: mem:hawking_bm_original_weighted_response_2026_09_09.

## Immediate obstacle — attack directly

Must identify ANGULAR LAPLACIAN INTEGRAL LIMIT with lambda times physical projection. Pointwise full-germ stabilization and mass-pairing convergence do NOT establish this.

Concrete next proof:

1. Transport scaled cutoff derivatives via modularCuspCutoff_germ and chartLaplacian_coordinates/congr. On fd: Delta(chi*conjE)=chi*conj(lambda E)+2(y chi')*(y partial_y conjE)+y² chi''*conjE. Profile first/second uniform bounds ALREADY CLOSED. Need actual chart product rule with both commutator terms.

2. E/y in angular L2 is closed by physicalDualDensity_memLp. Prove (weightedDeriv I E)/y=ordinary vertical derivative E in angular L2. Use actual value_coordDeriv_one (shift nu±1, powers/degree shifts) and weighted_value_bounded from BMAngularCuspBounds for tail. Exact physical principal E=reflectedCompletedLambda(r-1)*y^(1-r/2), whose ordinary derivative is coefficient*(1-r/2)*y^(-r/2), bounded at high cusp using 0<Re r<1. Existing full scalar smoothness handles compact part.

3. With yU in L2 and above angular bounds, dominate cutoff commutator pairings by integrable products and let derivatives vanish pointwise. Main term limit follows new mass-pairing theorem. Preserve conjugation: final coefficient lambda, not conj lambda.

4. Obtain actual radial distribution equation R=P_r(yU): <f'',R>+lambda<sech² f,R>-w²<f,R>=-<f,P_r(yF)>.

5. Prove ACTUAL radial endpoint conditions; radial L2 alone does not impose outer Dirichlet. Prior weighted energy can supply weighted radial derivative if needed. Identify same observable with original radial Green on causal overlap; continue same observable to QNMs. Projected continuation does not prove full joint inverse meromorphy. Physical adjoint residue, full-source pole survival, spin-two/AIME and independent extinction still open.

## Verified corpus and Lean pitfalls

BMFullCoreOperator: CoreField.planarTest, planarTest_periodize, laplacian : CoreField, energyOperator_apply, full seams. BMChartCoordinates: angularCoordinates : Complex ≃L[Real] (Fin2->Real), chartLaplacian_coordinates/congr. BMPhysicalAngularCutoffCalibration already has physicalScalar_invert; DO NOT reprove generic clearFactor cancellation. Physical parameter (r-1)/2 differs from center q=q-1/2.

BMPhysicalWeightedResponse: physical_height_pairing_integrable, physicalJointProjection_height_integral, completeCuspResponse_height_memLp. BMAngularScalarEquation: value_coordDeriv_zero/one, scalarCusp_hyperbolicLaplacian=(u²-1/4)*scalar. BMEisensteinCuspJointSmooth: cuspLeg_contDiffOn infinity and finite cuspLeg_contDiffAt.

PhysicalCorePairingLimit uses literal Bochner dominated convergence directly; no need to build abstract Lp DCT. Test inner integrand AE via l2SeparatedProduct_ae and quasiMeasurePreserving_snd.ae_eq_comp core_field_memLp.coeFn_toLp.

ContDiff.deriv DOES NOT EXIST; use (contDiff_infty_iff_deriv.mp h).2. For HasDerivAt.div_const compositions, simpa only [Function.comp_def,id_eq] may be needed. Before rw under lambdas, change explicit expression. Pin intermediate ContDiffAt composition types for angularCoordinates. Avoid inline 'have ... := by positivity; linarith' since semicolon scopes incorrectly; use multiline or helper lemma. innerSL is global.

## Documents and search

Current card: docs/drafts/pipeline/1-in-progress/hb-physical-response-radial-equation.md. Full proved scope/audits: docs/drafts/pipeline/3-formalized/hb-compact-physical-response-equation.md. STATUS added route-independent F20i-ab: differentiated test integral limit must be justified; local pointwise stabilization and mass convergence insufficient. Frontier map not edited by this work.

Requested broad searches completed in order via research single terms: Fokas 2254 declarations/163 modules; Higgs 285/26 at query time. Also broad cutoff 4751/1454. Search metadata counts are not mathematical evidence.