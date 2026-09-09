# Selberg cycle48 — original core Green and complete observed cusp forms

Latest continuation of mem:selberg/character-seam-phase-flux-2026-09-09. Full unbudgeted Selberg1/4 goal remains ACTIVE / UNPROVED. Previous goal turn classified PROGRESS and both cycle47 source hashes revalidated unchanged. This turn also PROGRESS:52 new audited public declarations, no endpoint assumption. Do not mark complete or blocked. User wants positive corpus-derived conjecture→proof/fail→pivot loops.

## Finished sources — do not repeat their proofs/checks

1. formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterDynamics.lean, matching namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics.18 public declarations, plus local gammaNormal. Imports CharacterSeamFlux.
- source_readout_dir: any fixed L:E→L[Complex]Complex commutes with original source-chart first real derivative.
- source_readout_second_dir: same for both repeated real derivatives, proved by source C² and equality on a positive-height neighborhood.
- sourceVector_laplacian: complete vector actual equation DxxF+DyyF=(-(lambda/y²):Complex) • F.
- source_readout_laplacian: every fixed observation retains actual scalar potential, including zero fields.
- characterField_contDiffOn, characterField_laplacian, characterField_dir: actual projected component retains C², eigen-equation and derivative=P(original derivative).
- characterMass N f p r w := ||P_p,r sourceVector(ofComplex w)||², original chart function Complex→Real.
- characterGradient N f p r z :=||P D_1F(z)||²+||P D_I F(z)||².
- characterMass_eq_sum; characterMass_contDiffOn.
- characterField_normSq_laplacian.
- CAPSTONE characterMass_laplacian at142: Delta(characterMass)(z)=2*(characterGradient(z)-(lambda/z.im²)*characterMass(z)). Complete original gradient retained.
- characterProjection_commute_block: P_p,r U_(p j)=U_(p j)P_p,r, by actual complete block commutativity; no phase/angle hypothesis.
- upperBlock_one_eq_T: finite upper parameter1=mk T, via upperBlock_intCast and upper_eq_T_zpow.
- characterMass_translation; characterMass_current_translation: actual T transport preserves mass and every physical mass derivative.
- characterMass_current_sides: literal mass currents at x=+1/2 and -1/2 agree for positive y.

2. formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterCoreGreen.lean, matching namespace.19 public declarations plus local instance. Imports Dynamics and actual SelbergModularPotentialGreen.
- arcCurrent r v x:=dir v(characterMass upper r)(point x(arcHeight x)). ContinuousOn full core arc proved, also reflected arcCurrent.
- circleNormalCurrent_components: actual cycle47 circle normal current equals (-x/y)*D_x M-D_y M for positive y.
- pairedArcCurrent r x:=circleNormalCurrent(x,arcHeight x)+circleNormalCurrent(-x,arcHeight x).
- pairedArcCurrent_components: x/y*(arcCurrent1(-x)-arcCurrent1(x))-(arcCurrentI(-x)+arcCurrentI(x)), exactly.
- horizontalArc_continuousOn, pairedArcCurrent_continuousOn: all physical boundary integrability inputs discharged.
- topCurrent r Y:=integral x=-1/2..1/2 of D_y characterMass at point x Y.
- character_area_stokes: ordinary planar integral_core Delta M =topCurrent+integral x=0..1/2 pairedArcCurrent. Actual side matching discharged; circle current NOT assumed zero.
- massAt r p:=characterMass(point p.1 p.2)/p.2².
- quarterAt r p:=characterGradient(ofComplex(point p.1 p.2))-characterMass(point p.1 p.2)/(4*p.2²).
- coreMass r Y:=integral_domainY massAt; coreQuarter:=integral_domainY quarterAt.
- quarterAt_eq_laplacian_mass at positive height: quarterAt=DeltaM/2+(lambda-1/4)*massAt.
- massAt_integrableOn, laplacian_integrableOn, quarterAt_integrableOn for every compact core.
- CAPSTONE core_quarter_identity at192: for Y>=1, coreQuarter=topCurrent/2+(integral_0^(1/2) pairedArcCurrent)/2+(lambda-1/4)*coreMass. All terms literal actual source; no boundary positivity hypothesis.

3. formal/GaloisForLFunctions/RHTower/SelbergMaassReadoutCusp.lean, matching namespace.15 public declarations +local instance +3 private zero helpers. Imports Dynamics and actual SelbergMaassBoundaryForm.
- readoutInvariant N f L: actual congruence-invariant function z↦L(sourceVector z). Each original component supplies Γ invariance.
- sourceVector_cusp_decay: full vector tends to0 at each integral cusp, via finite coordinate convergence and PiLp.continuous_toLp.
- readout_cuspidal: L continuity retains every original cusp condition.
- readout_eigen: positiveHyperbolicLaplacian of observed source=lambda times itself.
- readout_zero_or_maass: every fixed L observation is identically0 OR an actual MaassCuspEigenform at same level/eigenvalue with exactly those values. C², eigen and cusp conditions all constructed; no nonvanishing input omitted.
- characterField_zero_or_maass: specialization to L=(EuclideanSpace.proj q).comp P_p,r.
- readoutQuarterSlice L y: literal integral x=0..N+1 of |D_x LF|²+|D_y LF|²-(1/(4y²))*|LF|² in the original chart.
- readoutModeSquareTail L T n: if n=0 then0 else integral y>expT of the actual Bessel remainder applied to coefficient(N+1)n(observed original chart).
- readoutModeSquareTail_nonneg.
- readout_seam_summable: complete original Bessel seam series (all integer n) of observed coefficients summable, any actual lambda.
- CAPSTONE readout_boundary_square_identity at127: actual exceptional lambda:Ioo(0,1/4), normalized full observed physical cusp quarter integral =full seam series+tsum of all observed modeSquareTail. Both zero and genuine Maass cases proved; no assumed Bessel ansatz.
- readout_square_tail_summable: full square series genuinely converges, not default divergent tsum.
- readoutMass L y:=level^-1*SelbergMaassFlux.pairing level F_L F_L y.
- readoutFlux L y:=level^-1*pairing level (directional I F_L) F_L y.
- CAPSTONE readout_flux_boundary_identity at180: -readoutFlux(expT)+(lambda-1/4)*integral_y>expT readoutMass/y² =same complete boundary series+full square series.
All readout formulas derive from actual readout_zero_or_maass and existing Maass identities, retaining zero fields. Private helpers handle whole zero coefficient/directional functions and zero pairing.

## Positive loop / corpus evidence

Explicit OR queries (spaces mean AND; --any used): Green identity/boundary form/Dirichlet-to-Neumann/impedance ->197 declarations in78 modules, /tmp/selberg_core50_corpus.json. Projected source/linear combination/cusp condition/eigenfunction space ->295/196, /tmp/selberg_core50_linear_corpus.json. All matching metadata retrieved; not every proof body inspected.
Read actual SelbergModularPotentialGreen (complete horizontal/vertical integration with conditions), SelbergMaassTraceArea (whole-trace core/cusp identity), full original BoundaryForm/BesselRemainder definitions, MaassCuspAutomorphicCorrespondence subtype, MaassHomogeneousSpaceCorrespondence invariant submodule, SelbergMaassDeckAverage cusp sum proof. PinnedBoundaryExactInertia was read as a mechanism for retaining full boundary form before sign claims; its theta-specific premises not transferred to Maass.
Conjecture→proof: projected original derivatives/PDE; exact projected norm-square Laplacian; actual side matching; full coherent curved-seam Green identity; physical core quarter identity; every observed source zero or genuine same-level cuspidal Maass source; full observed cusp boundary-square/summability/flux identities. No numerical experiments or negative wrappers.

## Completed audit

All3 complete scratch files, all3 exact source checks and all3 final builds passed with no new-source warnings. Only Dynamics olean emitted pre-final as needed dependency. Final builds serialized and each rebuilt ONLY its named target: Dynamics13s, CoreGreen10s, ReadoutCusp21s. Cached EvenL2LogUnitary informational suggestion is existing output.
All52 public declarations passed post-build #print axioms in /tmp: only propext, Classical.choice, Quot.sound. All source SHA256 hashes unchanged. Exact names/hashes /tmp/selberg_core50_manifest.json; final audit /tmp/selberg_core50_audit.json. Search/API coverage all52 under exact modules;58 index entries incl3 locals+3 privates. All3 imports once in RHTower. Index and repository formal lint PASSED, existing large-file warnings only. Source hashes/whitespace and all links in3 updated research cards checked.
Every owned Lean/build/index/lint handle TERMINAL; final process scan no owned Lean/Lake. No overlap/full/umbrella build/numerical experiment/commit/push. Some other agents' Lean workers were visible; not touched. Never start a next owned Lean while write_stdin still returns session_id.
Artifacts prefix /tmp/selberg_core50: dynamics.lean/log, green.lean/log, cusp.lean/log; respective _source.log/_build.log; axioms.lean/log; manifest.json; audit.json; coverage.json; index.log; lint.log; corpus.json; linear_corpus.json.

## Persistent card / NEXT concrete assembly

Card remains docs/drafts/pipeline/1-in-progress/selberg-character-core-green.md. DO NOT move it to3-formalized yet: finite core–cusp assembly and quantitative full quarter comparison remain required. All52 current-source audits complete. Parent selberg-quarter-conjecturing-loop.md has cycle48 and newest verification entry; selberg-original-source-conserved-currents.md frontier updated.

For each actual upper character r take L_q=(EuclideanSpace.proj q).comp (characterProjection N (upperBlock N) r).toContinuousLinearMap.
1. Prove sum_q readoutFlux(L_q,Y)=topCurrent_r(Y)/2. The literal derivative of M_r equals2*sum_q Re(D_y(PF)_q*conj(PF)_q), via character_mass_dir +characterProjection_inner_left and coordinate inner sum. It is unit-periodic using characterMass_current_translation for arbitrary z, then translation_point and coe_ofComplex_point.
2. Convert width-N+1 integral to unit interval by Function.Periodic.intervalIntegral_add_zsmul_eq, then shift unit interval using intervalIntegral_add_eq. Existing exact model: SelbergMaassCongruenceTrace.density_integral_eq_sum_mass at159–184; its hper/hscale proof read this turn. Source file SelbergMaassTraceStokes.unit_current_eq_sum_flux at110 is another actual model, but uses derivative of mass; first part read.
3. Sum readout_flux_boundary_identity over ALL q; adjoin core_quarter_identity. Target exact formula:
coreQuarter_r + boundarySum_r + squareSum_r = pairedArcIntegral_r/2 + (lambda-1/4)*(coreMass_r+tailMass_r).
Define every sum from the literal L_q observations; preserve full countable modes, actual seam, and nonnegative squares. Finite sum/tsum exchange can use proved summability. Identify tailMass as original physical projected mass using unit-period mass normalization.
4. Then use cycle47 actual phase/arithmetic current bound and angular remainder to test source-derived full-domain mass<=4physicalgradient. That is still the real goal, never an assumed endpoint. Do not present completed inputs as completed Selberg.

## Verified THIS-toolchain proof lessons

Congr on EuclideanSpace functions can descend into PiLp exponent and create spurious goal ENNReal. In characterProjection_commute_block avoid congr2: prove hc:p k*p j=p j*p k from map_mul/mul_comm, then rw[mul_assoc,mul_assoc,hc].
Source/coercion equality: explicitly change RHS into literal quotientForm value before simpa. Likewise change readout CLM-composition statements to actual characterField before simplification; simp alone may leave semireducible coercion mismatches.
There is NO EuclideanSpace.proj_apply. Projection application is definitional: change to P v q. IsCuspidalAtIntegralCusps: after introA explicitly change to Tendsto atImInfty(nhds0), then simp only[Function.comp_def,map_zero].
Core boundary tangent: provide hcy:(y:Complex)≠0 from Complex.ofReal_ne_zero hy.ne' before field_simp. Explicitly type IntervalIntegrable with volume and0..1/2; otherwise IsLocallyFiniteMeasure meta is stuck.
IntegrableOn.congr_fun dot notation failed after .add because elaborator exposed And. Use explicit Integrable.congr, filter_upwards[ae_restrict_mem measurableSet] and pointwise equality.
For coe_ofComplex point, form hc:((ofComplex point):Complex)=point and hi:im=height, rw[hc,hi] at characterMass_laplacian. This avoids rewriting every UHP point into a constructor.
Simp with partial coefficient/directional functions needs whole-function zero lemmas proved by funext. Scalar simp only unfolds fully applied definitions otherwise. For square-tail Summable change function by funext equality first, then apply actual maass_square_tail_hasSum.summable.
Actual namespaces != filenames: SelbergMaassBesselRemainder uses SelbergMaassBessel; SelbergMaassBoundaryTrace uses SelbergMaassTrace; SelbergBesselBoundaryOperator uses SelbergBoundaryOperator; point/directional/periodIntegral use SelbergMaassMean in FourierMean; coefficient/maassCoefficient use SelbergMaassFourier in FourierModes.
Use rg --files before any unobserved path. NO SelbergMaassWeakEigenfunction.lean, SelbergMaassCoreEnergy.lean, or SelbergMaassCoreStokes.lean. Existing actual paths listed above are verified.
