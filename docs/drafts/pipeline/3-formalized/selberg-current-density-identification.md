# Actual density of the Maass current measure

- **ID:** SELBERG-CURRENT-DENSITY-IDENTIFICATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Original source currents](../1-in-progress/selberg-original-source-conserved-currents.md), [proved positive measure split](selberg-current-nodal-measures.md), Selberg cycle 40 continuation.
- **Objective:** Identify the actual current measure with its source density, retaining the separately proved nodal residual; continue toward the unchanged unconditional Selberg quarter bound.

## Source-derived theorem

Write D for the original trace density, C for the pair-plus-phase square numerator, and R_e=sqrt(D+e²). The proved regulated current is C/R_e³. The representing current measure equals hyperbolic volume weighted by y²*C/(sqrt(D))³, with value zero at original common zeros. Every compact-test density product is genuinely integrable, and the actual current integrals converge to its literal integral. The current and residual are mutually singular, are the restrictions of full curvature to the complement of the original nodal set and to that set, and are each modular invariant. These are identifications of existing source measures, not new endpoint hypotheses.

## Dependency-closed paper proof

At D>0, continuity of the positive square root makes R_e³ tend to the nonzero amplitude cube. At D=0, the original source theorem gives C=0, so the regulated current and the literal division-defined density are both zero. Tests vanish outside the upper half-plane, so their pointwise convergence holds on the entire plane even though source regularity is only local to the chart.

Take e_n=1/(n+1), with positivity, antitonicity, and convergence to the actual positive-regulator filter proved. For each nonnegative compact continuous test phi, the products phi*C/R_e_n³ are integrable, nonnegative, and monotone in n. Their integrals are bounded by the original finite full-curvature value L(phi). Extended-real monotone convergence shows that the integrals of their ENNReal.ofReal values converge to the extended integral of phi*C/(sqrt(D))³. The genuine regulated integrability identifies each prelimit extended integral with ofReal of its real integral. Passing the source bound to the limit gives an upper bound ofReal(L(phi)), strictly below infinity. Pointwise convergence of the measurable approximants proves measurability of the limit too. These two facts establish genuine density integrability.

Apply this to |phi|. It is again a continuous compact test with the same supported chart. Its integrable density product dominates the norm of every signed regulated product, including at original zeros. Dominated convergence along the actual countably generated positive-regulator filter identifies the full signed-test limit with the literal density integral. Comparison with the already proved currentMeasure compact-test limit proves equality of their pairings. No local convergence is promoted to a global mass assertion.

Define h(z)=y²*C/(sqrt(D))³ on the actual upper half-plane. Local continuity of C and amplitude makes their quotient measurable even at zeros; h is nonnegative. Set nu=volume.withDensity(ofReal h). The chart pushforward and the withDensity integrability theorem prove that y²*F on the upper half-plane is integrable exactly when F is integrable on the positive-height planar region. Thus every compact test is genuinely integrable for nu by the preceding density-product theorem. The integral chart identity cancels the y² factor against hyperbolic density y^-2 and gives the same planar density pairing.

For each compact K, choose an actual nonnegative compact continuous cutoff g equal to one on K. Its proved nu-integrability gives nu(K)<=ofReal(integral g dnu)<infinity. Hence nu is finite on compact sets and regular on the actual metrizable sigma-compact upper half-plane. Regular-measure uniqueness identifies nu with currentMeasure. Its definition proves absolute continuity relative to hyperbolic volume. On the literal nodal set h=0, so the withDensity measure vanishes there independently of that set's area. The already proved residual measure vanishes on the complement. This supplies a measurable separator proving mutual singularity of the two source measures.

This does not yet establish residual singularity relative to volume. In particular, current absolute continuity plus residual concentration on the nodal set is not a full Lebesgue-decomposition certificate without further control of that set or residual measure.

## Stronger source-carrier theorem and proof

The exact sum and disjoint concentration identify residualMeasure with curvatureMeasure restricted to the nodal set, and currentMeasure with restriction to its complement. Restriction distributes over measure addition. On the nodal set, the current restriction is zero and the residual restriction is the full residual measure; the complementary identities follow from the same measurable partition. These identities use addition and restriction only; they do not cancel possibly infinite measures by subtraction.

The literal nodal set is invariant under the modular action because the original trace density is invariant. Pushforward commutes with restriction to its measurable preimage. The already proved full-curvature invariance therefore transports both constituent measures separately. The resulting map identities give invariance on every measurable preimage and modular change of variables for each measure's real integrals. No new current Jacobian calculation, vanishing current period, or deletion of seam charge is used.

## Corpus evidence and gates

- [x] Current source re-read: CurrentTests, CurrentMeasures, ResidualSupport, WeakCurvature, CurvatureMeasure, CurvatureTransport, and regulator filter.
- [x] Wide OR discovery: monotone integral / density measure / integrable limit / Radon Nikodym / positive limit gives 152 declarations in 65 modules. Fatou / Beppo / bounded integrals / monotone convergence gives 120 in 32. Counts are index coverage, not proof-body coverage.
- [x] Inspect source mechanisms and verify new library names in scratch.
- [x] Prove exact pointwise source density limit and compact-test integrability/convergence.
- [x] Prove actual density-measure equality, including finiteness and regularity.
- [x] Prove current absolute continuity, zero nodal current mass, and mutual singularity of the two source measures.
- [x] Prove exact carrier restrictions and separate modular invariance.
- [x] Scratch/source checks, serialized single-module final builds, axiom/index/lint audit, umbrella wiring.

## Scope

Selberg remains active and unproved. This density identification alone gives no congruence-uniform lower comparison. The positive residual remains concentrated on common zeros; no nodal contribution is dropped. Numerical experiments, endpoint premises, and full builds are excluded.

## Source mechanisms and further frontier

Inspected `MobiusCenteredMertensLimit` derives finite-energy information from actual pointwise approximants and a Fatou bound; its one-dimensional source is not substituted for the Maass source. Inspected `RiemannXiUpperHeightTrace.tendsto_tsum_ennreal_of_monotone` derives the extended limit from monotonicity and exact supremum bounds. The new proof applies the general integral version with all Maass test bounds discharged. Inspected `CirclePoissonProductEquivalence` identifies a density measure by matching its actual determining test integrals; the new noncompact setting additionally requires the compact-finiteness argument above.

The invariant-carrier / measure-restriction / mutual-singularity / nodal OR search reached 520 declarations in 99 modules. Inspected `BoundaryBarycenterSpectralTransport.measureBarycenter_mutuallySingular` uses actual measurable label preimages as separators. Inspected `ProjectiveLabelNullPreimage` needs real analyticity for its source's null-preimage theorem; that analytic input has not been transferred to original Maass fields. The new nodal restriction argument does not need it.

The elliptic-regularity / unique-continuation / nodal-measure / entropy-production / current-lower-bound OR search reached 102 declarations in 20 modules. Inspected `PlanarSobolevLaplacianGain` proves a genuine two-derivative Sobolev gain from an already controlled actual Laplacian, with the Fourier normalization explicit. This is not an analytic zero-set theorem. The interior elliptic response module's declaration inventory exposes source and cutoff commutators; no transfer to an arbitrary original Maass nodal set is claimed. Entropy-current control still needs an actual source identification and a uniform constant.

## Lean modules

All three modules are under `formal/GaloisForLFunctions/RHTower/` and imported exactly once in its umbrella.

| Module | Public declarations | Main result |
|---|---:|---|
| `SelbergMaassCurrentDensity` | 14 | Genuine density-test integrability and full regulator-limit identification |
| `SelbergMaassCurrentDensityMeasure` | 14 | Actual withDensity equality, absolute continuity, zero nodal current mass, mutual singularity |
| `SelbergMaassCurrentCarrier` | 11 | Exact restrictions and separate modular invariance |

All 39 public declarations, including two measure instances, passed complete scratch and needed-source checks without warnings. Scratch files: `/tmp/selberg_{currentdensity,densitymeasure,currentcarrier}42.lean`; name checks: corresponding `42_names.lean` files. Final serialized `lake build` audits passed, rebuilding only their named target: CurrentDensity 4.1s, CurrentDensityMeasure 3.4s, CurrentCarrier 3.5s. Build logs: `/tmp/selberg_{currentdensity,densitymeasure,currentcarrier}42_build.log`. Existing cached EvenL2LogUnitary informational output was replayed; the three new modules emitted no warnings. No full or umbrella build ran.

The post-build `lake env lean /tmp/selberg_currentdensity42_axioms.lean` audit passed. All 39 expected names, including both measure instances, report only `propext`, `Classical.choice`, and `Quot.sound`. All three source hashes remained unchanged. Exact name/hash artifacts: `/tmp/selberg_currentdensity42_counts.json`, `/tmp/selberg_currentdensity42_hashes.json`; axiom log: `/tmp/selberg_currentdensity42_axioms.log`.

All 39 public declarations are searchable; the API catalog contains 37 noninstance rows, with named instances excluded by its documented parser. Each module has exactly one umbrella import. Coverage artifact: `/tmp/selberg_currentdensity42_coverage.json`. Index refresh and repository-wide formal lint passed, with existing large-file warnings: `/tmp/selberg_currentdensity42_index.log`, `/tmp/selberg_currentdensity42_lint.log`. The prior unrelated FokasLenellsRawPhase wiring error no longer occurs; this task did not edit that module.

## Log

- 2026-09-08 — Interrupted preceding continuation performed no tool work; revalidated current sources and resumed the next safe proof action. Candidate recorded before new Lean code.

- 2026-09-09 — Complete density, measure-separation, carrier-restriction, and modular-invariance proofs passed all targeted final audits and repository lint. Every task-owned Lean/build handle is terminal. No full/umbrella build, numerical experiment, commit, or push. Selberg remains active and unproved.
