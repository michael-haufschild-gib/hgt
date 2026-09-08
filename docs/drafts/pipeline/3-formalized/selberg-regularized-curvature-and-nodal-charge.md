# Actual regularized Maass curvature and surviving nodal charge

- **ID:** selberg-regularized-curvature-28
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 28](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** The actual regularized congruence-trace amplitude satisfies a standard-area curvature balance with its full top current; a local nodal profile has an exact nonzero integrated curvature limit.

## Goal and exact scope

Obtain a smooth actual-source identity through common trace zeros, then test a proposed removal of the regularization defect. The original core/Bessel quarter lower bound is still unproved. None of these statements establishes Selberg's conjecture or assumes that bound. The generic scalar-potential Green theorem has explicit smoothness and matching-current conditions; the actual Maass application proves every condition from its original source.

## Corpus-derived conjecturing loop

Discovery used broad OR searches (`--any`), respecting that unflagged multiple terms mean AND. Query families covered resistance/capacity, Dirichlet/boundary transport, Hardy/chord/oscillation, congruence/Hecke/Ramanujan, trace formulas/amplification, regularized norms, nodal measures, Fisher/square roots, and Green/divergence formulas. The resistance and boundary families returned thousands of declarations across thousands of modules. This is search coverage, not a claim to have read every result.

The source read in `SchwartzPositiveCompactDiagonal.pointwiseMulConj_nonnegativeSquareRootRegularization_self` retains an explicit cutoff error in a smooth square-root construction. That mechanism suggested regularizing the actual trace while retaining its constant-square correction. `PutnamApproximateIdentity` supplied a mass/concentration/local-oscillation viewpoint. A further OR search for nodal, curvature, defect measure, concentration, and ground state returned 6310 declarations in 1042 modules. `HTGeometry.LogTiltConcavity` was read for its full curvature decomposition; its log-concavity hypotheses are not transferred to a Maass trace. Those broad research modules were not imported.

1. **Conjecture:** adding a positive constant square gives a C² modular amplitude and an exact nonnegative-remainder curvature equation for the actual source. **Proved.**
2. **Conjecture:** the positive regulator's curvature defect can be removed after integration merely because it vanishes almost everywhere. **Fails in the exact local nodal profile.** This does not assert failure of any additional, unproved Maass-specific domination estimate.
3. **Pivot:** retain the full defect and top current in standard-area Green integration. **Proved.**
4. **Stronger positive survivor exposed by Lean:** the nodal curvature limit is classified on every oriented compact interval, including intervals ending at the node. **Proved.**

## Dependency-closed paper proof

Let `F_q` be the original finite congruence translates, `D=sum_q |F_q|²`, and `C_v=partial_v D`. For `e>0`, put `rho_e=sqrt(D+e²)`, `c_v=C_v/(2(D+e²))`, and

`R_{e,v}=sum_q |partial_v F_q-c_v F_q|² + e²*c_v²`.

The denominator is strictly positive even at common zeros. The original C² trace and modular invariance imply C² regularity and invariance of `rho_e`. Direct differentiation gives `partial_v rho_e=C_v/(2rho_e)`. Square completion, using `C_v=2*sum Re(conj(F_q)*partial_v F_q)`, gives

`R_{e,v}=E_v-C_v²/(4(D+e²)) >= 0`,

`E_v=(partial_v rho_e)²+R_{e,v}`.

Set `R_e=R_{e,1}+R_{e,i}`. Differentiating `rho_e²=D+e²` twice and substituting the already-proved actual trace equation `Delta D=2(E-lambda*D/y²)` yields

`rho_e*Delta rho_e=R_e-lambda*D/y²`.

The original quarter density therefore has the exact decomposition

`E-D/(4y²) = |grad rho_e|²-rho_e²/(4y²)+R_e+e²/(4y²)`.

The regularized first current is the original current divided by `2rho_e`. Translation identifies both side radii; inversion identifies both circular radii. Dividing the original matching-current identities by their common radii proves the new identities, with the full circular Jacobian.

On the truncated standard modular domain `Omega_Y`, `Y>=1`, C² regularity and compactness give integrability of the actual Laplacian. Both Fubini orders and FTC express its horizontal part by the circular boundary current and its vertical part by top minus circular current. The circular substitution and matching-current identities cancel the lower terms. Thus, with ordinary two-dimensional Lebesgue area,

`integral_{Omega_Y} Delta rho_e = integral_{-1/2}^{1/2} partial_y rho_e(x,Y) dx`.

The weighted source mass `D/(y²rho_e)` is continuous on the enclosing compact cell, hence integrable. The curvature equation then proves integrability of `R_e/rho_e` and gives

`integral_{Omega_Y} R_e/rho_e = top_e(Y) + lambda*integral_{Omega_Y} D/(y²rho_e)`.

In particular the right side is nonnegative. No top limit, quarter comparison, or regulator-limit interchange is used.

For the exact local real profile `h(x)=x`, let `r_e(x)=sqrt(x²+e²)` and `k_e(x)=e²/r_e(x)³`. Actual derivatives give

`r_e'=x/r_e`, `r_e''=k_e=(1-(r_e')²)/r_e`.

The curvature is continuous and interval integrable for each positive `e`. FTC proves

`integral_a^b k_e = b/r_e(b)-a/r_e(a)`.

As `e` tends to zero, each endpoint flux tends to `x/|x|`, with quotient zero at zero. Consequently

`lim integral_a^b k_e = b/|b|-a/|a|`.

At every nonzero `x`, the literal quotient `k_e(x)` tends to zero. The singleton node is Lebesgue-null, so convergence to zero holds almost everywhere. Nevertheless the integral on `[-1,1]` tends to two. Crossing the node retains its full curvature; an interval with the node as endpoint retains the corresponding half contribution. This local profile is not periodic, modular invariant, cuspidal, or a Maass eigenform.

## Lean files

- `formal/GaloisForLFunctions/RHTower/SelbergMaassTraceRegularized.lean`: actual C² radius, modular symmetry, square completion, curvature equation, and quarter-density correction.
- `formal/GaloisForLFunctions/RHTower/SelbergModularArcIntegration.lean`: shared reflection/circular integration lemmas, extracted from the previous area proof.
- `formal/GaloisForLFunctions/RHTower/SelbergModularPotentialGreen.lean`: C² scalar-potential Green theorem with explicit matching currents.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassRegularizedArea.lean`: actual boundary matching, standard-area curvature balance, all integrability, and weighted mass/flux nonnegativity.
- `formal/GaloisForLFunctions/RHTower/SelbergNodalCurvature.lean`: actual nodal derivatives, exact integral, all-endpoint classification, and almost-everywhere/integral-limit separation.
- Existing `SelbergMaassTraceArea.lean` now reuses the shared Green slice theorems. Its public statements and original source quarter identity are preserved; 142 duplicated proof lines were removed and 10 replacement lines added.

## Verification

- Complete scratch checks passed for the regularized trace, nodal curvature, shared arc geometry, generic Green identity, and actual regularized area. The changed original area module passed a direct source compatibility check.
- Six serialized final audits used `LEAN_NUM_THREADS=1 lake build <single-module>`. All passed, each rebuilding only its named target: arc geometry (4.2s), potential Green (3.6s), original trace area (3.7s), regularized trace (3.3s), regularized area (3.2s), nodal curvature (1.5s). No umbrella or full build ran.
- Logs: `/tmp/selberg_modular_arc_build.log`, `/tmp/selberg_potential_green_build.log`, `/tmp/selberg_trace_area_refactor_build.log`, `/tmp/selberg_trace_regularized_build.log`, `/tmp/selberg_regularized_area_build.log`, `/tmp/selberg_nodal_curvature_build.log`.
- All 88 public definitions/theorems across the six audited modules passed the scratch axiom audit, with only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. No added axioms or admissions. Scratch and results: `/tmp/selberg_regularized_axioms.lean`, `/tmp/selberg_regularized_axioms.log`, `/tmp/selberg_regularized_declarations.txt`.
- Five new modules are wired in `RHTower.lean`. The refreshed corpus returns all three queried capstones; `/tmp/selberg_regularized_corpus_audit.json` records that check. Tracked and new task-file whitespace checks passed.
- **Repository lint failed only on two unrelated, untracked, unwired HTGeometry modules: `FokasLenellsLeftJost` and `FokasLenellsScattering`.** No task-owned module is named in an error. Existing large-file warnings remain. Log: `/tmp/selberg_regularized_lint.log`. Those concurrent files were not modified.
- Every task-owned Lean/build handle is terminal. No task commit or push.

## Open continuation

A quarter estimate using this balance would require a quantitative lower bound for the retained weighted remainder relative to weighted mass and boundary cost. Nonnegativity alone supplies no factor of one quarter.

Next construct the actual augmented normalized source `(F_q,e)/rho_e`. Its additional coordinate should make the direction smooth through original nodes. Prove its derivative-energy identity and its precise weighted mean/chord defect before any transport estimate. The extra coordinate has weighted period mean `e*w`, not zero; it must be retained. Then test a source-built chord/capacity comparison, including its dependence on `e`, against the exact nodal concentration law. No uniform inverse-density resistance, regulator-limit exchange, congruence-uniform gap, or Bessel boundary positivity is assumed.
