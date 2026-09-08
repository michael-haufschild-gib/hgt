# Actual Maass weak curvature and compact order-zero control

- **ID:** selberg-weak-curvature-32
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 32](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** The actual finite congruence trace has a positive real linear weak-curvature functional on compact C² tests, with explicit regulator error and a finite order-zero bound on every compact subset of the upper half-plane.

## Scope

The source is the original Maass cusp eigenform for principal congruence level N+1. The local results hold for every real eigenvalue lambda. They do not assume an exceptional range, added automorphic lifts, a hypothetical measure, or any new source estimate. Test regularity and support restrictions specify the test space; all source continuity, integral convergence, and regulator-limit properties are proved from existing actual source theorems.

This does not prove Selberg's quarter lower bound. It identifies the spatial limiting curvature on tests, including any nodal concentration. It does not identify this with an integral of a pointwise curvature limit, or construct a representing measure.

## Corpus-derived conjecturing loop

All discovery searches used the full corpus index with explicit --any. Multiple unflagged terms mean AND. Counts are index coverage, not claims to have read every matching declaration.

- localGreen, compactSupport, weakDerivative, weakLaplacian, positiveDistribution, Kato, nodal: 530 declarations in 95 modules.
- support, localization, patching, product, continuity: 26054 declarations in 7965 modules.
- Positive distribution, positive functional, Riesz representation, compact test, local measure: 182 declarations in 44 modules.
- Order zero, cutoff mass, positive linear, domination: 1088 declarations in 533 modules.
- Smooth cutoff, compact neighborhood, order zero, bump function: 380 declarations in 217 modules.

Logs: /tmp/selberg_weak_curvature_discovery32.json, /tmp/selberg_local_products_wide32.json, /tmp/selberg_positive_weak_functional_discovery32.json, /tmp/selberg_cutoff_domination_discovery32.json, /tmp/selberg_compact_cutoff_discovery32.json.

Read mechanisms included ComplexLaplacianGreenIdentity's twice-directional Green proof, JumpFormAdjointness's genuine product integrability, SchwartzCompactDiagonalOrderZero's nonnegative cutoff envelopes, SchwartzCompactPositiveFunctional's positive extension mechanism, and CompactSmoothCutoff's constructed smooth cutoff on an arbitrary planar compact inside an open set. The chart Green/test modules were inspected for support and seam handling. This construction needs only C² local source regularity, so no stronger global smoothness from other source types was transferred.

1. Conjecture: two local Green integrations identify the actual compact-test curvature. Proved with local C² source regularity; no global extension regularity is assumed.
2. Conjecture: the scalar regulator errors imply a quantitative weak-curvature limit. Proved with the stronger absolute-eigenvalue error, valid for every real lambda.
3. Strengthening: positivity of actual regularized curvature gives positivity, linearity, monotonicity, and test domination of its actual limit. Proved.
4. New conjecture from the cutoff-envelope search: every compact set has a single finite constant controlling all supported tests by their uniform size, with no derivatives of those tests in the bound. Proved by constructing a nonnegative cutoff and using its actual curvature value. Compact support and integrability of each dominated test are discharged internally.

The failures during implementation concerned precise Lean norm rewriting and the current regularity-order coercion from infinity to order two. They do not constitute mathematical counterexamples or retired mathematical routes.

## Dependency-closed paper proof

Write H={z in C : Im z>0}, D for the actual finite congruence trace density, a=sqrt(D), and rho_e=sqrt(D+e²), where e>0. Original source regularity gives D and rho_e class C² on H. Original retained curvature R_e is nonnegative and satisfies, on H,

R_e/rho_e = Delta rho_e + lambda*D/(y²*rho_e).

Let phi be real C² on C with compact topological support contained in H. If G is continuous on H, then phi*G has compact support contained in H, is continuous there, and vanishes off that support. The support-extension continuity theorem makes it globally continuous, so it is genuinely integrable. This also applies to |phi| and to each first and second directional derivative of phi, whose topological supports lie in that of phi.

Apply the scalar directional integration-by-parts theorem twice in directions 1 and i. Each derivative/source product is integrable by the preceding paragraph. The source need only be differentiable on the other factor's support, which lies in H. Summing the two directional identities yields

integral phi*Delta rho_e = integral Delta phi*rho_e.

The source equation therefore identifies the literal tested retained curvature as

J_e(phi) = integral phi*R_e/rho_e
         = integral Delta phi*rho_e + lambda*integral phi*D/(y²*rho_e).

Both terms in

J(phi) = integral Delta phi*a + lambda*integral phi*a/y²

are integrable by actual amplitude continuity on H and compact support of the test and its Laplacian.

The scalar cycle-31 estimates, including d=0, give

0 <= rho_e-a <= e,
0 <= a-D/rho_e <= e/2.

Multiplying by the absolute tests, dividing the second bound by y², and using the integral norm inequality gives

|J_e(phi)-J(phi)| <= e*B_lambda(phi),
B_lambda(phi) = integral |Delta phi| + |lambda|/2*integral |phi|/y².

This is a finite constant for each admissible test. Every integral difference is justified by the proved integrability of its terms. The positive-regulator filter is the actual nontrivial filter constructed in cycle 31. The estimate proves J_e(phi) tends to J(phi) as e tends to zero through positive values.

For phi>=0, J_e(phi)>=0 by the literal nonnegative source curvature. Closedness of the nonnegative ray gives J(phi)>=0. Additivity and real scalar multiplication of the actual integrals pass to the unique limit, so J is real linear on the admissible test space. Similarly, pointwise ordering of two tests implies ordering of their limiting values.

More strongly, if |phi|<=c*psi for admissible tests, positivity of R_e/rho_e gives

|J_e(phi)| <= c*J_e(psi).

Both sides have proved limits; hence |J(phi)|<=c*J(psi). In particular, if chi is a nonnegative admissible cutoff equal to one on the support of phi and |phi|<=c with c>=0, then |J(phi)|<=c*J(chi).

Finally let K be any compact subset of H. CompactSmoothCutoff constructs a smooth compact chi_0 supported in H, equal to one on a neighborhood of K. Put chi=chi_0². This is a nonnegative C² compact test, remains supported in H, and equals one on K. Define C_K=J(chi), which is a finite real number and nonnegative by proved positivity. For every real C² phi with topological support contained in K, compactness of K itself proves compact support of phi. For every c>=0 with |phi|<=c,

|J(phi)| <= c*C_K.

Thus the source functional has local order zero: a fixed compact set admits one bound depending only on the source and that set, without derivatives of the varying test in the bound. No representing measure is used to obtain it.

## Lean and verification

SelbergLocalTestGreen contains 14 declarations: local product continuity/integrability, quantitative pairing error, support-preserving directional derivatives, two local Green identities, and the actual nonnegative compact cutoff. SelbergMaassWeakCurvature contains 40 declarations: original amplitude and curvature weights, integrability, the exact tested source identity, quantitative error and limit, positivity, linearity, monotonicity, domination, and the constructed compact order-zero bound.

Both complete scratch proofs and both needed olean-producing source checks passed without warnings. All 54 public declarations passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. No added axioms or admissions. Complete declaration and audit records: /tmp/selberg_weak_curvature_declarations.txt, /tmp/selberg_weak_curvature_axioms.lean, /tmp/selberg_weak_curvature_axioms.log.

Both modules are wired into RHTower.lean. The refreshed corpus indexes all 54 declarations in both modules, including the error, positivity, cutoff construction, and compact order-zero capstones (/tmp/selberg_weak_curvature_corpus_audit.json). Task-source, parent-card, new-card, and umbrella whitespace checks passed, including an explicit check of new files.

Both serialized final LEAN_NUM_THREADS=1 lake build <single-module> audits passed. Each rebuilt only its named target: SelbergLocalTestGreen (5.9s) and SelbergMaassWeakCurvature (9.6s). Logs: /tmp/selberg_local_test_green_build.log and /tmp/selberg_maass_weak_curvature_build.log. Cached informational output from EvenL2LogUnitary was replayed; no new task-module warning or error occurred. No full or umbrella build ran.

Repository lint exited 1 solely for four unrelated modules unreachable from the HTGeometry umbrella: FokasLenellsOrbitDecay, FokasLenellsOrbitEntries, FokasLenellsOscillatoryOrbit, and FokasLenellsScatteringDecay. Existing large-file warnings were also emitted. The stderr error list is recorded explicitly in /tmp/selberg_weak_curvature_lint.log. Those files were not modified by this task. No Selberg lint error was emitted; repository lint as a whole did not pass.

All task-owned Lean/build handles are terminal. The final process inspection found no Lean or Lake process (/tmp/selberg_weak_curvature_processes.log). No commit or push was made by this task.

## Remaining source gap

The next analytic construction is an actual positive representing measure on the upper half-plane, extending this functional from smooth compact tests to continuous compact tests. Uniform approximation must preserve a common compact support, use the proved order-zero bound, and retain the actual source pairing. That construction is not yet claimed.

The essential Selberg gap is still a source-derived quarter lower comparison involving actual congruence transport, compact core, and cusp/Bessel boundary contributions. Positivity and order-zero control alone do not supply it. Continue wide corpus discovery and conjecture/proof/fail/pivot work on those arithmetic and geometric inputs. The main goal stays active and unproved.
