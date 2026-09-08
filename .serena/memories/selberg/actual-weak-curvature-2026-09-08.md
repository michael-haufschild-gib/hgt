# Cycle 32: actual weak curvature and compact order-zero bound

Main unconditional Selberg 1/4 goal is ACTIVE and UNPROVED. This cycle made verified mathematical progress; do not mark goal complete or blocked. Continues `mem:selberg/quantitative-regulator-curvature-limit-2026-09-08`.

User requires wide corpus discovery with explicit --any (multiple unflagged terms mean AND), source-derived conjecture/proof/fail/pivot loops, no numerical experiments or added axioms/admissions. One task-owned foreground Lean process at a time; poll exact handles to terminal, never restart on an observation timeout. Use lake env lean <file> for scratch/direct needed oleans; final audit only LEAN_NUM_THREADS=1 lake build <single-module>; no full or umbrella builds. Preserve shared edits and do not commit/push or kill others' processes.

## Checked modules

formal/GaloisForLFunctions/RHTower/SelbergLocalTestGreen.lean: 14 declarations. Real functions on C, local source continuity/C2 only on H={Im z>0}; compact tests supported in H make actual products globally continuous/integrable. Norm pairing error helper, derivative support control, twice-directional Green identity, actual planar Green identity, constructed nonnegative C2 cutoff on every compact K subset H. Reuses HTGeometry.CompactSmoothCutoff.exists_smooth_cutoff then squares its cutoff. That theorem omits nonnegativity from its output, so square it rather than assume a range property. Current regularity order coercion hp.of_le (WithTop.coe_le_coe.mpr le_top) works; exact_mod_cast and norm_num alone failed on 2<=infinity.

formal/GaloisForLFunctions/RHTower/SelbergMaassWeakCurvature.lean: 40 declarations, namespace GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature. Source f is the original MaassCuspEigenform for principal congruence level N+1, ANY real lam. a=sqrt(D), radius rho_e=sqrt(D+e²), curvatureWeight=R_e/rho_e, massWeight=D/(y² rho_e), amplitudeWeight=a/y². All continuity/integrability is proved from original source.

For every real C2 compact test phi supported in H,
J_e(phi)=integral phi*R_e/rho_e
=integral Delta(phi)*rho_e +lam*integral phi*D/(y² rho_e).
weakCurvature J(phi)=integral Delta(phi)*a +lam*integral phi*a/y².
|J_e(phi)-J(phi)| <= e*(integral |Delta phi| + |lam|/2*integral |phi|/y²).
The actual nontrivial positive regulator filter from cycle31 gives testedCurvature_limit. weakCurvature_nonneg proves positivity on nonnegative tests, with actual additivity, scalar multiplication, monotonicity and test domination.
weakCurvature_norm_le: |phi|<=c*psi implies |J(phi)|<=c*J(psi).
weakCurvature_cutoff_bound specializes to a nonnegative cutoff equal one on support phi.
exists_compact_order_zero_bound: for every compact K subset H, exists finite C_K>=0 bounding |J(phi)|<=c*C_K for every C2 phi supported in K with |phi|<=c and c>=0. Cutoff is constructed; compact support of phi follows from K internally. No representing measure is assumed or constructed; no pointwise curvature-limit interchange. This retains any nodal concentration on actual tests.

## Source discovery

All searches explicit --any over full index. localGreen/compactSupport/weakDerivative/weakLaplacian/positiveDistribution/Kato/nodal: 530 declarations,95 modules. support/localization/patching/product/continuity:26054,7965. positive distributions/functionals/Riesz/compact tests/local measure:182,44. order-zero/cutoff-mass/positive-linear/domination:1088,533. smooth-cutoff/compact-neighborhood/order-zero/bump-function:380,217. Counts describe index coverage, not reading every result.
Read mechanisms: local Green twice IBP (ComplexLaplacianGreenIdentity and mathlib scalar FDeriv IBP), JumpFormAdjointness product integrability, SchwartzCompactDiagonalOrderZero cutoff envelopes, SchwartzCompactPositiveFunctional positive extension, CompactSmoothCutoff actual planar compact cutoff. Inspected chart Green/test modules for support/seams. No unrelated source hypotheses were transferred.

## Verification, all finished

Both full scratch proofs passed, including final cutoff and compact order-zero theorem. Both needed source olean checks passed. All 54 public declarations audited in /tmp/selberg_weak_curvature_axioms.lean, output /tmp/selberg_weak_curvature_axioms.log, full name list /tmp/selberg_weak_curvature_declarations.txt. Every declaration depends only on propext, Classical.choice, Quot.sound.
Both modules wired in RHTower.lean and indexed: /tmp/selberg_weak_curvature_corpus_audit.json returns all54. Serialized final targets passed and rebuilt only named target: local Green5.9s, actual weak curvature9.6s. Logs /tmp/selberg_local_test_green_build.log and /tmp/selberg_maass_weak_curvature_build.log. Cached informational EvenL2LogUnitary output is not a new failure. No full or umbrella build.
Repository lint FAILED only for unrelated HTGeometry.FokasLenellsOrbitDecay, FokasLenellsOrbitEntries, FokasLenellsOscillatoryOrbit, FokasLenellsScatteringDecay unreachable from their umbrella. Large-file warnings existed. /tmp/selberg_weak_curvature_lint.log explicitly records transcribed stderr errors (initial stdout redirection did not capture stderr). No Selberg error. Do not call repository lint passing.
Task-source/card/umbrella whitespace passed, including explicit new-file check. All task-owned Lean/build handles TERMINAL; no live process to resume. Final filtered process inventory found no Lean or Lake executable (/tmp/selberg_weak_curvature_processes.log). No task commit/push.

## Durable cards and next work

Parent docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md: cycle32 checked with exact proof, source discovery, and audit; cycle33 pending. Stage3 dependency-closed paper proof: docs/drafts/pipeline/3-formalized/selberg-actual-weak-curvature.md.

Next analytic conjecture: construct actual positive representing measure on H through common-compact smooth approximation and this source-derived order-zero estimate. SchwartzCompactPositiveFunctional supplies mechanism but is one-dimensional Schwartz; do not import its space/source assumptions into planar Maass tests. Need approximation independence, positivity, genuine integrals, original pairing recovery.
Essential ultimate gap remains source-derived quarter lower comparison with actual congruence transport, compact core and retained cusp/Bessel boundary costs. Positive weak curvature/order-zero alone do not supply it. Continue wide source discovery and actual conjecture/proof/fail/pivot work, not searches for a ready Selberg theorem. No goal status update is warranted.
