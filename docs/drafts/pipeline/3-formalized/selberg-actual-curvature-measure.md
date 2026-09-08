# Actual Maass curvature measure from original regulator integrals

- **ID:** selberg-curvature-measure-33
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Selberg conjecturing loop, cycle 33](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Statement:** The original finite congruence trace determines a unique regular measure on the upper half-plane representing its actual continuous compact-test regulator limits. The measure is finite on compact sets, recovers the original C² weak-curvature formula, and retains its quantitative regulator error.

## Scope

The source is the original Maass cusp eigenform at principal congruence level N+1, for every real eigenvalue lambda. All convergence, positivity, and source regularity are proved from that source. No representing measure, uniform regulator estimate, smooth extension outside the upper half-plane, or pointwise curvature-limit interchange is assumed.

The measure is constructed on the upper half-plane. This does not yet identify a quotient measure, its fundamental-domain mass, modular invariance of the limiting measure, or the quarter lower bound. Compact-set finiteness is not total finiteness on the whole upper half-plane.

## Corpus-derived proof loop

Every broad discovery search used the whole corpus index with explicit --any. Unflagged multiple terms mean AND. Counts describe index coverage, not claims to have read every match.

- Positive distribution, representing measure, vague convergence, smooth approximation, local mass, order zero: 432 declarations in 241 modules.
- Positive extension, Krein, Kantorovich, common support, compact approximation, uniformApproximation: 2199 declarations in 250 modules.
- Cauchy filter, uniform approximation, approximation independence, positive measure: 230 declarations in 120 modules.
- Zero extension, zeroExtend, compact support transport, open embedding, positive functional: 282 declarations in 112 modules.

Logs: /tmp/selberg_measure_discovery33.json, /tmp/selberg_positive_extension_discovery33.json, /tmp/selberg_cauchy_extension_discovery33.json, /tmp/selberg_zero_extension_discovery33.json.

SchwartzCompactPositiveFunctional was read for common-support approximation and positive extension. Its one-dimensional polynomial approximation does not supply the planar source theorem. PolynomialSmoothApproximation was inspected for the approximation mechanism; the present planar construction instead uses the current mathlib global smooth-approximation theorem for uniformly continuous functions, multiplied by an actual positive-height cutoff. The metric Cauchy criterion and completeness of the real numbers give the needed scalar limit without importing a hypothetical extension. The upper-half-plane open partial homeomorphism and compact-image theorems supply zero extension and restriction. StokesOpenExtensionByZero was inspected but concerns sheaves, so it is not imported or treated as a function-extension theorem. Current mathlib Riesz--Markov is applied only after the actual positive linear map on compact continuous upper-half-plane tests has been constructed.

1. Conjecture: every original continuous compact planar test at positive height has uniformly accurate C² approximants in one common compact set. Proved with an explicit cutoff and rescaled approximation tolerance.
2. Conjecture: positivity bounds approximation error uniformly for small regulators, so the original continuous-test integrals converge. Proved by a complete four-term Cauchy argument.
3. Strengthening: the actual limits are positive, real linear, monotone, and agree with the original C² formula. Proved directly from original regulator integrals and uniqueness of limits.
4. Conjecture: these source limits determine an actual regular measure on the upper half-plane. Proved after constructing continuous compact zero extension, restriction, and exact round-trip recovery. Uniqueness holds among regular measures representing every continuous compact-test limit.
5. Strengthening: the exact C² regulator error remains an error estimate against integration over this measure. Proved.

## Dependency-closed paper proof

Let H be the open upper half-plane. Write D for the actual finite trace density, a=sqrt(D), rho_e=sqrt(D+e²), and R_e for the full nonnegative retained curvature. The cycle-32 theorem proves, for every real C² compact test psi supported in H,

J_e(psi)=integral_C psi*R_e/rho_e -> J(psi),
J(psi)=integral_C Delta(psi)*a + lambda*integral_C psi*a/y²,
|J_e(psi)-J(psi)| <= e*B_lambda(psi),
B_lambda(psi)=integral_C |Delta psi| + |lambda|/2*integral_C |psi|/y².

These are genuine integrals. The positive-regulator filter is the nontrivial filter proved in cycle 31.

First let phi be merely continuous with compact support in H. Construct a compact C² cutoff chi equal to one on its support, supported in H. Its bounded-continuous-function norm B is finite and nonnegative. Compact support makes phi uniformly continuous, so the smooth-approximation theorem gives a smooth g with uniform error less than epsilon/(B+1). Put psi=chi*g. Since chi*phi=phi everywhere, including outside the original support,

|psi-phi| = |chi|*|g-phi| <= B*epsilon/(B+1) <= epsilon.

Every psi has support in the one fixed compact K=support(chi) union support(phi), contained in H. This K is chosen before epsilon. The approximants have C² regularity, and their compact support follows from K.

Choose a second nonnegative C² compact cutoff eta equal to one on K, still supported in H. Its actual regularized curvature values converge to the nonnegative J(eta), so J_e(eta)<M=J(eta)+1 for every sufficiently small positive regulator. In particular M>0.

If phi and psi are supported in K and |phi-psi|<=delta, positivity of the literal regularized curvature gives

|J_e(phi)-J_e(psi)| <= delta*J_e(eta).

Both tested integrals are genuinely integrable by actual source continuity and compact support. At every requested epsilon>0 choose the common-compact approximation with delta=epsilon/M. The last bound is eventually at most epsilon. Since J_e(psi) converges by the C² theorem, J_e(phi) is eventually uniformly approximated, at every positive accuracy, by a convergent scalar family.

For completeness, the scalar Cauchy argument is formalized explicitly. Given tolerance epsilon, approximate a family u_i by a convergent family v_i with eventual error at most delta=epsilon/5. Eventually v_i is within delta of its limit b. Thus, for two sufficiently late indices,

dist(u_i,u_j) <= dist(u_i,v_i)+dist(v_i,b)+dist(b,v_j)+dist(v_j,u_j) < 4*delta < epsilon.

The image of that eventual index set belongs to the original mapped nontrivial filter. It therefore is a Cauchy filter. Completeness of the real numbers constructs its limit. Applied to the actual J_e(phi), this constructs continuousCurvature(phi); convergence is proved, rather than relying on a default value of limUnder.

The actual integrals are additive and commute with real scalars on the admissible test space. Uniqueness of limits transfers these identities to continuousCurvature. Original nonnegative curvature transfers positivity and test ordering. On C² tests the limit is exactly the previous J by uniqueness.

Now let g be an actual compact continuous function on H. Extend it by zero to C: at positive height use g(ofComplex z), and elsewhere use zero. Its support lies in the image under the inclusion H->C of the original compact support. That image is compact, closed, and contained in H. The open partial inverse of the inclusion is continuous on H, so the zero extension is continuous there. Compact localization then proves global continuity, including at the boundary of H. The extension is thus an admissible planar compact continuous test. It respects addition, real scalar multiplication, and pointwise ordering.

Consequently L(g)=continuousCurvature(zeroExtend(g)) is an actual positive real linear map on C_c(H,R). Apply the current mathlib real Riesz--Markov theorem to this constructed map. It defines a regular measure mu, finite on compact subsets, such that

integral_H g dmu = L(g).

Every compact continuous test is genuinely integrable for mu. Any regular measure with these same compact-test integrals equals mu by the proved measure uniqueness theorem.

Conversely, an admissible planar continuous test phi restricts to a compact continuous test on H. Its restricted support is contained in the compact image of its planar support under the locally continuous partial inverse of H->C. Zero extension of the restriction recovers phi exactly, using phi=0 off its topological support. Hence

integral_H phi dmu = continuousCurvature(phi).

In particular every admissible C² test satisfies the original source equation

integral_H phi dmu = integral_C Delta(phi)*sqrt(D)
                  + lambda*integral_C phi*sqrt(D)/y²,

and its quantitative error is

|J_e(phi)-integral_H phi dmu| <= e*B_lambda(phi).

For every compact continuous g on H, the original J_e(zeroExtend(g)) converges to integral_H g dmu. Thus the representing measure is tied to the original regularized curvature through actual continuous test integrals. No spatial concentration was discarded by taking a pointwise limit.

## Lean and verification

Four modules are complete: SelbergCompactTestApproximation (2 declarations), SelbergUpperHalfPlaneCompactTests (13), SelbergMaassContinuousCurvature (10), and SelbergMaassCurvatureMeasure (15). All complete scratch proofs and all needed source olean-producing checks passed without warnings.

All 40 public declarations, including both named measure instances, passed the scratch axiom audit. Only propext, Classical.choice, and Quot.sound occur; no added axioms or admissions. Full declaration list and audit: /tmp/selberg_curvature_measure_declarations.txt, /tmp/selberg_curvature_measure_axioms.lean, /tmp/selberg_curvature_measure_axioms.log.

All four modules are wired into RHTower.lean. The refreshed full-corpus index returns all 40 declarations across the four modules (/tmp/selberg_curvature_measure_corpus_audit.json). Task-source, new-file, card, and umbrella whitespace checks passed.

All four serialized final LEAN_NUM_THREADS=1 lake build <single-module> audits passed. Each rebuilt only its named target: compact approximation 3.2s, upper-half-plane compact tests 13s, continuous curvature 7.0s, curvature measure 10s. Logs: /tmp/selberg_compact_test_approximation_build.log, /tmp/selberg_upper_half_plane_compact_tests_build.log, /tmp/selberg_maass_continuous_curvature_build.log, and /tmp/selberg_maass_curvature_measure_build.log. Cached informational output from EvenL2LogUnitary was replayed; no new task-module warning or error occurred. No full or umbrella build ran.

Repository lint exited 1 only for the unrelated, unwired RHTower.FokasLenellsHardyOrientation module, with existing large-file warnings (/tmp/selberg_curvature_measure_lint.log). This task did not modify that file. No Selberg lint error was emitted; repository lint as a whole did not pass.

All task-owned Lean/build handles are terminal. The final filtered process inventory found no Lean or Lake executable (/tmp/selberg_curvature_measure_processes.log). No numerical experiment, task commit, or task push was performed.

## Remaining source gap and next conjecture

The next geometric conjecture is modular invariance of this actual measure, derived from original amplitude invariance and change of variables in compact source tests. The checked radius_invariant theorem is available in SelbergMaassTraceRegularized. A new broad modular-invariance/curvature-measure/boundary-charge/seam-crossing/coarea/transport query reached 8003 declarations in 2109 modules (/tmp/selberg_measure_transport_discovery34.json); this is discovery for the next cycle, not a proof or a claim to have read every hit.

Vague convergence on compact continuous tests does not itself justify passing to the indicator of a chosen fundamental domain. Boundary charge and stabilizer weights must be handled when deriving the quotient budget. The already formalized nodal profile retains nonzero curvature under regularization, so its concentration cannot be silently discarded at seams. No vanishing claim for actual Maass curvature on those seams is made here.

The source-derived quarter comparison remains unproved. The measure now permits spatial curvature and transport estimates, but positivity and compact finiteness alone do not supply a quarter lower bound. Keep original core and cusp/Bessel boundary contributions in the next conjecture/proof/fail/pivot loop. Selberg's unconditional goal stays active.
