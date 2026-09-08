# Cycle 33: actual regular curvature measure

Unconditional Selberg 1/4 goal remains ACTIVE and UNPROVED. This cycle made verified progress, not a blocked/no-progress turn. Do not mark complete or blocked. Continues `mem:selberg/actual-weak-curvature-2026-09-08`.

User rules: whole-corpus broad research with explicit --any (multiple unflagged terms mean AND), source-derived conjecture/proof/fail/pivot, no added axioms/admissions/numerical experiments. One task-owned foreground Lean invocation at a time, poll exact handles to terminal, never restart on timeout. Scratch/direct checks lake env lean <file>; needed oleans lake env lean -o ... <source>; final audit only LEAN_NUM_THREADS=1 lake build <single-module>. No full/umbrella builds; wire modules. Preserve shared edits; no task commits/pushes or killing others' processes.

## Authoritative artifacts

Parent: docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md. Cycle33 checked and cycle34 pending.
Stage3 full dependency-closed paper proof/audit: docs/drafts/pipeline/3-formalized/selberg-actual-curvature-measure.md.
Four modules in formal/GaloisForLFunctions/RHTower, all wired, indexed, built:

1. SelbergCompactTestApproximation.lean (84lines,2 declarations): exists_common_compact_approximation takes continuous phi with compact topological support in H={Im z>0}. Returns one compact K subset H containing original support and, for every eps>0, a C2 approximant psi supported in K with uniform norm error<=eps. Uses actual cutoff chi, B=norm of its bounded continuous map, globally smooth approximation to phi at eps/(B+1), then chi*g; no dimension-one polynomial approximation imported. exists_limit_of_eventual_approximation proves a scalar real limit along a nontrivial filter if at every positive error it is eventually uniformly close to a convergent family. Explicit metric Cauchy argument with eps/5 and four triangle terms, then real completeness.

2. SelbergUpperHalfPlaneCompactTests.lean (113lines,13 declarations): actual zero extension C_c(H,R)->(C->R), by positive-height guard and g(ofComplex z); continuous globally, compact supported in H. Support lies in coe-image original compact support. Positive/additive/scalar/order transport proved. restricted_compact and restrictCompact recover a C_c(H,R) from admissible planar test. zeroExtend_restrictCompact gives exact round trip. ofComplex_continuousOn proved through actual OpenPartialHomeomorph source=H. Names all under GaloisForLFunctions.RHTower.SelbergUpperHalfPlaneCompactTests.

3. SelbergMaassContinuousCurvature.lean (138lines,10 declarations): original source f:MaassCuspEigenform at principal congruence level N+1, ANY real lam. testedCurvature_sub, testedCurvature_cutoff_error, exists_testedCurvature_limit on every continuous compact planar test in H. Actual positive regulator integrals converge: choose common K approximants; smooth nonnegative eta=1 on K has J_e(eta)<M=J(eta)+1 eventually by cycle32; approximation error delta gives pairing error<=delta*J_e(eta). Taking delta=eps/M supplies generic Cauchy criterion. continuousCurvature defined by limUnder actual regulator integrals, with convergence proved, not default-valued assumed. continuousCurvature_limit, continuousCurvature_eq_weak on C2, nonneg, add, const_mul, mono.

4. SelbergMaassCurvatureMeasure.lean (123lines,15 declarations): compactFunctional and compactPositiveFunctional on actual C_c(UpperHalfPlane,R), applying continuousCurvature to zeroExtend. curvatureMeasure=RealRMK.rieszMeasure of this CONSTRUCTED positive linear map. Instances curvatureMeasure_regular and curvatureMeasure_finiteOnCompacts. compact_test_integrable, integral_compact_test, original_test_integrable, integral_original_continuous_test, integral_original_test. For every admissible planar C2 phi:
integral_H phi dmu=J(phi)=integral_C Delta(phi)*sqrt(D)+lam*integral_C phi*sqrt(D)/y².
testedCurvature_limit_integral: original regulator pairings of every actual compact continuous H-test converge to its mu-integral.
measure_compact_lt_top: finite on every compact.
curvatureMeasure_unique and existsUnique_curvatureMeasure: uniqueness among regular measures representing all actual continuous compact-test limits.
testedCurvature_error_le_integral retains exact error <=e*testBudget lam phi from cycle32.
No pointwise curvature-limit interchange; no assumed measure. No claim of total finiteness on all H or quotient/fundamental-domain identity.

## Verification complete

All full scratch proofs and needed direct source olean checks passed without new warnings. All40 public defs/theorems/named instances audited in /tmp/selberg_curvature_measure_axioms.lean, log /tmp/selberg_curvature_measure_axioms.log; list /tmp/selberg_curvature_measure_declarations.txt. Only propext, Classical.choice, Quot.sound. No added axioms or admissions.
All four wired into RHTower.lean; /tmp/selberg_curvature_measure_corpus_audit.json returns40 declarations/4modules. All task source/card/umbrella/new-file whitespace checks passed.
Serialized final target builds passed, rebuilding only target: compact approximation3.2s, compact tests13s, continuous curvature7.0s, measure10s. Logs /tmp/selberg_compact_test_approximation_build.log, /tmp/selberg_upper_half_plane_compact_tests_build.log, /tmp/selberg_maass_continuous_curvature_build.log, /tmp/selberg_maass_curvature_measure_build.log. Cached informational EvenL2LogUnitary output is not a target failure.
Repository lint FAILED only for unrelated unwired RHTower.FokasLenellsHardyOrientation, plus existing large-file warnings; complete stdout/stderr captured in /tmp/selberg_curvature_measure_lint.log. No Selberg lint error; do not call global lint passing. No task edits to that module.
ALL task-owned Lean/build handles terminal, none to resume. Final filtered process inventory found NO Lean or Lake executable (/tmp/selberg_curvature_measure_processes.log). No task commit/push/numerical experiment.

## Corpus discovery/read mechanisms

Explicit --any full index queries: positive distribution/representing measure/vague convergence/smooth approximation/local mass/order zero432decl241mods; positive extension/Krein/Kantorovich/common support/compact approximation/uniformApproximation2199decl250mods; Cauchy filter/uniform approximation/approximation independence/positive measure230decl120mods; zero extension/zeroExtend/compact support transport/open embedding/positive functional282decl112mods. Logs /tmp/selberg_measure_discovery33.json, /tmp/selberg_positive_extension_discovery33.json, /tmp/selberg_cauchy_extension_discovery33.json, /tmp/selberg_zero_extension_discovery33.json. Counts are coverage, not reading all hits.
Read SchwartzCompactPositiveFunctional for extension mechanism, PolynomialSmoothApproximation for source contrast (one-dimensional), actual mathlib BumpFunction/SmoothApprox, metric Cauchy/complete filters, CompactlySupported/Bounded norm support, UpperHalfPlane/Topology and OpenPartialHomeomorph, RMK/Real measure representation/uniqueness. StokesOpenExtensionByZero is a sheaf construction, not imported as a function-extension result.

## Next mathematical work: cycle34

Actual measure transport under SL2Z and quotient budget with seam concentration retained. radius_invariant already verified in SelbergMaassTraceRegularized lines70ff; density_invariant source follows original finite congruence trace. Conjecture derive invariance of mu by literal change of variables in compact source tests, preserving original operator and hyperbolic weights. A broad --any query modular invariance/curvature measure/boundary charge/seam crossing/coarea/transport reached8003decl2109mods, results /tmp/selberg_measure_transport_discovery34.json. Most leading results are finite coarea laws; inspect candidate proof mechanisms before transfer, do not assume their source conditions.

Vague convergence on compact continuous tests DOES NOT by itself justify indicator/fundamental-domain mass passage. Need boundary concentration and stabilizer multiplicities/weights. Source seam nullity not proved. Existing SelbergNodalCurvature exact endpoint classification shows retained nodal charge but is a local toy, not an actual Maass seam classification. Quotient measure/transport not yet proved.

Essential ultimate gap: source-derived quarter lower comparison with actual congruence transport/spatial geometry, full compact core and cusp/Bessel boundary costs. The new measure permits spatial estimates but positivity and compact finiteness alone do not establish quarter. Continue wide corpus-driven conjecture/proof/fail/pivot loops, not just ready theorem searches. Goal remains active.

## Lean pitfalls verified here

Need open scoped CompactlySupported for C_c notation. C2 <= infinity coercion works with WithTop.coe_le_coe.mpr le_top; bare simp/norm_num/exact_mod_cast can fail. Continuous.const_mul exists; ContDiff.const_mul does not in this toolchain (use contDiff_const.mul hp). continuousCurvature_add needed explicit change of hleft to the literal pointwise sum lambda before simp of testedCurvature_add. In zero-extension local continuity, change membership hz to 0<z.im and spell out guarded function before rw if_pos; raw simp can fail because compact map/coercion wrappers. ofComplex.source is not definitionally range coe: rewrite generated Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target and UpperHalfPlane.range_coe. All these are fixed in checked tree.
