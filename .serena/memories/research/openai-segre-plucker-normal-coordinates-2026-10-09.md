# OpenAI source applications: native Segre and Plucker normal coordinates

Source remains proven OpenAI/math StableCoordinate at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; upstream HEAD rechecked equal. Scope: all 16 live routes and 23 route candidates, no Weil priority. Overall application goal remains active.

Completed six new HTGeometry leaves, 24 new theorems, 40 public declarations. Final `lake --old env lean <leaf>` checks passed with empty logs; every public declaration axiom-audited via `/tmp/paper-segre-plucker-axioms.lean`, only propext/Classical.choice/Quot.sound. Six modules wired exactly once into HTGeometry.lean; no umbrella/full build. Exact corpus searchback found all 40 declarations. Evidence: tmp/hgt-openai-math/segre-plucker-{audits,manifest,searchback-audit}.json. Global lint reports only foreign unwired HTGeometry.QKrawtchoukCompanionTriangular; do not edit that foreign module.

Files and content:
- PaperHomogeneousGeneratorIdeal.lean: span of any homogeneous positive-degree generator family, source weight-order bound and fully paid normal-presentation builder.
- PaperSegreNormalRelations.lean: native pair products X(inl i)*X(inr j), ideal equals product of the two coordinate-block ideals. Native segreDiagonalPresentation sends X(i,j) to single(segrePairExponent)1; segreToBiprojective sends it to the actual pair product. Segre evaluation and normal map have identical kernels over every CommRing K and all m,n.
- PaperSegreNormalEmbedding.lean: paperSegreNormalEmbedding injects EXISTING SegreDiagonalRing into ACTUAL PaperIdealAssociatedGraded of the product ideal. Native presentation descent via RingHom.liftOfSurjective, presentation formula, injectivity and actual coordinate initial-class formula. This is a coordinate-ring injection; do not claim a scheme embedding in the same direction.
- PaperNativeReesInitialLinearMap.lean: degree-n initial-class linear map on I^n; kernel exactly next-power membership I^(n+1). Uses actual native monomial and source specialization.
- PaperPluckerNormalRelations.lean: universal native Nieto1810.decomposableBivector on two polynomial rows over arbitrary CommRing and arbitrary index type. Fully paid ideal/presentation, exact scalar relation preservation, original generator-ring embedding, actual initial-coordinate formula, repeated-index zero, antisymmetry and Plucker quadrics.
- PaperPluckerNormalRowAction.lean: arbitrary 2x2 polynomial matrices transform native bivector generators by determinant, preserve their ideal and scale actual initial classes by determinant. Every polynomial Matrix.SpecialLinearGroup (Fin 2) fixes these normal coordinates. No added mathematical assumptions.

Lean details:
- Native decomposableBivector_swap u v i j concludes b j i = -b i j. Wrong call orientation caused costly failed elaboration. Direct equality transport via congrArg and map_add is checked and small.
- Polynomial scalar SMul typeclass search on the quotient exceeded default limits. Row-action leaf caches canonical Module AND SMul structures with private generic abbrevs and local instances. Local SMul cache is necessary in addition to Module. No heartbeat/recursion increases.
- RingHom.liftOfSurjective takes a subtype containing map and kernel inclusion; composition formula is liftOfSurjective_comp_apply.
- Ideal.span_mul_span uses pointwise set product in this toolchain.

Tracker completed_modules reconciled with coface/full-Veronese/normal-relations manifests. Stable totals: 117 source leaves +76 application leaves=193 modules, 2184 audited public declarations. Exact owned inventory: 519 modules, 4408 public theorem/lemma results. Initial audit counted 518 because new PaperSegreNormalEmbedding was omitted from own-files registration; registration and candidate owned_files corrected, complete ownership coverage asserted, final audit regenerated. All six mathematical leaf and axiom checks were already valid.

Next receivers: native symmetric-square representation, further homogeneous matrix/incidence coordinate algebras and other source mechanisms across all routes. Search direct Lean via scripts/formal_tools.py research before new math; no cards. Preserve foreign work, one foreground Lean process at a time, leaf audits only, no full builds.