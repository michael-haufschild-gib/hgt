# OpenAI source applications: native symmetric-pair and symmetric-square normal coordinates

Verified 2026-10-09. Scope remains ALL 16 live routes + 23 candidates, no Weil priority. Current changed ledger reread directly; no cards. OpenAI/math HEAD rechecked fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Source results are PROVEN, not conjectures.

Evidence: tmp/hgt-openai-math/symmetric-normal-audits.json, symmetric-normal-manifest.json, symmetric-normal-searchback-audit.json. Tracker stable-coordinate-native-port.json. Prior verified batch segre-plucker-audits.json (`mem:research/openai-segre-plucker-normal-coordinates-2026-10-09`).

Batch: 8 new modules, 45 public theorems, 64 audited public declarations. All final `lake --old env lean <leaf>` runs passed with EMPTY logs; no full or umbrella build. All public declarations printed in /tmp/paper-symmetric-normal-axioms.lean and use only propext/Classical.choice/Quot.sound. Fresh library objects, exact corpus searchback, each owned leaf wired once, no objects in source tree. Nine owned scratch/helper files removed; final axiom probe retained; all owned processes terminal.

Cumulative owned: 527 modules / 4453 public theorem+lemma results. StableCoordinate family: 117 source leaves + 84 application leaves = 201 completed modules, 2248 audited public declarations. Source inventory 118 includes import-only All.lean; do NOT count it as a ported leaf. Every completed manifest module explicitly checked against normalized/deduplicated own-files.txt.

All files under formal/GaloisForLFunctions/HTGeometry/:
- PaperMonicLeadingSubstitution: any monomial order, arbitrary CommRing. Monic generators plus injective leading-exponent substitution give injective polynomial substitution. Proof uses unique maximal monic term, no domain hypothesis.
- PaperSymmetricPairGenerators: existing symmetricPair evaluated on [X0,X1],[X2,X3]. Native generators ac, ad+bc, bd have lex leading monomials ac, ad, bd. Their exponent map is injective, giving polynomial independence over EVERY CommRing, including zero divisors.
- PaperSymmetricPairNormalSpace: actual generator ideal and fully paid source normal-presentation data. Actual initial-class polynomial map is injective, with exact native sigma/mono generator formula.
- PaperNativeReesHomogeneousInitial: generic homogeneous evaluation lies in matching ideal power; native Rees specialization is exactly its initial class. Methods on PaperHomogeneousNormalPresentationData: homogeneous_evaluation_mem and polynomialMap_homogeneous.
- PaperSymmetricDiscriminant: binary discriminant c1^2-4*c0*c2; pair discriminant is pair determinant squared; native Sym² action scales it by det²; maps and arbitrary scalar extensions preserve law; SL2 invariance.
- PaperSymmetricPairNormalDiscriminant: actual normal discriminant equals degree-two initial class of (ad-bc)^2. Vanishes iff (1:K)=0, unconditional for all CommRing. Polynomial has coefficient 1 at X1².
- PaperSymmetricPairNormalAction: arbitrary polynomial 2x2 coordinate matrices preserve original generator ideal; actual initial coordinates obey native Sym² covariance; normal discriminant scales by scalar det², fixed by polynomial SL2.
- PaperSymmetricSquareNormalRelations: all nine coefficients of native symmetricSquareMatrix(genericVarMatrix K 2), with their actual ideal. Actual initial classes preserve EXACTLY all scalar polynomial relations; actual generator coordinate ring embeds. Determinant of actual normal matrix is degree-three initial class of generic determinant cubed. Every power of normal determinant vanishes iff (1:K)=0. Generic determinant cube belongs to I³ and belongs to I⁴ iff (1:K)=0. Thus exact ideal order three over every nonzero commutative base ring.

Lean implementation lessons:
- Concrete quotient / polynomial ring instances can explode at default heartbeats. Cache generic `CommRing (PaperIdealAssociatedGraded I)` in a private abbrev and specialize with local instance before defining maps. This reduced normal determinant comparison from timeout to clean compile, no heartbeat hacks. Give generic ring-map lemmas explicit R/A when needed.
- For scalar action, cache generic Module, SMul, Algebra on actual graded quotient. Prove discriminant scalar-extension identity with abstract R/A first, then specialize; avoid concrete quotient RingHom instance diamonds.
- `ext i j` on polynomial-valued matrix equality recursively adds coefficient goals. Use `funext i j` for exactly matrix entries. Supply `aeval_X (R := K)` to fix coefficient algebra inference.
- NativeRees homogeneous coefficient membership: `simpa using h` handles coeff_monomial's residual if True; simp-only can leave it.
- Broad simp on quotient discriminant tried costly cancellation instances; use only map_sub/map_mul/map_pow/map_ofNat and mul_assoc.
- MonomialOrder methods carry extra Syn universe. Private/local declarations excluded from public inventory; exact dotted local names preserved.

Searches: direct Lean-only outputs inspected from symmetric-normal-search, symmetric-leading-substitution-search, symmetric-elementary-search, leading-monic-search, symmetric-discriminant-search, symmetric-discriminant-deep-search, symmetric-determinant-nonzero-search. Last deep search partial=true but complete file inventory; useful native minor results found, final applicability verified by Lean. Exact searchback all64 succeeded after index refresh.

Global formal lint still reports unrelated unwired HTGeometry.GammaTwoSanov and HTGeometry.QKrawtchoukCompanionTriangular. Neither is owned by this task; no new owned errors. Preserve concurrent work. No commits/pushes, no computations/experiments, no added axioms or unpaid analytic premises.

Overall unbudgeted goal remains ACTIVE. Next: search further direct Lean receivers across all routes/candidates, consider additional invariant/incidence families and other source mechanisms, monitor upstream growth. Do not mark overall goal complete merely because this batch is complete. No live jobs or unfinished proof files remain from this batch.