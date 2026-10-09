# OpenAI integral symmetric normal-coordinate application — 2026-10-09

Goal remains active, unbudgeted. All 16 live routes and 23 candidates in docs/reports/rh-current-frontier-map.md remain in scope; no Weil priority. Proven OpenAI/math source results remain PROVEN. No subagents, commits, pushes, numerical experiments, new axioms, heartbeat changes, full builds, or umbrella builds.

Source HEAD rechecked: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. StableCoordinate source family still complete: 117 actual source leaves (118 raw includes import-only All.lean). Native checkout Lean 4.32.2, source 4.34.1.

Authoritative audit: tmp/hgt-openai-math/integral-symmetric-audits.json
Manifest: integral-symmetric-manifest.json
Searchback: integral-symmetric-searchback-audit.json
Tracker: stable-coordinate-native-port.json, latest_verified_batch=integral-symmetric-audits.json, previous_goal_turn_classification=progress.
5 new modules, 21 new theorems, 27 new public declarations; 9 existing theorems strengthened. 8 affected modules / 49 public declarations audited. All final foreground lake --old env lean leaf checks empty; all 49 axioms only propext/Classical.choice/Quot.sound. All exact path+name searchbacks passed. All objects fresh in .lake/build/lib/lean. No owned source objects. Five new imports wired once into HTGeometry, no umbrella build.
539 owned leaves, 4508 public math results. StableCoordinate family 117 source +96 application modules =213 modules /2326 public declarations audited.
All owned processes terminal. Four scratch helpers removed; retain /tmp/paper-integral-symmetric-axioms.lean only from this batch.

New files in formal/GaloisForLFunctions/HTGeometry/:
- PaperUniversalVandermondeRegular: every universal variable difference and universal Vandermonde regular over arbitrary CommRing, including zero divisors and zero ring. Lex-leading coefficient of Xj-Xi for i<j is -1; split subsingleton/nontrivial base to use leadingCoeff_X. V permutation sign law.
- PaperIntegralAntisymmetrization: integral signed permutation sum as K-linear map; alternating sign law, invariant-factor law; monomial signed sum=C coefficient * native power-evaluation determinant. Native AlternantVandermondeDivisibility.vandermondeProd_dvd_det_pow works over every CommRing, giving V divisibility. Ascending staircase delta=product_i Xi^i has antisymmetrization exactly V. No factorial division.
- PaperIntegralSymmetricProjection: P(p)=unique quotient A(delta*p)/V. Constructed via private choice and regular cancellation. K-linear, symmetric, linear over symmetric polynomial factors, fixes invariant polynomials.
- PaperIntegralSymmetricRetraction: compose P with Mathlib all-CommRing MvPolynomial.esymmAlgEquiv (Fin n) K (Fintype.card_fin n).symm. Coefficient retraction spec, fixes aeval esymm, linear over coefficient algebra. paperIntegralElementarySymmetricRetraction packages PaperIdealRetraction.
- PaperIntegralSymmetricBaseChange: V, A, delta, P and coefficient retraction commute with EVERY ring hom K→+*L, including noninjective and positive-characteristic maps; no flatness premise. Reuses native SymmetricDescentBaseChange.map_esymmAlgHom.

Existing changes:
- PaperElementarySymmetricNormalSpace strengthened IN PLACE from Field+CharZero to CommRing. Imports integral retraction instead of averaging. Uses Mathlib general esymmAlgEquiv. Existing actual normal-coordinate injection, symmetric algebra embedding and exact coefficient-variable ideal-power membership all now arbitrary CommRing.
- PaperSymmetricDiscriminantEmbedding removes CharZero, keeps Field due native discCoeffPoly definition. Explicitly imports SymmetricCoefficientNonSquare after transitive import changed. eq_embedding still rfl (proof irrelevance for equivalent AlgEquiv.ofBijective proofs). All powers nonzero in EVERY field.
- PaperSymmetricBlockNormalEmbedding unchanged and freshly compiled: every scalar relation among native countable multiplier/Beurling coefficient families and equality of whole formal blocks preserved.
- Old PaperSymmetricCoefficientRetraction averaging implementation remains valid independent characteristic-zero infrastructure; do not delete.

Mathematical novelty verdict BRIDGE, not a new general symmetrizer. Classical longest-element isobaric divided difference/staircase symmetrizer shown in Luque arXiv:0802.1454 section5 pp13–14 (https://arxiv.org/pdf/0802.1454); our ascending variable convention reverses displayed ordering. New application connects native determinant divisibility to PROVEN source Rees kernel and strengthens native normal-coordinate realizations. Adjacent arXiv:1908.10934 checked, not proof premise. Dependency-closed mathematical argument recorded in tracker candidate.

Searches, all terminal:
integral-splitting-deep-search.json, vandermonde-regular-search.json, integral-symmetric-basechange-search.json (deep complete inventory, no exact integral retraction); integral-symmetric-splitting-search.json and integral-basechange-lexical.json. Direct Lean only; no cards. JSON Lean path key is relpath, NOT path. Whitelist .lean entries in declarations/candidate_lemmas/source_arguments and metadata.

Lean lessons:
- After apply (paperUniversalVandermonde_regular K n).left, rw may see unreduced (fun x=>V*x) arguments; dsimp only before rw. simp and exact already reduce them.
- aeval esymm is NOT definitionally coe esymmAlgHom; use esymmAlgHom_apply. For Mathlib E use simp only [MvPolynomial.esymmAlgEquiv_apply, esymmAlgHom_apply].
- rw [map_mul] can wrongly target nonmultiplicative projection LinearMap: specify map_mul (aeval ...), p, q.
- Native map_esymmAlgHom uses Fin(Fintype.card σ). For σ=Fin n, take h:=map_esymmAlgHom (σ:=Fin n) f WITHOUT supplying polynomial; rw [Fintype.card_fin] at h; then simp only [esymmAlgHom_apply] at h. simp alone does not rewrite dependent binder domain.
- Int.units_coe_mul_self is actual name; units_val_mul_self nonexistent.
- All new Mathlib API names verified in /tmp probe; probe removed after successful final checks.

Latest global lint has FOUR foreign unwired-module errors, none owned:
RHTower.Sieve.UnitBlockPoissonKernel
HTGeometry.MonotonePhaseFirstDerivativeTest
HTGeometry.QKrawtchoukCompanionTriangular
HTGeometry.SmoothPlateau
Do not modify foreign files or imports. Prior six errors no longer current. Lint log integral-symmetric-lint.log. Index succeeded (LEAN_API/GAPS/OVERVIEW and search database regenerated).

Next possible extension, not yet started:
Integral generic discriminant over arbitrary CommRing using universal V² and integral coefficient descent, natural under every coefficient map, sharp nonzero-power iff 1_K≠0 boundary. Native vandermondePoly in DiscriminantPolynomial.lean and discCoeffPoly in SymmetricCoefficientNonSquare.lean currently Field-only. Search Lean before adding. Also continue broad source-to-native application sweep across all routes; do not mark overall goal complete at this batch boundary.

Important process: ONE foreground Lean process at a time. Poll exact session terminal before new Lean or modifying compiling leaf. Never inspect live logs. Serial guarded audit helper was successful. Own-files.txt mixes absolute/relative; normalize/dedup, assert every completed manifest path is owned. Public regex excludes private and preserves dotted local names; exact path+canonical-or-local name searchback, never suffix matches.
