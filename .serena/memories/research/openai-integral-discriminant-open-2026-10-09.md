# Integral discriminant and its actual normal-ring complement — 2026-10-09

Unbudgeted goal remains ACTIVE. All 16 live routes +23 candidates in docs/reports/rh-current-frontier-map.md remain in scope, no Weil priority. Previous goal turn classified progress. Source Lean results are PROVEN. No subagents, commits/pushes, numerical experiments, added axioms, heartbeat changes, full builds, or umbrella builds.

Authoritative current batch:
tmp/hgt-openai-math/integral-discriminant-audits.json
integral-discriminant-manifest.json
integral-discriminant-searchback-audit.json
Tracker stable-coordinate-native-port.json latest_verified_batch=integral-discriminant-audits.json; previous=integral-symmetric-audits.json. Broad all-route-applications.json also updated with stable_coordinate_integral_discriminant_batch.

4 new modules, 20 new theorems, 29 public declarations. All four final foreground lake --old env lean leaf checks empty; all 29 axioms only propext/Classical.choice/Quot.sound. Exact path+name searchback all29 passed. Objects fresh in formal/.lake/build/lib/lean. All new imports wired once into HTGeometry, no umbrella build. No owned source objects.
543 owned Lean leaves /4528 public math results.
StableCoordinate family:117source+100application=217modules /2355 public declarations audited historically. 74 prior source hashes existed in tracker and were revalidated unchanged;139 earlier rows have no sha256 baseline (do not pretend these have fresh hash validation). Assert every completed module in normalized owned inventory.
All owned processes terminal, four helpers deleted; retain /tmp/paper-integral-discriminant-axioms.lean. No remaining scratch helpers from current batch. Git diff --check umbrella clean.

Upstream HEAD rechecked unchanged fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Current source family inventory in integral-discriminant-source-families.txt (24 OAI areas); native checkout Lean4.32.2, upstream4.34.1. All117StableCoordinate source leaves already native-ported (raw118includesAll.lean).

Four new files, namespace GaloisForLFunctions.HTGeometry:
1. PaperIntegralDiscriminant.lean (8public,7thm):
- paperUniversalVandermonde_eq_native: determinant-product universal V equals native PermutationAction.vandermonde K n for allCommRing. Proof reindexes Equiv.Perm.finPairsLT as univ.sigma filtered lower pairs; Finset.prod_sigma/prod_filter/prod_comm.
- paperNativeVandermonde_regular transports universal V regularity to that existing native definition.
- private universalVandermonde_square_symmetric reuses native isSymmetric_vandermonde_sq; no duplicate general symmetry proof.
- paperIntegralDiscriminantPolynomial K n := integral coefficient retraction(V*V).
- _spec: aeval elementary symmetrics(D)=V*V.
- _regular: IsRegular D over EVERY CommRing, including zero divisors and zero ring. Injective esymm substitution (paid by retraction) reduces cancellation to regular V².
- _pow_eq_zero_iff m: D^m=0 ↔(1:K)=0, including m=0.
- _baseChange f: map f D_K=D_L for ANY ring hom K→+*L.
- _eq_native F d forFieldF: D_F=existing discCoeffPolyF d.

2. PaperIntegralNormalDiscriminant.lean (4public,3thm):
- paperIntegralNormalDiscriminant := actual paperElementarySymmetricNormalMap(D).
- _eq_embedding: equal symmetric normal embedding of native vandermondeK n^2.
- _pow_eq_zero_iff m: actual normal D^m=0 iff1K=0.
- _eq_native F d: equal existing paperSymmetricNormalDiscriminant over everyField.
This is the actual source associated graded ring, not an abstract surrogate.

3. PaperIntegralDiscriminantLocalization.lean (9public,5thm):
- PaperDiscriminantCoefficientOpen :=Localization.AwayD.
- PaperDiscriminantNormalOpen :=Localization.Away(actualNormalD).
- paperDiscriminantOpenEmbedding : coefficientOpen→ₐ[K]normalOpen :=Localization.awayMapₐ(actualNormalMap)D.
- _injective from Mathlib localization of injective map.
- _algebraMap: polynomial inclusion sent to localization of actual normal image.
- paperDiscriminantCoefficientOpen_injective: original coefficient algebraMap into coefficientOpen injective because every Dpower regular.
- paperDiscriminantOpenCoefficientMap := IsScalarTower.toAlgHom K actualNormalRing normalOpen composed actualNormalMap.
- _injective, _eq_zero_iff: removing discriminant divisor kills NO original coefficient polynomial over anyCommRing.
Private generic CommRing cache specialized to actual normal ideal resolves elaboration heartbeat issue, NO heartbeat limit raised.

4. PaperSymmetricDiscriminantOpen.lean (8public,5thm):
- paperSymmetricDiscriminantOpenEmbedding := openCoefficientMap ∘ Mathlib allCommRing esymmAlgEquiv.symm.
- _injective,_eq_zero_iff.
- _relations_iff for ANY symmetric family a:ι→symmetricSubalgebra and p:MvPolynomialιK: aeval(openEmbedding∘a)p=0 iff aeval(coe∘a)p=0.
- paperSymmetricBlockDiscriminantOpenCoefficient r c k embeds native PowerSeries.coeffk(symmetricBlockr c).
- _relations_iff for all countable multiplier coefficients.
- paperBeurlingDiscriminantOpenCoefficient and _relations_iff for native bernoulli'-scaled Beurling family.

Mathematical verdict BRIDGE: classical integral symmetric descent and localization applied to PROVEN source Rees kernel + actual native discriminant/multiplier structures. No claim of new general discriminant/localization theory. Full dependency-closed argument in tracker candidate.

Searches completed and Lean-only hits inspected:
integral-discriminant-search.json (deep120s complete inventory)
integral-discriminant-localization-search.json (deep120s complete inventory)
integral-block-open-search.json (lexical --any; available ranked native hits used)
All searchJSON path key relpath. Never read cards; whitelist .lean in declarations/candidate_lemmas/source_arguments and coverage/freshness.

Useful native files/API:
- DiscriminantPolynomial.lean contains Field-only vandermondePoly, symmetry, zeroLast and top-esymm nondivisibility. Read whole115lines this turn; unchanged.
- SymmetricCoefficientNonSquare.lean Field-only esymmAlgEquiv and discCoeffPoly; native E≡Mathlib E by same esymmAlgHom and proof irrelevance.
- PermutationAction.lean allCommRing vandermonde uses finPairsLT (sigma pairs with second<first), isSymmetric_vandermonde_sq. This native definition is NOT syntactically same as vandermondeProd until finite-product reindexing.
- MvPolynomial.comp_aeval_apply f φ p gives φ(aevalf p)=aeval(φ∘f)p.
- IsLocalization.Away.mapₐ_injective_of_injective a (hf:Injectivef) gives localizedAlgHominjective.
- IsLocalization.map_eq has only hy,x explicit in current signature; Q,g,etc implicit.
- IsLocalization.injective S (hM:M≤nonZeroDivisorsR).

Lean pitfalls/resolutions:
- Default200k-heartbeat elaboration failed for concrete localized source quotient. Generic private abbrev {R}[CommRingR](I:IdealR):CommRing(PaperIdealAssociatedGradedI):=inferInstance, specialized local instance to actual ideal, fixed it. No heartbeat hacks.
- For localized-map injectivity, first change target to Function.Injective(Localization.awayMapₐ(actualNormalMap)D), then apply mapₐ_injective_of_injective with explicit f. Supplying alias PaperDiscriminantNormalOpen as Bₚ caused TC failure because semireducible normalD hides fD.
- For map_eq, give explicit M=powersD,T=powersnormalD,S,Q,g and prove hy by rintro x⟨m,rfl⟩; exact⟨m,(map_pow f D m).symm⟩.
- In coefficient-map injection, rw localizedEmbedding_algebraMap twice then exact h; simpa only using h failed to reduce AlgHom composition.
- Normal-discriminant embedding proof needs membership explicitly (mem_symmetricSubalgebra _).mpr nativeSymmetry, then change coefficient equality to E.symm before applying E.injective. Rewriting pow_two under projected dependent subtype fails; finish exact(pow_two_).symm.
- Generic symmetric relation proof: comp_aeval_apply with subalgebra.val is defeq to coercion but rw cannot see it. Define a typed hv:(aevala p:R)=aeval(coe∘a)p := comp_aeval_apply ...; rw←hv.
- All new Mathlib API names verified in /tmp scratch before final checks; scratch deleted after audit.

Current GLOBAL lint NINE foreign unwired errors, none owned:
RHTower.RiemannAutocorrBalancedQuadratic
RHTower.Sieve.UnitBlockFrequencyBounds
RHTower.Sieve.UnitBlockFrequencyComparison
RHTower.Sieve.UnitBlockPoissonKernel
RHTower.WeilLogShiftQuarticClusterCost
RHTower.WeilLogShiftTripleCancellation
HTGeometry.MonotonePhaseFirstDerivativeTest
HTGeometry.QKrawtchoukCompanionTriangular
HTGeometry.SmoothPlateau
Do NOT wire or alter foreign work. Previous four-error snapshot no longer current. Index regenerated LEAN_API/GAPS/OVERVIEW/searchDB successfully.

Next:
Continue all-route direct Lean/source mechanism sweep, not just wrappers of completed discriminant results.
Potential source-mechanism application: invariant localization/factorial closure classifies native derivations that remain locally nilpotent after discriminant inversion. Search existing root-translation/coefficient derivation infrastructure before adding. PaperNativeInvariantLocalization and PaperIntrinsicFiberLocalization were read this turn; source factor closure kills units, nativeAway_locallyNilpotent_iff over characteristic-zero domains is already proved. No new derivation candidate started yet.
Always one foreground Lean process, poll exact owned handle terminal before another; never inspect live logs; no full/umbrella builds. Normalize mixed absolute/relative own-files inventory. Maintain goal ACTIVE at batch boundaries.