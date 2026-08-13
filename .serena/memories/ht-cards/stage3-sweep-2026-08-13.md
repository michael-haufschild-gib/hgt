# ht/ folder stage-3 sweep (goal: formalize all 7 cards in 2-fully-proven/new_scientific_knowledge/ht)

## Status 2026-08-13 (afternoon)

### Card 1 triptic-kummer — ✅ DONE, PROMOTED TO STAGE 3
Six new modules, all built, all `[propext, Classical.choice, Quot.sound]`, wired into the
HTGeometry umbrella, lint gate passed (`formal_tools.py lint` exit 0, indexes regenerated):
`TripticMultiplicativeSourceClass`, `TripticSourceDivisorFinsupp`,
`TripticGammaProductRealization`, `TripticKummerRootClassification`, `TripticSourceReciprocity`,
`TripticSourceClassGroup`.
Card git-mv'd to `3-formalized/new_scientific_knowledge/ht/` with Stage set to 3-formalized, a new
companion `triptic-ht-kummer-content-root-classification-formalized.md` (module list + theorem
chain + verification block), relative link fixed, Formalized-companion pointer added.
Everything in the card is formal: divisor in ℤ[ℂ/H₃] (τ-invariance from germ constraint; finite
class support by fundamental-parallelogram reduction), reciprocity D_σ=D_τ on the class, kernel =
DA both directions (germ forms), gamma-product realization of every divisor, root theorem
(charge + content forms) + uniqueness + exact max root order, germ-unit group packaging with
`tripticSourceQuotientEquiv : M/ker D ≃+ ℤ[ℂ/H₃]` and verbatim abstract Kummer application.
NOTE: another concurrent agent session repaired two of my modules mid-flight (lemma names/tactics)
and prebuilt them — cooperative concurrency worked; check file mtimes before editing shared files.

### Card 4 (nonautonomous-rational-first-order-tail-orbifold-law) — IN PROGRESS
Plan in `mem:ht-cards/card4-complete-tail-plan`. Already built this session:
`FreeDifferentialTranslationAutomorphism.lean` (u ↦ c + u differential automorphism of free
C⟨u⟩; jets unchanged in positive degrees; adjunction invariance) — built, wired, axiom-clean.
Next steps:
1. `DerivativeTranslationFixedField.lean` — additive mirror of LogarithmicDerivativeFixedField:
   C⟨u⟩ = C⟨u′⟩(u) (jets n≥1 lie in C⟨u′⟩ since jet(n+1)u = jet n (u′)); u transcendental over
   C⟨u′⟩ (translation orbit c+u infinite, mirror transcendental_over_logDerivField);
   invariant ⟹ ∈ C⟨u′⟩ via RatFunc translation transport + existing
   `ratFuncTranslation_fixed_eq_constant` (RatFuncTranslationFixedField.lean; needs CharZero base
   via charZero_of_injective_algebraMap); final `fixedField_translation_eq_derivField`.
   NOTE ALSO: `FreeJetTranslationFixedField.lean` already proves the model-side version
   (fixed field of depth-0 coordinate translations = tail-coordinate field) — check reuse before
   writing; `ScalarAdditiveDifferentialTorsor.fixedField_zpowers_scalarDifferentialTranslation_one`
   proves "unit translation fixes exactly F⟨q′⟩" via `scalarDerivativeField` — POSSIBLY ALREADY THE
   WHOLE ADDITIVE LAYER: its carrier T with q hypertranscendental, hgen top. Verify whether that
   theorem + rotation layer suffices without my new fixed-field module.
2. Rotation layer: rank-1 instance of `fixedField_torusScaleRep_eq_torusInvariantMonomialField`
   (TorusProtocolMonomialTail.lean) with S = ⟨ζ⟩ (ζ primitive n-th root, n ∈ {2,3,4,6}) on the
   subfield C⟨u′⟩-as-field (plumbing via DifferentialSubfieldTransfer adjoinLift); simplify
   C⟨v′/v, vⁿ⟩ = C⟨vⁿ⟩ via v′/v = (vⁿ)′/(n vⁿ).
3. (2,2,∞): inversion w ↦ w⁻¹ via paletteEndo (independence of inverse palette via
   `DifferentialIndependentTransfer.differentialIndependent_of_range_subset_closure`); acts by
   ℓ ↦ −ℓ on ℓ = w′/w; rank-1 scaling machinery with S = {−1} gives C⟨ℓ²⟩;
   `logDeriv_sq_eq_chebyshev_current` identifies downstairs.
4. Protocol assembly per signature mirroring MultiplicativeProtocolLogCurrentTail /
   TorusProtocolMonomialTail; then card-4 promotion (its §§1–3 already formal per card text).

### Cards 2,3,5,6,7 — recon notes unchanged (see earlier sections of this memory’s history and
`mem:ht-cards/card4-complete-tail-plan`): card 3 = abelian-variety degree data
(AbelianVarietyIsogenyTail.lean conditional bridge exists); card 2 = canonical carrier +
all-depth exact image (parent card in other/); card 6 = Pong/Andersson/Saksman–Webb (large formal
Dirichlet DA layer exists: PrimeDirichletDifferentialField etc.); card 7 = Barnes (4)–(6) +
Sibuya–Ramis (large Barnes layer exists: BarnesDoubleZeta*, BarnesKernelExpansion, NewtonPuiseux*).
