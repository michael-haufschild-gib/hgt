# Rational CCM restriction has a continuous Real-Brauer lift — formalized closure

- **ID:** `ccm-rational-analytic-real-descent-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-rational-analytic-real-descent.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicBruhatSchwartzSpace` — Bruhat's Schwartz space of
  `ℝ × 𝔸_f`, its identification with the algebraic tensor core, and the pointwise form of the
  source involution.

Carrying the rest of the theorem (all pre-existing):

- source Real structure and its continuity: `CCMRationalAdelicRealStructure`,
  `CCMRationalAdelicLFTopology`, `CCMRationalAdelicTwistedRestrictionReal`;
- endpoints and reduced source: `CCMRationalAdelicEpsilonZero`, `CCMRationalAdelicEpsilonOne`,
  `CCMRationalAdelicEndpointReal`;
- target: `CCMRationalMoritaTraceNormAlgebra`, `CCMRationalStrongCyclicTarget`,
  `CCMRationalStrongCyclicTargetReal`, `CCMRationalNonunitalStrongCyclicReal`;
- landing in CCM Definition 4.9: `CCMRationalAdelicTensorStrongClassSpaceLanding`,
  `CCMRationalAdelicReducedStrongCyclicHom`;
- restriction equivariance: `CCMRationalAdelicRestrictionReal`,
  `CCMRationalAdelicTwistedRestrictionReal`;
- closed quotient and idele-class action: `CCMRationalAdelicClosedStrongRealLefschetz`,
  `CCMRationalAdelicClosedNonunitalStrongRealLefschetz`, `KRealClosedCokernel`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Formal theorem chain

1. **The source space is Bruhat's space, not a dense core.**
   `IsCCMRationalAdelicBruhatSchwartz` is Bruhat's condition on `ℝ × 𝔸_f`: one compact open
   period subgroup in the finite variable, one compact support in the finite variable, and a
   Schwartz function along every finite fibre.  `range_ccmRationalAdelicBruhatEval_eq` proves that
   the canonical realization of `𝒮(ℝ) ⊗ C_c^∞(𝔸_f)` has range exactly that space, and
   `ccmRationalAdelicBruhatEval_injective` proves the realization is faithful, so
   `ccmRationalAdelicBruhatEquiv` is a linear isomorphism onto it.  The substantive direction is
   the finite-coset decomposition: a compact set meets only finitely many cosets of an open
   subgroup, so every Bruhat function is a finite sum `∑ φ(·, yᵢ) ⊗ 1_{yᵢ + K}`.
2. **The algebraic involution is Bruhat's involution.**  `ccmRationalAdelicBruhatEval_sigma`:
   the core's sign-reflection realizes pointwise as `φ ↦ conj (φ ∘ (-1))`, equation `(2)` of the
   card on the genuine function space.
3. **Claim 1 — continuous conjugate-linear unital algebra involution.**
   `ccmRationalAdelicCrossedProductRealStructureₛₗ` (conjugate-linear),
   `ccmRationalAdelicCrossedProductRealStructure_mul`, `..._sq`,
   `ccmRationalAdelicTwistedSourceReal_one`, `ccmRationalAdelicSourceRealStructure_continuous`
   for the LF topology `ccmRationalAdelicSourceLFTopology`.
4. **Claim 2 — the reduced source is stable.**  `ccmRationalAdelicEpsilonZero_real` and
   `ccmRationalAdelicEpsilonOne_real` (`εⱼ ∘ α = conj ∘ εⱼ`), `ccmRationalAdelicReducedSourceCyclic_real_stable`
   (stability of the simultaneous cyclic double kernel), and the even Real cyclic structures
   `ccmRationalAdelicReducedSourceCyclicKReal`,
   `ccmRationalAdelicTwistedReducedSourceCyclicKReal`.
5. **Claim 3 — the target involution.**  `ccmRationalMoritaTraceNormL1RealStructure_norm`
   (trace-norm isometry, equation `(4)`'s premise), `..._mul`, `..._sq`,
   `ccmRationalMoritaTraceNormL1Trace_real` (`Tr(αT) = conj Tr T`),
   `ccmRationalStrongDiagonalTrace_real` (degreewise cyclic diagonal trace conjugation), and the
   even structures `ccmRationalStrongCyclicTargetKReal`,
   `ccmRationalNonunitalStrongCyclicTargetKReal` on CCM Definition 4.9.
6. **CCM Definition 4.9 landing.**  `ccmRationalAdelic_reduced_source_image_mem_strong` — the
   cyclic diagonal trace of the reduced source lands in the all-weight Meyer target
   `DeningerMeyerStrongLogTarget`, i.e. in `𝐒(C_ℚ)`; `ccmRationalAdelicReducedStrongCyclicHom`
   bundles the degreewise maps into the cyclic morphism `ρ^♮`.
7. **Claim 4 — equation `(3)`.**  `ccmRationalAdelicReducedStrongCyclicKRealHom` and
   `ccmRationalAdelicReducedNonunitalStrongCyclicKRealHom` are `CyclicModule.KRealHom`s, whose
   `real_naturality` field is exactly `α_B^♮ ∘ ρ^♮ = ρ^♮ ∘ α_A^♮` in every simplicial degree; the
   `KReal` structures themselves carry face, degeneracy and cyclic naturality, so this is an
   identity of cyclic morphisms, not a degree-zero extrapolation.
8. **Claim 5 — even `K_ℝ` on the closed quotient.**
   `ccmRationalAdelicClosedStrongRelativeCyclicKReal` and
   `ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal` are `CyclicModule.KReal false`
   structures on the quotient by the closed range of `ρ^♮`.
9. **Claim 6 — the rational idele-class action.**
   `ccmRationalNonunitalStrongCyclicRightActionDegree_real` (class-space translation commutes with
   the target involution) and `ccmRationalAdelicClosedStrongLefschetzKReal`,
   `ccmRationalAdelicClosedNonunitalStrongLefschetzKReal` (every Lefschetz correspondence is a
   `KRealHom` of the closed quotient).

## Verification

- `lake env lean` clean, with no warnings, on `CCMRationalAdelicBruhatSchwartzSpace`.
- `lake build GaloisForLFunctions.RHTower` — green (18146 jobs) with the new module wired into the
  umbrella.
- `#print axioms` on the seventeen capstones of the chain above: `propext`, `Classical.choice`,
  `Quot.sound` only.  Every statement is closed: no hypothesis parameter, no `Prop` interface, no
  added axiom.

## Scope boundary

The card's own open item is untouched: this is the Real-equivariant restriction and its closed
quotient, not the chain-level Real Morita equivalence identifying the intertwiner realization with
CCM's single complex cyclic realization.  That remains gate 5 of the paper card.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
