# Isogeny tails are Maurer–Cartan holograms of the iterated deck closure — Lean certificate

- **ID:** `isogeny-tail-maurer-cartan-holography-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `isogeny-tail-maurer-cartan-holography.md` (proof route: the order-zero
  reduction recorded there under "Lean plan — order-zero reduction of Theorems A–D" and
  "Functor-of-points Maurer–Cartan")
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Setting in Lean

`C` an algebraically closed field of characteristic zero; `G : Over (Spec C)` a group object
(`GrpObj G`) that is commutative (`IsCommMonObj G`), integral (`IsIntegral G.left`: connected
reduced) and locally of finite type; `α : G ⟶ G` with `IsIsogeny G α` (a homomorphism that is
surjective with finite kernel).  No further hypothesis appears in any capstone except the card's
own density assumption `H = G` in Corollary C and the commutation `φ ∘ α = α ∘ φ` in Corollary D.

- `F = C(G)` is `G.left.functionField`; `g` is the generic point as an `F`-valued point.
- `K = C(J^∞G)` is `GroupJetField G`, the free differential field over `F` on a transcendence
  basis (`groupDim G = dim G`, `groupDim_eq_trdeg`), with derivation `groupJetDerivation G`.
- `α*` on `K` is `jetIsogenyPullback G α` (the unique differential extension of the
  function-field pullback); `Tail(α) = {u | ∀ n, u ∈ range (α*)^[n]}`.
- `Γ_n = ker(αⁿ)(C)` is `isogenyKernelPoints G α n`; `H(C)` is `deckClosurePoints G α`, the
  rational points in the Zariski closure of `⋃ₙ Γ_n`; translation on `K` is `jetTranslation`.
- `ℓ_δ(g)` is `maurerCartanPoint`: the `K[ε]`-point `G(ψ_δ)(g) · G(ι)(g)⁻¹` of `G`, with
  `ψ_δ(a) = a + ε δa`; its tangent coordinates are
  `tangentCoords G (GroupJetField G) (jetDerivationOnFunctions G) : Fin r → K`
  (`maurerCartanPoint_eq_tangentLift`).
- The position field `C(Q) = C(G/H) = π*C(Q)` is `deckClosurePositions G α = F^{H(C)}`.

## Capstones

All in `formal/GaloisForLFunctions/HTGeometry/`:

- **Theorem A** `mem_isogenyTail_iff_deckClosure_fixed` (`AlgebraicGroupIsogenyTail`):
  `u ∈ Tail(α) ↔ ∀ x ∈ H(C), x·u = u`, i.e. `Tail(α) = K^{H(C)}`.
  Level input `mem_range_isogenyPullback_pow_iff` (`IsogenyFunctionFieldLevel`):
  `α^{n*}C(G) = C(G)^{Γ_n}`.
- **Theorem B (4)** `deckClosure_fixed_iff_mem_differentialAdjoin_maurerCartanPoint`
  (`AlgebraicGroupMaurerCartanPoint`): `K^{H(C)} = C⟨F^{H(C)}, ℓ_δ(g)⟩`; also in the
  invariant-derivation coordinates `deckClosure_fixed_iff_mem_differentialAdjoin`
  (`AlgebraicGroupPositionVelocity`).
  **`α` induces an automorphism of `Q`**: `bijOn_overFunctionFieldPullback_deckClosurePositions`
  (`α*` restricts to a bijection of `C(Q) = F^{H(C)}`).
- **Corollary C** (`H = G`, hypothesis `Dense (⋃ₙ Γ_n)`):
  (5) `mem_isogenyTail_iff_mem_differentialAdjoin_maurerCartanPoint`
  (`Tail(α) = C⟨ℓ_δ(g)⟩`) and `mem_isogenyTail_iff_mem_velocityField`;
  (6) `algebraMap_mem_isogenyTail_iff` (`Tail(α) ∩ C(G) = C`);
  (7) `differentialTranscendenceDegree_velocityField` (`dtrdeg_C C⟨ℓ⟩ = dim G`) and
  `differentialTranscendenceDegree_groupJetField` (`dtrdeg_C K = dim G`)
  (`AlgebraicGroupIsogenyTailCorollaries`).
- **Corollary D** (`AlgebraicGroupIsogenyTailCorollaries`), for any set `Φ` of automorphisms of
  `G` commuting with `α` (in particular a finite group; `K^Φ = C(J^∞(G/Φ))`):
  (8) `finiteHolonomyTail`: `⋂ₙ α^{n*}(K^Φ) = (K^{H(C)})^Φ`;
  (9) `finiteHolonomyTail_of_dense`: `⋂ₙ α^{n*}(K^Φ) = C⟨ℓ⟩^Φ` when `H = G`.

Axiom audit (every capstone above, plus `maurerCartanPoint_eq_tangentLift`,
`tangentCoords_jetDerivationOnFunctions`, `groupDim_eq_trdeg`):
`[propext, Classical.choice, Quot.sound]`.

## What the corpus already had

`DeckClosureStableCore` and `FixedFieldStableCoreRestriction` (fixed fields commute with
intersections; stable cores of commuting restrictions), `DifferentialTranscendenceDegree`
(differential matroid rank and the basis-cardinality formula), `AlgebraicGroupJet`
(scheme-valued jets), the Picard–Vessiot/differential-adjoin API, `conjDerivation`
(`AffineLineEtaleLocallyNilpotent`) and `differentialAlgebraicOver_of_isAlgebraic`
(`HypertranscendentalPow`).

## What was built

Field level (reusable, no geometry):

- `FunctionFieldJetField`, `FunctionFieldJetBasis` — the free differential field on a
  transcendence basis; triangular jet families are independent and generating.
- `FunctionFieldJetExtension` — every `C`-endomorphism of `F` extends uniquely to a differential
  endomorphism of `K`; functoriality; automorphisms.
- `FixedAdjoinIndependentDescent` — `F(y)^Γ = F^Γ(y)` for independent `Γ`-fixed `y`.
- `MaurerCartanJetCoordinates` — `δa = Σ ℓ_i D_i a` for a derivation basis `D`; the `ℓ`-jets are
  independent over `F` and generate `K`; chain-rule matrix and `φ̃ ℓ_j = Σ a_ij ℓ_i`.
- `MaurerCartanFixedFields` — `K^σ = PV(F^σ)`, `φ̃(K) = PV(φF)` for constant chain-rule matrix,
  and the abstract Theorem A `mem_tail_iff_fixed` from the two order-zero inputs.

Scheme level:

- `AlgebraicGroupGenericPoint` — the generic point as an `F`-valued point, injectivity of field
  points through it, translation action `x ↦ σ_x` on `F`.
- `AlgebraicGroupRationalPointEvaluation` — values at rational points; stabilizers of rational
  functions are Zariski closed; `C(G)^{G(C)} = C`.
- `IsogenyFunctionFieldLevel` — `IsIsogeny`, field points of finite `C`-schemes are constant, the
  level theorem `α^{n*}C(G) = C(G)^{Γ_n}` via conjugate embeddings (no degree theory).
- `SchemeStalkPoints`, `SquareZeroPointLifts` — points of local rings as stalk maps; dual numbers
  `L[ε]`, `L[ε₁,ε₂]`; the group law on lifts is addition.
- `AlgebraicGroupTangentMap`, `AlgebraicGroupDerivationCoordinates` — derivations `F → L` are
  lifts of the generic point to `L[ε]`; the tangent coordinates `Θ : Der_C(F,L) → L^r` are
  `L`-linear, injective and translation-equivariant.
- `AlgebraicGroupInvariantDerivations` — Galois-type descent of stable subspaces; a basis of
  translation-invariant derivations with `det(D_i t_j) ≠ 0`.
- `AlgebraicGroupIsogenyTail`, `AlgebraicGroupPositionVelocity`,
  `AlgebraicGroupIsogenyTailCorollaries`, `AlgebraicGroupMaurerCartanPoint` — assembly of
  Theorems A–D and the literal Maurer–Cartan point `ℓ_δ(g)`.

## Mathematical note

The proof does not use the differential rational quotient theorem (elimination of imaginaries).
It reduces to order zero: with a basis `D_i` of translation-invariant derivations of `F`, the
velocity `ℓ` satisfies `δa = Σ ℓ_i D_i a`, its jets are free over `F` and fixed by translations,
and `α*` acts on `ℓ` by the constant invertible matrix `dα`.  Theorem A then follows from
`α^{n*}F = F^{Γ_n}` and closedness of stabilizers, and Theorem B from `F(ℓ^{(≥0)})^{H(C)} =
F^{H(C)}(ℓ^{(≥0)})`.

The quotient `Q = G/H` enters the statement only through its function field: `C⟨π(g)⟩` is the
differential field generated by `π*C(Q)`, and `π*C(Q) = F^{H(C)}` is the field of rational
functions constant on `H(C)`-cosets.  The Lean statements use `F^{H(C)}` directly, and the
assertion that `α` induces an automorphism of `Q` is formalized as `α*` restricting to a
bijection of `C(Q)`.
