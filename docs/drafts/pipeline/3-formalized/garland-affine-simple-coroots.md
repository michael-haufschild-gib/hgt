# Affine simple coroots inside the actual loop group

- **Stage:** 3-formalized
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](../1-in-progress/garland-loop-eisenstein-over-q.md)
- **Target:** Construct the simple coroots from the actual lifted root words,
  prove `h₀(a)=z(a)h₁(a⁻¹)`, and identify the resulting Cartan torus.

## Dependency and novelty audit

The affine root/weight model already uses `h₀=c-h₁`. The concrete central
extension must prove this relation, rather than assume that its central
coordinate has the desired sign. The proved inverse tame normalization and
constant/uniformizer symbol formula supply its algebraic input. The result is
the standard untwisted affine `A₁` coroot relation, not new science. See Liu,
*Eisenstein Series on Loop Groups*, §3.1, <https://arxiv.org/abs/1103.4212>.

Corpus searches exposed finite matrix elementary-factorization identities, but
no previously constructed affine simple-coroot lifts in this extension.

## Dependency-closed paper proof

Write `L(s),U(s)` for the canonical lower/upper root lifts already proved to
be injective additive homomorphisms. For a field unit `t`, put

`W(t)=L(t)U(-t⁻¹)L(t)`.

Its underlying matrix is `[[0,-t⁻¹],[t,0]]`. The two cocycle factors in this
word vanish: in the first multiplication the first symbol argument is one;
in the second multiplication both arguments are one. Thus `W(t)` is exactly
the zero-central-coordinate section of this matrix. Its inverse is `W(-t)`:
the inverse matrix is as stated and the inverse cocycle is the opposite-pair
symbol `{-t⁻¹,t⁻¹}=0`.

For units `a,b`, matrix multiplication gives

`W(ab) W(b)⁻¹ ↦ diag(a⁻¹,a)`.

The central symbol is

`{b⁻¹,-a/b} = {b⁻¹,a}+{b⁻¹,-b⁻¹} = {a,b}`.

Hence in every pushout of the proved Milnor-valued cocycle,

`W(ab) W(b)⁻¹ = z(T{a,b}) s(diag(a⁻¹,a))`.

Specialize to Laurent series, with a constant coefficient unit `a` and `b=X`.
The already proved formula `T{a,X}=a` gives

`h₀(a) := W(aX)W(X)⁻¹ = z(a) s(diag(a⁻¹,a))`.

For the finite simple coroot use
`h₁(a):=W(a⁻¹)W(1)⁻¹=s(diag(a,a⁻¹))`, with coefficients viewed as constants.
Both defining words use the actual root embeddings. Thus
`h₀(a)=z(a)h₁(a⁻¹)` with the required central sign.

Constants have integer valuation zero, so the tame symbol of any two constants
is one. Therefore `h₁` is a multiplicative homomorphism, as is `h₀` by the
displayed central-factor formula. The map `(c,a)↦z(c)h₁(a)` from `Fˣ×Fˣ`
is a homomorphism. If its value is one, matrix projection forces `a=1`, then
injectivity of the central embedding forces `c=1`. It is therefore injective.
In these central/finite coordinates, `h₀(a)h₁(b)=z(a)h₁(b/a)`, which identifies
the root-data central coordinate with the actual Cartan torus.

## Status

Paper proof and Lean formalization complete. This constructs the Cartan
subgroup and its coroot coordinates. Iwasawa decomposition and the arithmetic
Eisenstein series remain open.

| Module | Main declarations |
| --- | --- |
| `SL2WeylLifts` | `kubotaCocycle_weylLower_relative`, `SL2SymbolExtension.weylLower_eq_rootWord`, `SL2SymbolExtension.weylLower_relative` |
| `AffineA1Coroots` | `laurentTameSymbol_constants`, `LoopSL2.finiteCoroot`, `LoopSL2.affineCoroot`, `LoopSL2.affineCoroot_eq_central_finite`, `LoopSL2.cartanEmbedding_injective`, `LoopSL2.simpleCoroots_eq_cartan` |

Both modules passed final direct source checks with `lake --old env lean`,
without warnings. The saved [transitive axiom audit](garland-affine-simple-coroots-audit.txt)
contains only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are
wired into the loop Eisenstein umbrella; no umbrella build was run.
