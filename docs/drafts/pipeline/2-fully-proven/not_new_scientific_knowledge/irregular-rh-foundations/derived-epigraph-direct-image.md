# Bounded-below derived direct image for exponential epigraph addition

- **ID:** derived-epigraph-direct-image
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** irregular microlocal Riemann--Hilbert foundations
- **Statement:** For universe-0 sheaves of integer modules, direct image along every continuous map preserves injective objects and therefore has a bounded-below right-derived functor; in particular this gives `Rμ_*` for proper fiberwise addition of continuous exponential epigraphs.

## Goal
Construct the first honest derived operation in the exponential-support chain. Keep exact boundary: this is `Rf_*`; proper epigraph addition makes it the relevant proper-map case, but no general nonproper `Rf_!`, derived tensor, `Rμ_!!`, enhanced quotient, ind-sheaf, D-module, or RH claim is made.

## Gates
- [x] 0 → 1  in-progress: statement is well-typed; parent theory and local APIs audited; no corpus duplicate found
- [x] 1 → 2  fully-proven: complete paper proof below survived hostile review
- [ ] 2 → 3  formalized: exact theorem, targeted build, and new-declaration axiom audit pass; authoritative repository lint remains blocked by unrelated unreachable modules
- [ ] 3 → 4  publication-ready: not targeted; established bridge mathematics

## Labels and frontier

- `[LITERATURE]` Derived direct image of sheaves is standard; enhanced irregular RH uses derived proper direct image and convolution, not an underived substitute.
- `[CORPUS]` `HTGeometry.rightDerivedFunctorPlusCompIso` proves a generic composition law once additive/derived/injective hypotheses exist.
- `[CORPUS]` `RHTower.deningerSheafPullback_preservesFiniteLimits` proves the analogous inverse-image exactness for `AddCommGrpCat`.
- `[CORPUS]` `ordinaryEpigraphConvolutionFunctor` supplies the underived integer-module support map and tensor construction.
- `[OPEN CORE]` Derived tensor and the enhanced `Rμ_!!` quotient remain absent after this claim.

## Paper proof

`[PAPER-PROVED]` Let `f : X → Y` be a continuous map of universe-0 topological spaces and let `Sh_Z(X)` denote sheaves valued in `ModuleCat ℤ`.

1. `Sh_Z(X)` and `Sh_Z(Y)` are Grothendieck abelian categories. Hence both are abelian, have enough injective objects, and admit standard bounded-below derived categories.
2. Inverse image `f^* : Sh_Z(Y) → Sh_Z(X)` is the sheafification of the site pullback induced by inverse image of opens. That functor on opens is representably flat, so the sheaf pullback construction preserves finite limits. Thus `f^*` preserves monomorphisms.
3. Sheaf inverse image is left adjoint to direct image: `f^* ⊣ f_*`.
4. A right adjoint of a monomorphism-preserving functor preserves injective objects. Therefore `f_* : Sh_Z(X) → Sh_Z(Y)` preserves injective objects.
5. Direct image is additive: its action on sheaves and sheaf morphisms is induced pointwise by presheaf precomposition, so it preserves addition of morphisms.
6. Since `Sh_Z(X)` has enough injectives and both source and target derived categories exist, the injective derivability construction defines `Rf_* : D^+(Sh_Z(X)) → D^+(Sh_Z(Y))` unconditionally.
7. For continuous phases `φ,ψ`, the restricted fiberwise addition map between their paired epigraph and the epigraph of `φ+ψ` is already proved continuous and proper. Applying steps 1--6 gives its bounded-below right-derived direct image. Properness is extra geometric information about this particular map; it is not used to manufacture a nonproper `f_!`.

Every step is functorial and source-independent. No Xi divisor, zero, RH predicate, or unproved route hypothesis enters.

## Hostile review

- **Possible circularity:** None; construction is generic sheaf theory and does not mention RH.
- **Possible overclaim:** `Rf_*` is not renamed `Rf_!`. Equality with proper-support direct image is asserted only as standard semantics for this already proper map, not formalized as a separate functor equality.
- **Possible hidden resolution premise:** None; enough injectives follows from the Grothendieck-abelian sheaf category, and the bounded-below derived category uses the standard construction.
- **Possible coefficient error:** Coefficients are `ModuleCat ℤ`, retaining tensor over integers; cartesian `AddCommGrpCat` monoidal structure is not used.
- **Verdict:** `BRIDGE`; proof is dependency-closed. Remaining obstruction is derived tensor/K-flat machinery, not right-derived direct image.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Not applicable.
- **Strongest positive survivor:** Not applicable.
- **New insight:** Right-derived pushforward is available before derived tensor; the first genuine derived bottleneck is the tensor/K-flat side of convolution.
- **Status:** Dependency-closed paper proof and Lean module complete; repository-wide lint blocker prevents Stage-3 promotion.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesDerivedEpigraphDirectImage`
- Main declarations:
  - `intModuleSheafPullback_preservesFiniteLimits`
  - `intModuleSheafPushforward_preservesInjectiveObjects`
  - `rightDerivedSheafPushforward`
  - `derivedEpigraphPushforwardFunctor`
- Direct module check: PASS.
- Targeted module build: PASS.
- New-declaration axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

## Log
- 2026-08-24 — created after corpus and parent-theory audit; exact paper proof recorded in Stage 1.
- 2026-08-24 — hostile audit passed with `BRIDGE` verdict; moved to Stage 2 before Lean work.
- 2026-08-24 — exact Lean formalization, targeted build, and new-declaration axiom audit passed.
