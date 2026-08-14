# HT stage-2 → stage-3 sweep (`2-fully-proven/new_scientific_knowledge/ht`)

State as of 2026-08-14 (late).

## PROMOTED to `3-formalized` (each with a `-formalized.md` certificate)
- `nonautonomous-rational-first-order-tail-orbifold-law` (card 6)
- `nonautonomous-isogeny-tail-time-splitting` (card 4) — complex-torus column in every dimension;
  see `mem:ht-cards/card4-complex-torus-stack-plan`
- `hypertranscendental-pair-localization-noncompression` (card 2) — canonical pair carrier
  `F_e = ∏_{k∉e} Δ_{τ_k} Ψ` is the face with surviving set `e`; HT on `e`, DA on every other pair;
  direct sum in differential-independence form (`PairFaceNoncompression.lean`).  The exact-image
  parent turned out to be unnecessary.

## REMAINING (3 cards) — each blocked on ONE mathlib-scale classical theorem

### `nonautonomous-rational-complete-tail-orbifold-classification` (card 5)
Everything formal except the **Lie–Cartan/Casale classification** of proper transitive rational
differential groupoids on a curve into `G1/G2/G3`.  New this session:
`RationalPrefixDifferentialAdjoin.lean`, `RationalPrefixDeckDescent.lean`,
`NonautonomousCompleteTailOrbifoldLaw.lean`.
NEXT: build the pseudogroup layer.  Entry point: a rational differential groupoid on `P¹` as the
invariance groupoid of a differential-rational structure; the three model structures are already
formal as pullback laws (`affineConnection_projectivization_transport`,
`projectiveConnection_exponentDiscriminant_transport`, tensor transport in
`VerticalSymbolTransformation`).

### `irrational-power-canonical-products-…-gevrey-slope-rigidity` (card 3)
Formal: `(1)`, `(8)`, `(9)`–`(12)`, `(10)`, §4.1–4.4, **`(14) ⟹ (15)`** (new:
`AsymptoticExpansionAlgebra.lean` — Poincaré expansions form an injective algebra map into `ℂ⟦t⟧`),
and §5's Newton-slope rationality.
OPEN: the **Barnes derivative-compatible expansion `(4)`–`(6)`** and the **Sibuya–Ramis exact
Newton-slope theorem**.

### `helson-universal-ht-arbitrary-divisor-orthogonality` (card 1)
Abstract layer formal; Pong's HYPOTHESIS discharged (`PrimeSupportNotFinitelyGenerated`).
OPEN: the CONCLUSIONS of Pong 5.9, Andersson Thm 5, Saksman–Webb/Seip.

## Working rule
The user's directive is explicit: research-level construction and mathlib-scale gaps are to be
BUILT, not parked.  Only mathematical impossibility stops a card.  Do not promote a card whose
residue is still open — record the residue precisely on the card instead, and keep building.
