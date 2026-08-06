# Local law bridged into mathlib's `Ring.ord` vocabulary (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2).

## New module

`GaloisForLFunctions/HTGeometry/RingOrdRamification.lean`

`Ring.ord R x := Module.length R (R ⧸ span {x})` is mathlib's order of vanishing in a Noetherian
local ring, and `AlgebraicGeometry.ord` at a codimension-one point is *defined* as
`Ring.ordFrac (X.presheaf.stalk z)`.  So `Ring.ord` is the interface any globalisation of the
card's law must speak.  Glue lemma: `Ring.ord_eq_addVal` (DVR case).

| statement | declaration |
|---|---|
| ramification scales `Ring.ord` | `ord_map_eq_mul_ramification` |
| local law in `Ring.ord` vocabulary | `ord_pullback_form` |
| uniformizer has order one | `ord_uniformizer` |
| order zero characterises units | `isUnit_of_addVal_eq_zero` |
| **local hom ⟹ ramification index ≥ 1** | `one_le_ord_map_uniformizer` |

All axiom-clean.  `lake build GaloisForLFunctions.HTGeometry` green (14910 jobs); lint clean.

## A correction worth remembering

I first tried to prove `e ≥ 1` from **injectivity** of `φ : A →+* B`.  That is **false**: an
injective ring hom of DVRs can send a uniformizer to a unit — e.g. `k[x]_(x) ↪ k[x,x⁻¹]_(x-1)`,
where `x` is a unit downstream.  The correct hypothesis is **locality** (non-units go to
non-units), which is exactly what a dominant morphism of varieties supplies at a point of the
image.  `one_le_ord_map_uniformizer` therefore takes `hlocal`, not `hinj`.

## Card status

Formal: (7); (8) and (9) for regular *and* rational forms, both the `e` and the `e−1`; the
`1 ≤ e` hypothesis; steps 3, 4 (sharpened: one ramified place per cycle suffices), 5 and
conclusions (2)–(6).  The law is now stated both in `addVal` and in `Ring.ord` vocabulary.

Remaining — globalisation only, two concrete mathlib gaps:
1. divisor of a rational function as a cycle with **finite support**
   (`AlgebraicGeometry/AlgebraicCycle/Basic.lean` is a stub);
2. **pullback law for `AlgebraicGeometry.ord` along a morphism** — needs the stalk map of a
   dominant morphism, the induced function-field map, and DVR-ness of the stalks (normality).
   `ord_map_eq_mul_ramification` is the ring-level content already in hand; what is missing is
   purely the scheme-theoretic transport.

Plus the identification of a rational top form with a coframe top wedge.  `N^1`/int-amplification
is needed much less than the card assumes after the sharpened step 4.
