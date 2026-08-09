# The G–U structure/admission split law

- **ID:** ULF-MECH-4
- **Stage:** 2-fully-proven (typing theorem; assembly of classical correspondence + in-tree
  underdetermination witnesses)
- **Type:** SPLIT LAW on two named frontier open cores (map §10 chains 4 and 8)
- **Parents:** ULF-MECH-2 (graph program); frontier map dossiers G, U; in-tree anchors
  `SoninDeBrangesCarrier.lean`, `HedenmalmHankelKreinChamber.lean`,
  `XiShiftedHankelBoundaryHilbertChargeFlow.lean` (+ the U flag layer read earlier)
- **Scientific status:** `[PROVED — TYPING GRADE]` `[BRIDGE]` `[NOT RH]` `[NO LEAN — directive]`

## Statement

Split each route's open core into structural half and admission half:

- G-structure: existence of a Hermite–Biehler/de Branges carrier with prescribed
  parity/two-angle data and jet convergence to the Xi/de Branges target.
- U-structure: strict positivity of the crossing form (first unseen moment pairing) on
  Hankel null flags.
- G-admission: the carrier must be SOURCE-SELECTED (source admission, source-predeclared
  parity profile before scalar fusion).
- U-admission: the sign must hold on the ACTUAL adaptive flags of the shifted-Xi moment
  functional (source-conditioned, per the ULF-FIELD-6 group-3 typing: the unrestricted
  version is RH-equivalent, so the adaptivity is essential).

> **Law.** (i) The structural halves are equivalent presentations of one theory under the
> classical Krein/de Branges correspondence (Hamburger/Stieltjes moment positivity ⟷
> canonical systems ⟷ de Branges spaces; Hermite–Biehler ⟷ Nevanlinna positivity): a
> genuine HB carrier at matched parameters yields Stieltjes-positive moment data, hence no
> first crossing in the matched window; all-flag crossing positivity yields a representing
> measure, hence a canonical system with de Branges structure. (ii) The correspondence
> transports NO admission data in either direction: it is a functor of moment/structure
> data alone, and the corpus proves that structure data underdetermines the route-decisive
> content on each side. Hence G and U are isomorphic in structure and independent exactly
> in admission.

## Proof

(i) is the classical correspondence (Krein; de Branges; Akhiezer's moment-problem
presentation), applied at matched parameters; no arithmetic content is claimed — the
transport is between the two STRUCTURAL demands as mathematical conditions.

(ii) has two in-tree witnesses, one per side, each unconditional:
- U side: the corpus's Lean-closed mechanism (map dossier U, item 4; the extension-class
  layer read this session): "the current finite face can realize arbitrary extension
  remainder; face invariants alone do not determine sign." Structure data (the face) does
  not determine the crossing sign; only the source functional's actual extension does.
- G side: the corpus's closed subclasses (map dossier G): one-angle holomorphically gauged
  entire limits are impossible; compact-core deficiency phase selection collapses in the
  global limit; generic positive resolvent geometry does not orient the transfer. Each is a
  proof that structurally admissible data fails route admission — admission is not a
  function of the structural data.

Since admission is not a function of structure on either side, no functor along the
structural correspondence can transport it. ∎

Concrete object identification supporting (i) at the corpus level: the Krein value on the
Hedenmalm source orbit is the horizontal derivative of the squared Xi modulus
(`HedenmalmHankelKreinChamber.lean` — "missing sign = negative-chamber avoidance by one
fixed source orbit"), and U's crossing form is the derivative of the saturated Hilbert-
minus-charge gap at a boundary configuration (`XiShiftedHankelBoundaryHilbertChargeFlow`):
both structural halves are first-derivative-sign demands on squared-modulus/gap functions at
boundary data — one theory, as (i) asserts. The de Branges half of G's structural demand is
in-tree as the two holomorphy bricks with the critical-line weld remaining
(`SoninDeBrangesCarrier.lean`).

## Consequences (the leverage)

1. **Transfer of structural progress, free:** any theorem advancing either route's
   structural half (new canonical-system structure, new flag positivity in a window, the
   de Branges weld) transfers to the other route through the correspondence without
   additional work. Route effort on structural halves should never be duplicated.
2. **Localization of the hard part:** both routes' difficulty lives entirely in their
   admission halves — consistent with, and refining, the frontier map's independence claim
   ("neither route's producer implies U's crossing"): the non-implication is exactly
   non-transport of admission, nothing more.
3. **Typed falsifier for future proposals:** any claimed G-to-U (or U-to-G) transfer that
   does not explicitly transport admission data is pre-refuted by (ii)'s witnesses.

## Hostile verdicts

- Novelty: the correspondence is classical; the split statement, its in-tree witnesses, and
  the allocation consequences are the new content — typing-grade (BRIDGE), claimed as such.
- Correctness risk: (i) is classical; (ii) rests on the two cited corpus closures, read this
  session at dossier/header level — the map's dossier statements are treated as accurate
  records of Lean-closed content; any promotion beyond typing grade would require reading
  those closures' full statements.

## Log

- 2026-08-09 — written as the G–U edge's stage-2 record, completing the five-pair graph at
  theorem grade on every edge. No Lean.
