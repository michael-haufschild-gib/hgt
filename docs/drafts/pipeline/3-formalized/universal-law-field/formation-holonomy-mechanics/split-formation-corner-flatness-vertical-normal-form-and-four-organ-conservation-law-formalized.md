# Split-formation corner flatness and the vertical normal form — Lean certification

- **ID:** ULF-FHM-1
- **Paper card:** `split-formation-corner-flatness-vertical-normal-form-and-four-organ-conservation-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.SplitFormationCornerFlatness`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## §1 Arbitrary-category split formations (Theorem 1.1)

Stated for an arbitrary `CategoryTheory.Category`, with `f i ≫ p i = 𝟙 X`:

* `cornerIdem`, `cornerTransport` — `(SFH.2)`;
* `cornerIdem_idem` — `(SFH.3)`;
* `cornerTransport_comp` — `(SFH.4)`, strict composition, i.e. corner flatness;
* `cornerTransport_loop` — `(SFH.5)`, every canonical loop is the local corner identity;
* `cornerIdem_comp_cornerTransport`, `cornerTransport_comp_cornerIdem` — `(SFH.6)`.

These seven declarations depend on **no axioms at all** (`#print axioms` reports "does not depend
on any axioms"), which is the sharpest possible form of Corollary 1.2: common recovery cannot
generate holonomy, independently of topology, probability, positivity, dimension, or
presentation.

## §2 The linear split chart (Lemma 2.1)

`vertical p = ker p` is `(SFH.7)`; `splitAssemble` is `(SFH.8)`; `splitSplit` is `(SFH.9)` (its
second component is proved to land in `ker p`); `splitAssemble_splitSplit`,
`splitSplit_splitAssemble` and `splitChart` give the canonical isomorphism `Z ≅ X ⊕ ker p`, with
`splitChart_apply`, `splitSplit_fst`, `splitSplit_snd` the computation rules `(SFH.10)`.

## §3 Base-compatible comparisons (Theorem 3.1)

`BaseCompatible` is `(SFH.11)`; `verticalProj` is the vertical component;
`verticalTransport` is `(SFH.12)`; `splitChart_comparison` is **`(SFH.13)`** and
`verticalTransport_unique` is its uniqueness clause.  `verticalTransport_eq_zero_iff` is
**Corollary 3.2**: a comparison equals the canonical recover-then-form map exactly when its
vertical transport vanishes.  `BaseCompatible.comp`, `baseCompatible_id`,
`verticalTransport_comp`, `verticalTransport_id` are the functoriality used by **Corollary 4.2
`(SFH.17)`**: along any loop the base returns exactly and the vertical part is the ordered product
of the edge transports.

## §4 Three-organ fusion defect (Theorem 4.1)

`fusionDefect` is `(SFH.14)`; `recover_comp_fusionDefect` and `fusionDefect_comp_form` are
**`(SFH.16)`**; `reporter_comp_fusionDefect` is the Loop C refutation — every reporter factoring
through recovery annihilates the defect; `splitChart_fusionDefect` is **`(SFH.15)`**: the defect is
purely vertical with vertical part `L_{kj}L_{ji} − L_{ki}`.

## §5 Four-organ conservation (Theorem 5.1)

`fourOrgan_conservation` is **`(SFH.18)`**; since every defect is purely vertical by `(SFH.15)`,
this is also `(SFH.19)`.

## Loop E refutation

`comparisonOfVertical`, `baseCompatible_comparisonOfVertical` and
`verticalTransport_comparisonOfVertical` show that **every** vertical transport is realized by a
base-compatible comparison, so arbitrary loop products occur and vertical holonomy alone selects
nothing.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/SplitFormationCornerFlatness.lean
```

Elaborates with no errors and no warnings.  `#print axioms` on all 41 public declarations reports
only `propext`, `Classical.choice`, `Quot.sound` (and nothing at all for the categorical section).
The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField` and by
`GaloisForLFunctions.HTGeometry`.

## Still open (not proved theorems)

The card's last two gates: three literal heterogeneous corpus realizations, and a
source-generated positive vertical-work theorem.  Both are construction burdens the card states as
future work.
