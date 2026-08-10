# Simple-horizon rank-to-depth transmutation law — formalized

- **ID:** `simple-horizon-rank-to-depth-transmutation-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `simple-horizon-rank-to-depth-transmutation-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SimpleHorizonTransmutation.lean` |
| `GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology` | imported: augmentation, split, relation basis |
| `GaloisForLFunctions.HTGeometry.PhysicalCharacteristicIncidence` | imported: row-reduced Koszul homology |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The card's Lean note asked for existing Koszul and Vandermonde infrastructure to be reused after a
corpus search.  It exists and is cited, not rebuilt:

- `unitWeightedAugmentation` is the card's constraint covector `h` (2), `unitWeightedSection` its
  normalized leg (9), `unitWeightedRelations` the excess module `E`, `unitWeightedSplitEquiv` the
  splitting `R^N = R·v ⊕ E` used in the card's Koszul proof, and `unitWeightedRelationsBasis` its
  explicit free basis — which **is** card `(10)`;
- `rowReducedPhysicalKoszulHomologyEquiv` and `card_physicalKoszulSurvivingBasis` are the
  row-reduced Koszul homology and its rank count;
- `Matrix.det_vandermonde` and `exteriorPower.finrank_eq` come from mathlib.

## Formal theorem chain

All new declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `span_constraints_eq` — **cards `(1)`, `(6)`**: constraints with a common uniformizer and unit
   leading coefficients already generate `(a)`; the underived ideal saturates at one constraint.
2. `finrank_unitWeightedRelations` — **card `(10)`, boxed**: the excess module is free of rank
   `N − 1`, the type-`A_{N-1}` root module, from the corpus basis.
3. `finrank_exteriorPower_unitWeightedRelations` — **card `(8)`**: `rank ⋀^j E = binom (N-1) j`.
4. `card_koszul_excess`, `koszulExcessEquiv` — **cards `(7)`, `(8)`**: in the normalized frame the
   sequence is row-reduced, and its degree-`k` Koszul homology is `binom (N-1) k` copies of the
   Cartier quotient — the card's `k ⊗ ⋀^• E`.
5. `sheetObserver`, `sheetObserver_eq` — **cards `(5)`, `(14)`**: the observer factors as the
   Vandermonde of the leading units times `diag(1, a, …, a^{N-1})`.
6. `range_diagonal_mulVecLin`, `cokerSheetObserverEquiv` — **cards `(11)`, `(12)`, boxed**: with an
   invertible Vandermonde factor the observer cokernel is the persistence staircase
   `⊕_j R/(a^j)`.
7. `sum_val_eq_choose`, `det_sheetObserver` — **cards `(15)`, `(16)`**: the orientation order is
   `binom N 2`.
8. `constraint_sub`, `disc_constraints` — **card `(16)`**: the discriminant order is twice that,
   `N(N−1)`.
9. `grade_dimension` — **card `(13)`**: the `a`-adic grade dimensions are `N−1, …, 1`.
10. `successor_bars` — **card `(17)`, boxed**: one more sheet appends a bar of length `N`.

Together items 1–10 are the transmutation dictionary `(18)`: extra underived codimension `0`,
derived excess rank `N − 1`, maximal observer jet depth `N − 1`, orientation order `binom N 2`,
discriminant order `N(N−1)`.

## Scope

The card's §"Scope and falsifiers" records that colliding residues, higher common vanishing order
and nonmonogenic observers fall outside the normal form; those are stated as hypotheses
(`IsUnit (vandermonde …).det`, unit leading coefficients) rather than assumed away.  The card states
plainly that this is a local normal form and not a source selector, and cannot force RH.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/SimpleHorizonTransmutation.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation          # green
```
