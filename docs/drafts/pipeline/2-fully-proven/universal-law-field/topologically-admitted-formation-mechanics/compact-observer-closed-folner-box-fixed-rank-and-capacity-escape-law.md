# Compact observer-closed Følner boxes, fixed-rank selection, and capacity escape

- **ID:** ULF-TAFM-11
- **Stage:** 2-fully-proven
- **Type:** THEOREM PACKAGE / THREE-ORGAN FUSION
- **Source:** ULF-TAFM-9 compact cofinal return; ULF-TAFM-10 formation Stokes/Følner and
  rank-width laws; hypertranscendence rank frontier
- **Status:** dependency-closed paper proof; Lean formalisation complete

## 1. Result

Compact recurrence simultaneously closes every fixed finite phase palette at arbitrarily large
common widths. If those widths support local formation boxes of fixed channel rank and uniformly
bounded edge-current capacity, the real bulk formation character vanishes.

The positive survivor is quantitative. If the character is nonzero and rank stays fixed, local
edge capacity must grow at least linearly along cofinally large observer-closed widths.

This is the first direct fusion of:

1. compact observer recurrence;
2. local Stokes/boundary-current conservation; and
3. hypertranscendence channel rank.

It replaces the slogan “hypertranscendence causes noncompactness” by an exact dichotomy: a
nonneutral compact-phase realization needs rank at width scale or unbounded local current.

## 2. Simultaneous cofinal return

Let `K` be a compact additive commutative group equipped with a translation-invariant extended
pseudometric. Fix a positive radius `r`, a finite rank `d`, and a palette

`α=(α₁,…,α_d)∈K^d`.

Equip `K^d` with its maximum product extended pseudometric.

### Theorem 11.1 — simultaneous compact return at cofinal widths

For every integer threshold `N`, there exists `n>N` such that

`dist(nα_j,0)≤2r` for every `j=1,…,d`.                              `(11.1)`

### Proof

The finite product `K^d` is again a compact translation-metric additive group. Apply the cofinally
large return theorem ULF-TAFM-9 to the single product point `α`. It gives `n>N` with

`dist_{K^d}(nα,0)≤2r`.

Every coordinate distance is bounded by the maximum product distance, proving `(11.1)`
simultaneously with one common `n`. ∎

The construction is stronger than selecting unrelated recurrence times for individual channels.

## 3. Fixed-rank observer-closed box selection

Assume `d>0`. Let `χ∈ℝ` be the constant bulk grade and `M∈ℝ` one local edge-current capacity.
Suppose every positive width `n` satisfying `(11.1)` admits a legal rank-`d` formation box whose
bulk and boundary laws imply

`n^d|χ|≤2Md n^(d-1)`.                                               `(11.2)`

This is exactly the ULF-TAFM-10 Stokes/Cheeger bound for a width-`n` box.

### Theorem 11.2 — fixed-rank compact-phase selection

Under `(11.2)`,

`χ=0`.                                                              `(11.3)`

### Proof

ULF-TAFM-10 cancels the positive factor `n^(d-1)` in `(11.2)` and gives

`n|χ|≤2Md`.                                                         `(11.4)`

Suppose `χ≠0`. Choose `N` so large that

`2Md<N|χ|`.

Theorem 11.1 supplies an observer-closed width `n>N`. Equation `(11.4)` then gives

`n|χ|≤2Md<N|χ|≤n|χ|`,

a contradiction. Hence `χ=0`. ∎

No density of the palette orbit, continuity of a recovered potential, or common fibre gauge is
used.

## 4. Capacity escape

Allow local edge-current capacity to depend on width, writing it as `M_n`. Suppose every
observer-closed width obeys

`n^d|χ|≤2M_n d n^(d-1)`.                                           `(11.5)`

### Theorem 11.3 — cofinal local-capacity lower bound

Beyond every threshold `N`, there is an observer-closed width `n>N` satisfying

`M_n≥n|χ|/(2d)`.                                                    `(11.6)`

### Proof

Choose `n` by Theorem 11.1. Cancel `n^(d-1)>0` in `(11.5)` to obtain
`n|χ|≤2M_nd`; divide by `2d>0`. ∎

If `χ≠0`, the right side of `(11.6)` tends to infinity along the cofinal return widths. Thus fixed
rank forces unbounded local current. If local current remains bounded, rank must grow at least
linearly with width by ULF-TAFM-10.

## 5. Exact dichotomy

For a compact-phase local formation law with nonzero bulk character, at least one of the following
must occur:

1. **rank escape:** no fixed finite palette carries cofinal formation; active channel rank grows at
   width scale;
2. **capacity escape:** elementary boundary-current magnitude grows at least linearly along
   cofinal closed widths;
3. **locality fracture:** bulk grade is not local divergence on the legal packet complex;
4. **packet fracture:** source doctrine does not admit the observer-closed boxes supplied by phase
   recurrence.

This is not a list of analogies. Items 1--4 are mutually auditable failures of a single theorem
interface.

## 6. Hypertranscendence reinterpretation

The corpus proves unbounded independent analytic formation rank in hypertranscendental source
organs. ULF-TAFM-10 showed rank alone is insufficient; the relevant ratio is rank/width.
ULF-TAFM-11 now proves why fixed rank is impossible under compact recurrence and bounded local
formation current.

Consequently:

- hypertranscendence is a possible supplier of rank escape, not a synonym for noncompactness;
- a valid source theorem must compare active analytic rank to legal packet width;
- if arithmetic source structure supplies sublinear rank, selection follows;
- if rank has positive density, that density is the exact chamber where open history can survive a
  compact observer without local-current blow-up.

This is a route-independent prediction for any finite-rank approximation organ, including spectral
truncations, finite prime palettes, finite jet towers, and finite observer graphs.

## 7. Hostile audit

1. **Simultaneity:** one product-group return time closes all coordinates; no diagonal subsequence
   handwave occurs.
2. **Cofinality:** ULF-TAFM-9 applies recurrence to `(N+1)α`, so widths exceed every threshold.
3. **Metric:** coordinate control follows from the finite-product maximum extended pseudometric.
4. **Rank zero:** selection assumes `d>0`; no division by zero is hidden.
5. **Sign:** absolute bulk current enters the Stokes inequality.
6. **Negative capacity:** legal edge bounds already force nonnegative capacity on any nonempty
   boundary; the algebraic selection proof does not need a separate sign premise.
7. **No false hypertranscendence claim:** infinite rank may still have zero rank/width density and
   select neutrality.
8. **No arithmetic smuggling:** literal prime/theta packet existence and source edge bounds are not
   asserted.
9. **No RH claim:** theorem supplies a producer architecture and a compulsory escape law, not the
   remaining arithmetic comparison.

## 8. Dependency audit

- Theorem 11.1: finite-product compactness, product maximum extended pseudometric, ULF-TAFM-9
  cofinal additive return.
- Theorem 11.2: Theorem 11.1, ULF-TAFM-10 box rank-width bound, Archimedean unboundedness of natural
  numbers.
- Theorem 11.3: Theorem 11.1, ULF-TAFM-10 box bound, division by positive `2d`.

All dependencies are unconditional and already paper-proved. No zero-location, density,
continuity, or unproved analytic premise occurs.

## 9. Corpus and literature boundary

The corpus contains compact character descent, finite observer recurrence, route-specific
fixed-rank escape, and the separate ULF-TAFM-9/10 laws. Search found no theorem fusing simultaneous
compact return with formation rank-width current selection. Standard external parents are product
recurrence, Følner boxes, network divergence, and isoperimetric profiles. No novelty criterion is
imposed.

## Gates

- [x] 0 → 1: statement and hostile tests frozen after corpus search
- [x] 1 → 2: dependency-closed simultaneous-return, fixed-rank selection, and capacity-escape proof
- [x] 2 → 3: Lean fusion over product compact phase
- [ ] 3 → 4: literal arithmetic finite-palette instantiation or rank-growth theorem
