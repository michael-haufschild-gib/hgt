# Finite Wick-Contracted Interaction Matroid

- **ID:** WCDMF-FINITE
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / INFRASTRUCTURE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** `../../1-in-progress/wick-contracted-differential-matroid-field.md`
- **Statement:** Labeled higher connected reporters carry a canonical algebraic matroid contracted by the face-complete Gaussian base; its rank is relative transcendence degree, Wick-algebraic reporters are loops, algebraic counterterm refinements preserve the entire signal matroid, injective reporter embeddings preserve it, and an infinite vertical jet restriction is free exactly for a hypertranscendental reporter.
- **Scientific status:** `[PROVED HERE] [PARENT MATROID THEORY] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Goal

Replace the rank-only finite Wick--Kolchin skeleton by the exact labeled matroid required by the proposed quantum matroid field. The theorem must preserve distinct probe labels even when their evaluated responses coincide, and it must show full circuit-level counterterm neutrality rather than equality of one numerical rank.

## Setup

Let `K ⊆ L` be a field extension. Let `G` and `S` be disjoint finite label sets, and let

```text
ev : G disjoint-union S -> L
```

evaluate the Gaussian/face labels and higher connected signal labels. Let `A_K(L)` be the algebraic matroid on `L`, and pull it back to the labeled ground set:

```text
M_ev = A_K(L).comap(ev).                                    (1)
```

The comap condition declares a labeled subset independent exactly when its evaluated values are algebraically independent and the evaluation map is injective on that subset. Thus coincident labels become parallel rather than being erased.

Define the finite interaction matroid

```text
I_K(ev;G,S) = (M_ev / G) | S.                               (2)
```

All ranks below are finite ordinary matroid ranks.

## Theorem `[PROVED HERE]`

### 1. Relative-rank law

For every `T ⊆ S`,

```text
r_I(T)
  = trdeg_K K(ev(G),ev(T)) - trdeg_K K(ev(G)).               (3)
```

Here the right side is the transcendence degree of the finitely generated subfields, equivalently the rank difference of the corresponding finite value sets in `A_K(L)`.

### 2. Wick-collapse law

If every `ev(s)`, `s ∈ S`, is algebraic over `K(ev(G))`, then every signal label is a loop of `I_K(ev;G,S)`. Equivalently, `(2)` is the loopy matroid on `S`.

### 3. Full counterterm neutrality

Let `C` be a further finite label set disjoint from `G` and `S`, extend `ev`, and assume every `ev(c)` is algebraic over `K(ev(G))`. Then

```text
(M_ev / (G union C)) | S = (M_ev / G) | S.                  (4)
```

Thus algebraic counterterms preserve every independent set, circuit, closure, and rank on the signal labels, not only the total Wick-reduced rank.

### 4. Embedding covariance

Let `phi : L -> E` be an injective `K`-algebra homomorphism. Replacing `ev` by `phi ∘ ev` leaves the labeled matroid `(1)` unchanged, hence leaves `(2)` unchanged. If the labels are also relabeled by a bijection, that bijection is a matroid isomorphism. When `L,E` are differential fields and `phi` commutes with the derivations, the isomorphism preserves derivative order on jet labels.

### 5. Vertical hypertranscendence law

Let `(F,D) ⊆ (L,D)` be a differential field extension and `x ∈ L`. Pull `A_F(L)` back along

```text
j_x : natural-numbers -> L,   n |-> D^n x.                  (5)
```

The resulting finitary matroid on the vertical jet labels is free exactly when `x` is hypertranscendental over `F`.

## Proof

### Proof of 1

For any matroid `M`, contraction satisfies

```text
r_(M/G)(T) = r_M(T union G) - r_M(G)                         (6)
```

when the sets are finite and disjoint. Restriction to `S` does not change ranks of subsets of `S`.

For a comap, the rank of a labeled set `U` is the rank in the target matroid of `ev(U)`: choose one preimage label for each element of an independent subset of `ev(U)` to obtain the reverse inequality, while the image of every independent labeled subset is independent. In the algebraic matroid the finite rank of a value set is the transcendence degree of the field it generates over `K`. Substituting these two facts into `(6)` gives `(3)`. ∎

### Proof of 2

The algebraicity hypothesis says each signal label lies in `closure_(M_ev)(G)`. The loops of a contraction are

```text
loops(M/G) = closure_M(G) minus G.                           (7)
```

Since `G` and `S` are disjoint, every signal label is therefore a loop of `M_ev/G`, and remains a loop after restriction to `S`. ∎

### Proof of 3

The hypothesis gives `C ⊆ closure_(M_ev)(G)`. After contracting `G`, equation `(7)` makes every element of `C` a loop. Contracting loops is the same as deleting them. Because `C` is disjoint from `S`, deleting `C` has no effect after restriction to `S`. Using associativity of contraction,

```text
M_ev/(G union C) = (M_ev/G)/C,
```

and the preceding loop/deletion argument yields `(4)`. ∎

Equivalently, for every `T ⊆ S`, closure of `G` implies

```text
r(G union C)=r(G),
r(T union G union C)=r(T union G),
```

so the two contractions have identical rank functions on `S`.

### Proof of 4

An injective base-field algebra map preserves and reflects polynomial relations. Hence a finite family in `L` is algebraically independent over `K` exactly when its image in `E` is. The injectivity clause in the labeled comap is also unchanged. Therefore the two comap matroids have exactly the same independent sets. Contraction and restriction preserve equality. If `phi(Dy)=D(phi(y))`, induction on `n` gives `phi(D^n y)=D^n(phi(y))`, so the same identity respects jet labels. ∎

### Proof of 5

By definition, `x` is hypertranscendental over `F` exactly when its complete derivative family

```text
{D^n x : n >= 0}
```

is algebraically independent over `F`. Algebraic independence of the complete family means every finite jet subset is independent. By the comap definition this is exactly freeness of the finitary matroid pulled back along `(5)`. ∎

## Consequences for QFT

1. The face-complete Wick--Kolchin rank is the rank shadow of a canonical circuit-bearing matroid.
2. A generalized free field, a finite polynomial Wick composite, or any higher reporter algebraic over the completed Gaussian face field gives only loops after Wick contraction.
3. Admissible algebraic counterterms cannot change the exact signal circuits. A physical locality theorem is still needed to prove that all renormalization-scheme changes lie in this neutral class.
4. HT interaction is not ordinary HT. It is a free vertical flat in a higher connected sector after contraction by the full Gaussian face field.
5. The theorem is finite and presentation-relative. The directed source category, quotient coherence under base refinement, enriched valuation/phase data, and an interacting continuum example remain open.

## Novelty gate

This theorem is a direct assembly of standard facts about algebraic matroids, comaps, contraction, closure, and differential independence. The full-matroid statement is stronger and more useful than the already formalized rank equality, but it does not introduce a new mathematical mechanism. It is classified as infrastructure and not new scientific knowledge.

## Lean target

The existing corpus already proves the finite rank shadow and algebraic-counterterm rank neutrality in `WickKolchinProfile.lean`. A justified Lean extension would formalize only the missing full structure:

```text
wickContractedInteractionMatroid
wickContractedInteractionMatroid_eq_loopyOn_of_signal_subset_closure
wickContractedInteractionMatroid_eq_of_counterterms_subset_closure
```

Mathlib already exposes contraction associativity, loops of contraction, contraction of loops as deletion, restriction/contraction commutation, and `eRk_comap`. Do not add theorem-name wrappers for the relative-rank or vertical-HT facts already represented elsewhere in the corpus.

The missing full structure is now implemented in
`formal/GaloisForLFunctions/HTGeometry/WickContractedInteractionMatroid.lean`. The exact-module build and direct touched-file check pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both the loopy-collapse and full-counterterm-neutrality theorems. The global formal lint currently fails on numerous unrelated concurrently added RHTower and HTGeometry modules that are unreachable from their umbrellas; this new module is imported by the HTGeometry umbrella and is not among the lint failures. The card therefore remains at stage 2 until the shared-tree lint gate is globally green.

## Gates

- [x] 0 → 1: labeled comap/contraction object and exact claims stated
- [x] 1 → 2: complete finite proof given above
- [x] novelty gate: infrastructure / not new scientific knowledge
- [ ] 2 → 3: full-matroid Lean equality formalized and exact checks pass; shared-tree global lint remains red on unrelated concurrent modules
- [ ] 3 → 4: not a standalone publication result

## Log

- 2026-07-17 — created directly in 2-fully-proven after proof. The exact counterterm result is equality of the restricted contracted matroids, strengthening the existing rank-only formal theorem.
