# Arithmetic sign kernel of the full zero field

- **ID:** galois-zero-kummer-sign-kernel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Arithmetic image in the signed fibre groups; multiplicative relations.

Let `K` be the complete-fibre source, `L` the centered zero field,
`δ_q` its widths, and `D=K(δ_q² : all q)`. Work with nonzero widths.
Every offset `b_q=iδ_q` belongs to `L` and has square `−δ_q²∈D`.
The ordinates lie in `K`, so `L=D(b_q : all q)`.

## Theorem

`Gal(L/D)` is the closed group of all signs `ε_q∈{±1}` satisfying

```
∏_(q∈S) ε_q = 1 whenever ∏_(q∈S) (−δ_q²) is a square in D,
```

for every finite set `S` of nonzero-width zeros. Each compatible sign family
extends uniquely to the entire field.
The classification is both a group isomorphism and a homeomorphism onto the
closed subgroup of compatible signs. It replaces existential finite-field
compatibility for the sign kernel by explicit square-class relations.
No independence of the actual widths is assumed.

## Proof

The action on the square roots is faithful and Krull-continuous, hence has
closed image in the product of signs. Its finite-product character indexed
by `S` is trivial exactly when `∏ b_q∈D`, by infinite Galois correspondence.
Since `(∏ b_q)²=∏(−δ_q²)`, this is exactly the displayed square condition.
For the converse, let `H` be any subgroup of a finite sign cube and let `ε`
annihilate every finite-product character trivial on `H`. Expand

```
A(ε)=∑_(h∈H) ∏_i (1+ε_i h_i)
    =∑_S ε_S ∑_(h∈H) h_S.
```

A nontrivial character of `H` has zero sum: translation by an element with
sign `−1` negates the sum. Every surviving character has `ε_S=1`, hence
`A(ε)=A(1)>0`. If `ε∉H`, every product defining `A(ε)` has a zero factor,
a contradiction. Thus finite-product characters separate finite sign subgroups.

Apply this to each finite coordinate image of `Gal(L/D)`. Triviality of a
coordinate-product character is exactly the square condition above, so each
finite sign prescription is realized. The corresponding closed subsets of
the compact Krull group have the finite-intersection property; their full
intersection gives one automorphism realizing every prescribed sign.
Generation by the offsets proves uniqueness.

## Positive structure

`D⊆ℝ`. An odd product of the negative numbers `−δ_q²` cannot be a square
in `D`; thus every square-class relation has even parity. Uniform sign
reversal therefore annihilates every actual square-class relation.
Its fixed field remains `L∩ℝ`. Every source automorphism sends an offset to
an offset in the same ordinate fibre. Thus it permutes all squared offsets, making `D/K` normal. Restriction
`Gal(L/K) → Gal(D/K)` is continuous and onto; its kernel is exactly `Gal(L/D)`.
The relation-sign classification therefore identifies the full sign kernel
inside the original arithmetic group, with the complete Krull topology.
For continuity of the kernel embedding, a finite source subfield has a
primitive element. Its open stabilizer over `D` fixes the whole finite
subfield, since every element has a polynomial expression in that generator.

## Formalization

`GaloisTheoryOfZeros/TheKummerRelationsOfTheZeroWidths.lean`:
`compact_sign_image_iff`, `radical_product_trivial_iff_square`,
`radicalSignAction_unique_extension`, `widthSquareField_le_even`,
`widthSignRadicals_adjoin_top`, `widthKernelSignAction_unique_extension`,
`widthKernelSignHomeomorph`, `widthKernelSignAction_conjugation`,
`widthKernelRelation_even`, `widthSquareField_normal`,
`widthSquareRestriction_surjective`, `widthSquareRestriction_ker`,
`widthKernelSourceEmbedding_range`, and `widthKernelSourceEmbedding_continuous`.

Direct source audit passed. All seventeen transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Boundary

Actual square-class relations and splitting of the squared-width restriction
remain undetermined. The classification identifies the full sign kernel from
those relations, without identifying the entire arithmetic group with the
ambient signed-permutation product or proving any width nonzero.
