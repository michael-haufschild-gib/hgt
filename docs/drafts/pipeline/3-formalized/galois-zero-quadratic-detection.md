# Quadratic detection of centered conjugation

- **ID:** galois-zero-quadratic-detection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Location of conjugation; full arithmetic character group.

Let `K` be the complete-fibre source field, `L` the centered zero field,
`c` its conjugation, `E=L∩ℝ`, and `F` the signed-width field.

## Theorem

A continuous character `χ:Gal(L/K)→{±1}` with `χ(c)=−1` exists exactly when
`Gal(F/K)→Gal(E/K)` splits continuously and some width is nonzero.
Every detecting character has a nonzero purely imaginary eigenradical
`b∈L` with

```
σ(b)=χ(σ)b,       b²∈K,
L^ker χ=K(b),    [K(b):K]=2.
```

All nonzero eigenradicals for the same character differ by a source unit.
The map `σ↦(σ|E,χ(σ))` gives both a group isomorphism and a homeomorphism
`Gal(L/K) ≅ Gal(E/K) × C₂`, taking `c` to `(1,−1)`.
The criterion covers all continuous quadratic characters, including those
not obtained from complete-block products. No finiteness of `L/K` is assumed.

## Proof

For a detecting character, its kernel is closed. Infinite Galois correspondence
identifies the fixing subgroup of its fixed field with that kernel. Since
`χ(c)=−1`, some `d` in the fixed field satisfies `c(d)≠d`. Set `b=d−c(d)`.
Centrality and `c²=1` give `c(b)=−b`. Elements of the kernel fix `b`;
every other automorphism differs from one in the kernel by `c`, so
`σ(b)=χ(σ)b`. Hence every source automorphism fixes `b²`, giving `b²∈K`.
For two nonzero eigenvectors of the same character, their quotient is fixed
by the entire Galois group and belongs to `K×`.

The kernel consists exactly of automorphisms fixing `b`, hence fixes
exactly `K(b)` by infinite Galois correspondence. The square equation gives
degree at most two; nontrivial conjugation excludes degree one.

Choose any nonzero width `δ`. Both `b` and `iδ` are purely imaginary in
`L`; their quotient belongs to `E=L∩ℝ`. Thus the square class of `δ²` is
represented over `K` by `−b²`, proving width-class descent and continuous
splitting. A nonzero imaginary element excludes the all-real case, so some
width is nonzero.

Conversely, descent writes `δ²=a u²`, with `a∈K×`, `u∈E×`. Then
`b=iδ/u∈L×`, `b²=−a`, and `c(b)=−b`. Every source automorphism sends
`b` to `±b`, defining a multiplicative sign character. Its kernel is the
open stabilizer of the algebraic element `b`, so the character is continuous.
Conjugation has sign `−1`.

Every nonzero purely imaginary element generates `L` over `E`: each zero
offset divided by it is real and lies in `L`, hence in `E`. Restriction and
character value are therefore jointly injective. Every automorphism of `E/K`
extends to `L`; composing with `c` adjusts the sign while preserving the
restriction. This gives surjectivity. Compactness of the source Galois group
and the Hausdorff target make the continuous bijection a homeomorphism.

## Formalization

`GaloisTheoryOfZeros/TheQuadraticCharactersOfConjugation.lean`:
`sourceRootSign_continuous`, `sourceRootSign_fixedField`,
`centered_character_has_radical`, `centered_character_radical_unique`,
`centered_character_quadratic_field`, `centered_imaginary_ratio_mem_even`,
`widthSquareDescends_of_imaginary_source_root`,
`imaginary_source_root_of_widthSquareDescends`,
`centered_conjugation_quadratic_detection`,
`centered_quadratic_characters_blind_of_not_split`,
`centered_imaginary_adjoin_top`, `centeredQuadraticCoordinates_bijective`,
`centeredQuadraticGaloisHomeomorph`, and `centeredQuadraticGaloisEquiv_conjugation`.

Direct source audit passed. All fourteen main transitive axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Boundary

Actual descent and existence of a nonzero width remain undecided.
Nonsplitting would make every continuous quadratic character blind to
centered conjugation. The criterion does not assert that the complete-block
characters exhaust these characters or that character blindness implies
trivial conjugation.
