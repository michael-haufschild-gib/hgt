# Bounded elimination onto coordinate intersections

- **ID:** CDG-ELIM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A coordinate intersection of the rational span of bounded
  small integer forms has a spanning family with controlled height and value.

## Theorem

Let `k≥0`, `H≥1`, `ε>0`, and let `S⊂ℤ^k` be finite, with
`|v_j|≤H` and `|L(v)|<ε` for every `v∈S`, where `L` is any real linear form.
For every coordinate set `J`, the intersection
`span_ℚ(S)∩ℚ^J` is spanned by integer rows `T` supported on `J` satisfying

`|t_j|≤k!H^k`, `|L(t)|<k!H^(k−1)ε`.

A rational basis selected from `T` has exactly the dimension of this intersection.
No lower bound on `L`, or prime-logarithm input, is assumed.

## Proof [PROVED HERE]

If `J` is empty, take `T` empty. Otherwise restrict `S` to the coordinates
outside `J`. Select `q` original rows whose restrictions form a basis of
the restricted span, and choose a nonsingular `q×q` column minor `B`.
Then `q≤k−1`. The case `q=0` uses the empty determinant, equal to one.

For each `v∈S`, let `v_P` be its selected pivot coordinates and put

`E(v)=det(B)v−Σ_a cramer(Bᵀ,v_P)_a M_a`.

Every outside restriction lies in the span of the pivot-row restrictions.
Cramer's identity therefore gives `E(v)=0` outside `J`.
The same formula defines a rational linear map on `V=span_ℚ(S)`.
Its image lies in `V∩ℚ^J`. On that intersection it is multiplication by
the nonzero integer `det(B)`, since all pivot coordinates vanish.
Consequently `T={E(v):v∈S}` spans the entire intersection.

The determinant and every Cramer numerator have absolute value at most
`q!H^q`. Thus `|E(v)_j|≤(q+1)!H^(q+1)` and
`|L(E(v))|<(q+1)!H^q ε`. Strictness follows from the nonzero determinant
term and `|L(v)|<ε`. Since `q+1≤k` and `H≥1`, these give the stated bounds.
Selecting a basis from the finite spanning family proves the last assertion.

## Contribution

This discharges the bounded elimination input to
`cdg-weighted-coordinate-separation.md`: small forms in a coordinate
intersection retain an explicit value bound after denominators are cleared.
Hereditary arithmetic sparsity and weighted selection remain separate inputs.

## Formalization

`CollectiveDiophantineGeometry/BoundedCoordinateElimination.lean`:

- `exists_bounded_coordinate_elimination`: exact spanning family and both bounds.
- `exists_bounded_coordinate_basis`: independent integer rows of the full intersection rank.

Direct `lake --old env lean` check passed. Both transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. The programme umbrella imports the module.
