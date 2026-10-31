# Positive-loop torus coordinates commute with field maps

- **Stage:** 2-fully-proven
- **Parent:** [Elliptic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** Coefficient-field maps commute with the actual positive-loop
  splitting, preserve and reflect positive Borel, and map both intrinsic Borel torus
  coordinates by the induced map on coefficient-field units.

## Proof

Coefficient mapping commutes with the power-series inclusion into Laurent
series: compare nonnegative coefficients, while all negative coefficients
vanish. The actual central-loop field map therefore commutes with the upper
and lower positive root embeddings. Every power-series determinant-one matrix
is a product of four such roots; multiplicativity proves compatibility with
the full positive splitting.

The lower-left constant remains zero, so entrywise mapping preserves Iwahori.
Its finite torus coordinate is the upper-left constant and hence maps as claimed.
The central embedding is already natural. Mapping the central–Iwahori
factorization therefore gives such a factorization in the target field.
Faithfulness of that factorization identifies the chosen intrinsic factors,
and their central and finite torus coordinates have the asserted values.

Laurent coefficient-field maps preserve the integer Laurent valuation.
The entrywise Iwahori valuation criterion therefore also reflects Borel
membership from the target field to the source field.

## Lean

`HTGeometry/LoopEisenstein/PositiveLoopFieldMap.lean`:
`LoopSL2.fieldMap_positiveEmbedding`, `LoopSL2.borelFieldMap`,
`LoopSL2.borelTorusHom_fieldMap`, `LoopSL2.fieldMap_mem_positiveBorel_iff`. Direct check pending.
