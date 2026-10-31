# Product formula on the actual adelic completions

- **ID:** elliptic-product-formula-uses-the-actual-adelic-completions
- **Stage:** 3-formalized
- **Statement:** For every nonzero function on `y²=x³−x` over `𝔽₃`, the
  product of its residue-normalized magnitudes in the actual finite and
  infinity completions defining the adele ring equals one.

## Proof

The canonical affine-ring equivalence carries prime powers and principal
ideals to their counterparts in the integral closure. Divisibility by every
prime power therefore identifies the integral adic valuations. Taking
fractions identifies the valuations on the function field. The same ring
map gives residue-ring equivalences, so their cardinalities agree.

Completion preserves the valuation on the embedded function field. The
finite-place equivalence consequently reindexes the already proved product
formula, with the infinity normalization unchanged at three.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticPlaceNormalization.lean`:
`finitePlaceAffineEquiv_valuation` and `adelic_product_formula` passed direct
Lean checks. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
