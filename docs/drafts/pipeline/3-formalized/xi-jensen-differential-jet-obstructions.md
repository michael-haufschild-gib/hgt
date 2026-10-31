# Xi Jensen differential-jet obstructions

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** If a Jensen polynomial of any real translate of `D^k prod(1-cD) XiC`, with real `c`, fails to split over the reals, RH is false.

## Corpus boundary

`riemannHypothesis_of_splits_jensenPoly_XiC` proves only the sufficient direction at the origin.
`riemannHypothesis_iff_laguerrePolya_XiC` supplies RH-to-Laguerre–Pólya membership.
The corpus also proves closure under derivatives, real translations and first-order factors,
and `splits_jensenPoly_realTaylorCoeff` gives every finite Jensen section.
Searches found no Xi falsification endpoint for this finite-jet family.

## Proof

Under RH, Xi is Laguerre–Pólya. Apply derivative, first-order-factor and real-translation
closure. Conjugation symmetry is preserved by each operation. Its real Taylor coefficients
therefore define splitting Jensen polynomials at every degree. A single nonsplitting section
contradicts RH. The witness uses finitely many actual Xi derivative values; no analytic
closure condition is included in the antecedent.

The base section also supplies the missing necessity direction of the existing Jensen criterion.
All translates, orders and factors belong to one endpoint family, not separate counted additions.

## Lean

`arithmetic-positivity-theory/Jensen/XiJetObstruction.lean`:

- `xiDifferentialJensenPolynomial_splits_of_rh`.
- `not_riemannHypothesis_of_xiDifferentialJensenPolynomial_not_splits`.
- `riemannHypothesis_iff_splits_jensenPoly_XiC`.

Final `lake --old env lean` source audit passes. Printed transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Imported by `ArithmeticPositivityTheory.lean`;
no umbrella build.
