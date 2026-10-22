# P/C1 four-channel lower-Cauchy facts

## Simultaneous finite-source carrier

For any four vectors in `xiWeilCauchyHilbertSubspace`, there is one sequence of four-tuples of
finite linear combinations of literal lower prime--Gamma Cauchy atoms converging componentwise to
those vectors.  For every pair of labels `i,j : Fin 4`, the corresponding Hermitian Gram entry
converges to the target mixed term.

Formal source: `RHTower/DeningerPrimeGammaLowerCauchyFiniteGramApproximation.lean`, theorem
`exists_lowerCauchy_fourTuple_gramApprox`.

## Consequence for P and C1

Lower source reachability is not limited to isolated scalar values.  It supplies a genuine
non-scalar, four-channel finite-source boundary carrier retaining every one of the 16 mixed
Hermitian terms.  Therefore any remaining P/C1 failure cannot be attributed to an inability to
realize a labelled finite source carrier.

## Remaining hard core

The theorem gives convergence, not a sign.  It neither proves reflected-diagonal positivity nor
evades the nuclear-root obstruction.  The exact remaining statement is a source-faithful sign or
coercivity law for the limiting four-by-four Gram matrix; replacing it by separate diagonal or
scalar-reader bounds loses the orientation the carrier preserves.
