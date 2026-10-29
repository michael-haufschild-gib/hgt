# Hecke L-series as finite sums of actual class theta transforms

- **ID:** hecke-l-series-as-finite-class-theta-sums
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Global continuation](hecke-global-continuation-from-ordinary-classes.md)
- **Lean:** `HeckeLFunctions/HeckeLSeriesAreFiniteSumsOfClassThetaTransforms.lean`

## Statement and proof

For every ordinary ideal class `c`, choose a nonzero integral ideal `B_c`
prime to the finite modulus with class `c^-1`. Such ideals exist by the
proved prime-to representative theorem. The ideals in the inverse class
of `B_c` are exactly the fiber of the ordinary class map over `c`.
Absolute convergence partitions the full Hecke ideal series into these
finitely many inverse-class series.

The base character value is nonzero. Multiply each actual continued
unit-theta transform by `psi(B_c)^-1 N(B_c)^s` and by the common scalar
`degree * 2^unitRank / torsionOrder`. The proved class Mellin identity
cancels these factors and gives `GammaFactor(s) * heckeL(s)` on `Re s>1`.
The reciprocal Gamma product is entire and nonzero there, hence removing
it gives an actual continuation of the original series.

If finite residue weight or real parity is nontrivial, both theta zero
modes vanish. Every class transform is then entire, as are the base
weights and reciprocal Gamma product. Their finite sum is entire.

## Declarations

- `exists_heckeClassBaseIdeal`
- `heckeL_eq_sum_inverseClassL`
- `heckeClassWeight_mul_idealTerm`
- `heckeCompletedThetaContinuation_eq`
- `heckeThetaLContinuation_eq`
- `differentiable_heckeThetaLContinuation_of_ramified`

## Verification

Complete scratch passes without warnings. Transitive axiom audits of the
class partition, actual L-series agreement, and entire ramified continuation
report only `propext`, `Classical.choice`, and `Quot.sound`.
Final direct source audit with `lake --old env lean` passes without warnings;
the olean is built for the written global-continuation consumer.
Global removal of the unramified apparent poles remains on the source card.
