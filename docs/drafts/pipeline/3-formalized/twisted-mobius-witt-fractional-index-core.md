# Twisted Möbius--Witt fractional-index core

- **ID:** ULF-TMW-1A
- **Stage:** 3-formalized
- **Lean:** `GaloisForLFunctions.HTGeometry.TwistedMobiusWittCompletion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

Closed theorem `twistedMobiusWitt_fractional_boundary_index_law` proves:

- neutral twist gives exact Möbius delta recovery;
- every positive twist leaves strictly positive Euler-product coefficients;
- boundary index is `1 / ζ(1+a)`, lies strictly in `(0,1)`, and is not integral;
- no nonzero meromorphic germ can have that index as its cofinal logarithmic current.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

This certifies completion-index quantization, not yet the analytic theorem identifying the explicit
Witt formation's radial current with that index, and not the Xi occurrence-to-completion lift.
