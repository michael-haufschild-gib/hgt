# Parity of ordinate relations and the unit mass infimum

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; uncounted
- **Obstacles:** B13, B112; simultaneous positive annihilation at fixed ordinates.
- **Statement:** For a nonempty finite family `gamma_i` and any real abscissa `beta`, conjecture equivalence between: (a) for every `delta>0`, a positive two-prime polynomial with constant coefficient one annihilates every `beta+i gamma_i` and has tail mass below `1+delta`; (b) every integer relation `sum n_i gamma_i=0` has even coefficient sum `sum n_i`.
- **Novelty:** Odd-relation mass gaps give the obstruction. The missing converse would classify precisely which fixed finite ordinate families permit near-unit exact annihilation.

## Evidence and proof gates

The inspected theorem `GaloisForLFunctions.HTGeometry.screwHull_eq_screwAnnihilator` in `HTGeometry/SummableSpectrumScrewHull.lean` identifies the continuous phase-orbit closure with the annihilator of all integer relations, without a Kronecker hypothesis. Its all-half-period point should therefore belong to the hull exactly under the parity condition.

Three bridges remain unproved here:

1. Identify the closure of nonconstant two-prime monomial phases with this continuous relation hull, using the two incommensurate logarithmic periods and compact semigroup recurrence.
2. Use the all-minus-one hull point to make the phase hull centrally symmetric. Its convex hull then has zero in its relative interior; this avoids a separate Haar-mean argument.
3. Turn every strict radial contraction of the all-minus-one point into an exact finite convex combination of actual nonconstant monomial phases. Rescaling positive coefficients then gives exact annihilation with mass arbitrarily close to one.

Do not replace the last step by approximate cancellation or assume a dense-orbit interface. The exact finite convex correction is essential.
