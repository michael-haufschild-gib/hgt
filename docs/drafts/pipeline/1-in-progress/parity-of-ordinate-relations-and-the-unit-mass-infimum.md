# Parity of ordinate relations and the unit mass infimum

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; uncounted
- **Obstacles:** B13, B112; simultaneous positive annihilation at fixed ordinates.
- **Statement:** For a nonempty finite family `gamma_i` and any real abscissa `beta`, conjecture equivalence between: (a) for every `delta>0`, a positive two-prime polynomial with constant coefficient one annihilates every `beta+i gamma_i` and has tail mass below `1+delta`; (b) every integer relation `sum n_i gamma_i=0` has even coefficient sum `sum n_i`. The converse construction gives every exact mass `H>1`.
- **Novelty:** Odd-relation mass gaps give the obstruction. The missing converse would classify precisely which fixed finite ordinate families permit near-unit exact annihilation.

## Evidence and proof gates

The inspected theorem `GaloisForLFunctions.HTGeometry.screwHull_eq_screwAnnihilator` in `HTGeometry/SummableSpectrumScrewHull.lean` identifies the continuous phase-orbit closure with the annihilator of all integer relations, without a Kronecker hypothesis. Its all-half-period point should therefore belong to the hull exactly under the parity condition.

Proof decomposition:

1. **Verified:** `closure_nonconstant_twoPrimePhase` in `ArithmeticPositiveDuality/TwoPrimePhaseHull.lean` identifies the nonconstant two-prime phase closure with the continuous relation hull. Compact semigroup recurrence and density of the integer span of `log 2, log 3` supply the proof. Direct Lean audit passes; axioms: `propext`, `Classical.choice`, `Quot.sound`.
2. The all-half-period point evaluates an integer character as `(-1)^(sum n_i)`. The relation-hull theorem therefore identifies its membership with the parity condition. Translation by that point makes the complex phase hull centrally symmetric.
3. **Verified:** `smul_mem_convexHull_of_symmetric_closure` in `SymmetricPhaseConvexity.lean`. For any finite-dimensional set with symmetric closure, work in its linear span. Symmetry puts zero in its affine span. Its convex hull has nonempty interior there, and symmetry of its closure puts zero in that interior. Every strict radial contraction of a closure point therefore belongs to the convex hull of the original set. Kernel check passes with the three standard axioms; final direct audit remains.
4. Represent `-1/H` by an exact finite convex combination of nonconstant monomial phases. Multiply the weights by `H` and each coefficient by `exp(beta * monomialLog d)`. This produces exact annihilation with constant coefficient one and tail mass exactly `H`.
5. Conversely, summing the phase-energy identities gives total weighted defect `2*N*(H-1)`. Since `H>=1`, arbitrarily near-unit mass forces a nonconstant monomial arbitrarily close to the simultaneous antipodal point. Hull membership then forces parity.

The remaining components have Lean proof drafts in `PhaseHullParity.lean`, `PositivePhaseCombinations.lean`, and `ParityClassifiesNearUnitAnnihilation.lean`; kernel verification remains incomplete. No contribution is counted yet.

Do not replace the last step by approximate cancellation or assume a dense-orbit interface. The exact finite convex correction is essential.
