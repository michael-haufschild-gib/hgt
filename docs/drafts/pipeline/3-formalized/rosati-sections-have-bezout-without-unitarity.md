# Rosati sections have Bézout without unitarity

- **ID:** qii-rosati-bezout
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** Every finite curve datum has Bézout and ampleness on its Rosati source cone and Frobenius-mass section cone. Riemann–Roch is exactly vanishing of the reflection defect.

## Paper proof [PROVED HERE]

For a window S and a source polynomial p, let v(p) be its finite vector of
normalized Frobenius evaluations. Functional-equation and conjugation
permutations give a reflection permutation R. Expanding the actual mixed
Toeplitz form gives

    δ(x,y) = Re sum_i conjugate(v(x)_i) v(y)_(R i).

Finite Cauchy–Schwarz and permutation invariance of the squared norm imply
δ(x,y)² ≤ Φ(x)Φ(y), where Φ(x)=sum_i |v(x)_i|² is the original Rosati source
mass. The exact source-cone criterion therefore proves Bézout. Zero source
mass kills every mixed defect, which proves ampleness.

The existing exact reflection decomposition is δ(x,x)=Φ(x)−D(x), with
D(x)≥0. The RR boundary criterion is Φ≤δ. Thus RR holds precisely when
D vanishes for every source. The matrix-section mass is exactly Φ, so the
same conclusions hold for its section presentation.

The existing golden datum has nonzero reflection defect and fails RR. The
unconditional Bézout and ample theorems still apply to it. This is an exact
separation of positive source mass from the additional purity obligation.

## Lean certificate

Module:
`formal/GaloisForLFunctions/ArithmeticOrientationTheory/RosatiSectionsHaveBezoutWithoutUnitarity.lean`.

Main declarations:

- `CurveDatum.mixedToeplitz_eq_reflectedFrobenius`
- `CurveDatum.rosatiSourceCone_bezout`
- `CurveDatum.rosatiSourceCone_ample`
- `CurveDatum.rosatiSourceCone_riemannRoch_iff_reflection_zero`
- `frobMassSectionCone_bezout_and_ample`
- `goldenDatum_frobMass_bezout_ample_not_riemannRoch`

Actual-file check passed with `lake --old env lean` from `formal/`. All six
transitive axiom audits returned only `propext`, `Classical.choice`, and
`Quot.sound`. Temporary audit commands removed; umbrella and README wired.
No unitarity hypothesis was added to the positivity theorem. No assertion
about external novelty is made.
