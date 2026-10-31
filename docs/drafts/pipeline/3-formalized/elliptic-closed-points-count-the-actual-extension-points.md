# Elliptic closed points count the actual extension points

- **Stage:** 3-formalized
- **Programme:** Arithmetic Effectivity Theory; A13.
- **Target:** For the actual affine ring `A=F₃[x,y]/(y²−x³+x)` and every
  finite extension `E/F₃` of degree `n`,
  `#C(E)=1+Σ_{v : deg(v)∣n} deg(v)`.
  Here `v` ranges over actual nonzero prime ideals of `A`,
  `deg(v)=dim_F₃(A/v)`, and the displayed set of places is finite.

The affine-point equation represents `F₃`-algebra maps `A→E` by the
universal property of `AdjoinRoot`. Each map has a nonzero prime kernel:
an injective map would embed the infinite ring `A` into the finite field `E`.
The maps with kernel `v` are precisely the embeddings `A/v→E`.
The proved finite-field embedding theorem counts these as `deg(v)` when
`deg(v)∣n`, and zero otherwise. Their finite union counts all affine points;
the unique infinity point contributes one.

Existing inputs: `pointsEquiv`, `coordinateRing_infinite`,
`affine_quotient_finiteDimensional`, and
`FiniteField.natCard_algHom_of_finrank_dvd`.
`ArithmeticEffectivityTheory/FiniteFieldEllipticClosedPoints.lean` proves
`pointsAlgHomEquiv`, `affinePointFiberEquiv`, `mem_affinePlacesOver_iff`, and
`card_points_eq_closed_place_sum`. Direct Lean check and transitive axiom
audits passed: only `propext`, `Classical.choice`, `Quot.sound`.
The closed-point Euler product is a subsequent target.
