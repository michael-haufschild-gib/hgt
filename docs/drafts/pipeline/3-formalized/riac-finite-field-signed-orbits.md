# Signed Frobenius orbit cancellation

- **ID:** RIAC-finite-field-signed-orbits
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [discriminant-cover construction](riac-discriminant-cover-signed-counts.md)
- **Statement:** Actual Frobenius transporter counts define orbit orientation weights in `{-1,0,1}`. Repeated coordinates have weight zero, distinct coordinates retain Frobenius sign, and the total cancels exactly for at least two labels.

## Actual local counts

Let a finite group `G` act on a finite set `X`, let `φ` be equivariant,
and let `χ:G→{±1}` be an integer unit character. For an orbit `O`, define

`A(O)=Σ_(x∈O) Σ_(g·x=φ(x)) χ(g)`,  `w(O)=A(O)/|G|`.

The numerator is the difference between the cardinalities of two actual
transporter sets. No local orientation sign is inserted as a premise.

If `O` is not fixed, its transporter sets are empty. If a stabilizer
contains an element of sign `−1`, right multiplication pairs opposite
signs; conjugation transfers this pairing throughout the orbit. In both
cases `w(O)=0`.

Otherwise choose `g₀·x₀=φ(x₀)`. Every transporter over the orbit has
character `χ(g₀)`: conjugation reduces its ratio with `g₀` to a stabilizer
element. The actual transporter-pair set has `|G|` elements by the proved
orbit–stabilizer bijection. Hence `w(O)=χ(g₀)`. This proves the
unconditional classification `w(O)∈{−1,0,1}`.

## Independent arithmetic cancellation

Take `G=S_I` on tuples indexed by a finite set `I`, with `|I|≥2`.
For a finite field `F` of cardinality `q`, construct the extension `E/F`
of degree `|S_I|`. Put `X=E^I`, take coordinate Frobenius for `φ`, and
take permutation sign for `χ`.

The independent normal-basis construction gives exactly `q^|I|` tuples
in every permutation-twisted fibre. Reindexing the actual transporter
pairs therefore gives

`Σ_O A(O)=q^|I| Σ_(g∈S_I) sign(g)=0`.

A transposition pairs the last sum with its negative. Thus `Σ_O w(O)=0`.
This proof imports no polynomial Möbius degree-sum theorem.

A repeated coordinate supplies an actual odd stabilizing transposition,
so its orbit weight vanishes. For a tuple with distinct coordinates,
the stabilizer is trivial and the weight is its Frobenius permutation sign.
The construction and cancellation work in every finite characteristic.

## Scope and lighthouse

These are orientation weights of arithmetic orbit counts. They are not
identified with the relative singular-homology indices of the integer
prime complex. The [discriminant comparison](riac-discriminant-cover-signed-counts.md)
identifies them with `(-1)^deg(f) μ(f)` over odd finite fields. Integer cancellation
`Σ_p index_p(N)=1−M(N)=Oε(N^(1/2+ε))` is not proved.

## Formalization

[FiniteFieldSignedOrbits.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldSignedOrbits.lean):

- `transporterSignSum_eq_zero_of_odd_stabilizer`, `sum_transporterSignSum`.
- `sum_orientationOrbitNumerator`, `orientationOrbitNumerator_eq_sum_orbit`.
- `orientationOrbitNumerator_eq_zero_of_not_fixed`.
- `orientationOrbitNumerator_eq_zero_of_odd_stabilizer`, `orientationOrbitWeight_eq_zero`.
- `sum_frobeniusOrientationNumerator`, `sum_frobeniusOrientationWeight_eq_zero`.
- `arithmeticOrientationSum_eq_zero`.
- `orientationOrbitNumerator_eq_sum_transporters`, `orientationOrbitWeight_eq_character`.
- `orientationOrbitWeight_trichotomy`.
- `frobeniusOrientationWeight_eq_zero_of_collision`, `frobeniusOrientationWeight_eq_sign`.

Direct leaf check and fifteen transitive axiom audits; only `propext`,
`Classical.choice`, `Quot.sound`.

## Literature boundary

The stabilizer average and its Frobenius distribution are classical;
[Gadish, Definition 1.1, Corollary 1.4 and §3.2](https://arxiv.org/html/1703.01710v2)
treat the ramified-cover formulation. The construction here formalizes
actual transporter sets, local sign classification and independent
normal-basis cancellation. No new finite-field cancellation theorem is
claimed.
