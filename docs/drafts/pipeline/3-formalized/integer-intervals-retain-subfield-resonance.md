# Integer intervals retain subfield resonance

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Argon §3A; `QuasiRHSubfieldMoment` and `QuasiRHSubfieldProjection`.
- **Statement:** Integer intervals in quadratic prime fields retain the sextic fourth-moment obstruction, even at cube-root cardinality. Balanced two-coordinate windows have a different line-occupancy geometry.

## Exact obstruction and paper proof

Choose any prime `p ≡ 5 (mod 6)`, put `t = floor(cuberoot(p)) ≥ 2`, and take
`K = F_(p²)`, an order-six character χ, and the literal integer interval
`S = {0,…,t²−1}` in K. Such primes are unbounded by the corpus's installed Dirichlet theorem.
Norm surjectivity makes χ trivial on `F_p*`. The interval has `B=t²` distinct elements and
`B³≤p²`. On `F_p`, its packet equals B outside S and B−1 inside S. Therefore

`M₄ ≥ (p−B)B⁴+B(B−1)⁴`.

Since `2B≤t³≤p` and `p<(t+1)³≤8t³`, multiplication gives
`16 M₄ ≥ t p² B²`. Thus the normalized moment grows at least proportionally to
`p^(1/3)=|K|^(1/6)`. In particular interval support does not remove the known power obstruction.
This refutes only the claim that rational/integer interval geometry alone supplies the proposed
extension-field non-concentration. Prime-field interval CM4 and balanced Eisenstein windows remain open.

## Positive survivor: a quantitative occupancy invariant

Write `r=|F|`, `B=|S|`, and `n_u(x)=|S∩(x−uF)|`. The exact line-average identity gives
`Σ_a T(x−ua)=χ(u)(r n_u(x)−B)`. Since `|χ(u)|=1`, Hölder gives

`(r n_u(x)−B)^4 ≤ r³ Σ_a |T(x−ua)|⁴`.

Summing over x and translating each inner sum proves

`Σ_x (r n_u(x)−B)^4 ≤ r⁴ M₄(χ,S)`.

This is a necessary quantitative occupancy condition for every direction, retaining the
complete fourth-power imbalance distribution. It replaces the report's qualitative
non-concentration assertion with a precise invariant. No fourth-moment upper bound follows
from it. Its proof uses only the existing exact projection, finite Hölder, and translation.

## Surviving window geometry

For a two-coordinate box `I+ωJ`, `ω∉F`, each affine F-line intersects it in at most
`max(|I|,|J|)` points: a nonhorizontal line has at most one point for each first coordinate,
and a horizontal line has a fixed second coordinate. Injectivity follows from `ω∉F`.
This gives an exact geometric distinction between one-coordinate intervals and balanced boxes;
it does not estimate the remaining signed fourth-moment correlations.

## Lean declarations

All declarations below are in `GaloisForLFunctions.ArithmeticHarmonicAnalysis`.

- `FiniteField/IntegerIntervalResonance.lean`: `exists_integerInterval_sextic_moment_excess` constructs the prime, field, character, and literal interval without assumed arithmetic input.
- `FiniteField/LineOccupancyMoment.lean`: `affineLine_imbalance_fourth_le` and `affineLine_occupancy_moment_le` retain the quantitative occupancy obstruction for every shift set and direction.
- `FiniteField/CoordinateBoxLines.lean`: `coordinateBoxLine_card_le_min`, `coordinateBoxLine_card_le_max`, and `coordinateBoxLine_max_attained` give the sharp box geometry; horizontal and vertical identities realize the extrema.

All three leaves pass `lake --old env lean` and are wired into `ArithmeticHarmonicAnalysis`.
All ten exported theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
External novelty unclaimed; research was local only.

The balanced-window signed moment and its actual detector transport remain open on the
[parent route card](../1-in-progress/argon-quasi-rh-and-critical-proportion.md).
