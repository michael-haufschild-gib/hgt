# Quartic theta compensation envelope from scale seven

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenPolynomialCrossCompactEnvelope.lean`
- **Theorem:** `FifthPolynomialCross.compensation_compact_quartic_lower_seven`

For `q=π exp(2x)≥7`, `x²≤1/2`, and `K=4q² exp(x−2q)`, the complete
quartic compensation satisfies `G_P(x)>−(3/20)Kq⁴`.

For `7≤q≤8`, retain the exact first-atom slope
`S=(8q²−30q+15)/(2(2q−3))+10⁻⁵`, so `8≤S≤45/4`.
The complete source bounds give `G_P≥−J_S(x)F²`, where
`J_S(x)=2x(1−2x²)²S+(1−2x²)(14x²−3)`.

On `0≤x≤1/4`, `J_S≤7S/16−119/64`; on `1/2≤x≤1/√2`,
`J_S≤S/4+4/7`. Both are at most `13S/40`. On the intervening interval,
put `t=x−2/5`. At slope endpoints `8` and `45/4`, the differences
`13S/40−J_S` dominate the positive quadratics
`492/3125−(288/125)t+39t²` and `229/20000+(87/250)t+50t²`.
Their remainders are nonnegative for `|t|≤3/20`; affine interpolation in
`S` gives `J_S≤13S/40` throughout.

With `u=q−7∈[0,1]`, the exact scale gap before the small source errors is
`641/80−(24/5)u+(63/20)u²+(8/5)u³+(3/20)u⁴`.
It exceeds `1`, while mass inflation and slope error each cost at most
`1/100`. The complete-source mass bound and `F₁²=K(2q−3)²` finish the
comparison. For `q≥8`, the existing decreasing-profile argument applies.

Transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
The [matrix reserve from scale seven](theta-cusp-quartic-cross-load-ray.md)
is formalized. The compact matrix sign below seven remains open.
