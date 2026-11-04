# Polynomial cross-load: positive source regions

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Result:** One explicit polynomial flux preserves the fifth even mixed matrix
  and repairs neighborhoods of the origin and scale eight, together with a
  cofinal source ray.

Write `F=thetaCuspFullSource`, `G=3F²+2xFF′`,
`B=loadMapᵀ paidSevenSchur loadMap`, `H(x)=nativeShiftedMatrix 5 0 x`,
and `x₈=½log(8/π)`.
For `P(r)=(1−r²/2)²`, define

`J_P(a,r)=P(r)r²sinh(ar)F(r/2)²`,
`G_P(x)=(1−2x²)²G(x)−8x²(1−2x²)F(x)²`,
`H_P(x)=H(x)+G_P(x)B`.

There are `0<δ≤R` such that `H_P(x)` is positive definite whenever `x≥0`
and `x<δ`, `|x−x₈|<δ`, or `x≥R`. The literal weighted matrix
`r sinh(ar)H(r/2)+J_P′(a,r)B` is positive on the corresponding radius regions
for every `a>0` and `r>0`. For `0≤a<½`, its entries are integrable and their integrals
are exactly `thetaCuspCenterMixedSignedJet a (2(i+j))`.
Global positivity through the intervening compact interval remains open.

## Proof

The flux is `polynomialFlux 0−polynomialFlux 2+polynomialFlux 4/4`.
Each derivative has zero half-line integral. Since `P≥0`, its derivative
is bounded below by `r sinh(ar)G_P(r/2)`.

At the origin the correction is unchanged. At `x₈`, complete-source bounds
give `G≤−6F²` and `(1−2x²)²≤1/3`. Also `8x²(1−2x²)≤1`, so
`G_P≥G/3−F²≥G/2`. The [positive half-load](theta-cusp-cross-load-scale-eight-capacity.md)
and `B≥0` give strict positivity. Continuity supplies both neighborhoods.

The exact expansion is
`G_P=(3−20x²+28x⁴)F²+(2x−8x³+8x⁵)FF′`.
With first-atom mass `f₁` and `q=πe^{2x}`, the mass and slope limits and
exponential domination of powers give
`G_P/(f₁²q⁴)→0`. The load vanishes when `i+j<4`; hence every affected
Gaussian-balanced entry tends to its unchanged Gaussian moment.
Strict Gaussian positivity and an invertible diagonal congruence give the ray.

## Lean

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross`:

- `integral_deriv_flux`, `weightedRepair_integrable`, `weightedRepair_integral`
- `compensation_center_lower`, `repair_center_posDef`, `weightedRepair_center_posDef`
- `compensation_four_limit`, `repair_posDef_eventually`
- `repair_compact_gap`, `weightedRepair_compact_gap`

Modules: `FifthEvenPolynomialCrossLoad`, `FifthEvenPolynomialCrossTail`.

The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
