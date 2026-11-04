# Positive interval across the quartic profile zero

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Statement:** For `x≥0`, `1/2≤x²`, and `x≤3/4`,
  `G_P(x) ≥ (3/8)(2x²−1)F(x)² ≥ 0` and `H_P(x)` is positive definite.
  The literal weighted repair is positive for every `a>0` and
  `r>0` satisfying `2≤r²` and `r≤3/2`.

Write `q=π exp(2x)` and `t=2x²−1`. Then `0≤t≤1/8`.
The interval gives `7≤q≤57/4`: the lower bound follows from
`x≥1/2`, `exp(1)≥5/2`, and `π>3`; the upper bound follows from
`π<3.15` and `exp(3/2)<9/2`.

The complete-source mass and derivative bounds give
`F≥f₁>0` and `F'≥−(firstSlope(q)+10⁻⁵)f₁≥−24F`.
Indeed, `firstSlope(q)=2q−9/2−6/(2q−3)`, so the rational bounds on `q`
imply `firstSlope(q)+10⁻⁵≤24`.

The exact correction is
`G_P=t[(3t+8x²)F²+2xtFF']`.
Consequently it is at least
`tF²[4+(7−48x)t] ≥ tF²(4−29/8) = (3/8)tF²`.
The complete native fifth even source is positive definite for `q≥5`;
the cross-load is positive semidefinite. Their sum is therefore positive.
The literal weighted source adds a nonnegative multiple of the same
cross-load to a positive scalar multiple of `H_P`.

This certifies an explicit compact interval. Global positivity of the
profiled source, and global rank-nine positivity, remain open.

Lean: `ThetaCuspSections/FifthEvenPolynomialCrossInterval.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross`:
`compensation_interval_lower`, `repair_interval_posDef`,
`weightedRepair_interval_posDef`.
Canonical check passed without warnings. All three declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`.
