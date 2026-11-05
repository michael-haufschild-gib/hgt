# Complete quartic theta compensation on the initial and middle intervals

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenPolynomialCrossCompactEnvelope.lean`

Put `q=π exp(2x)`, `F=thetaCuspFullSource x`, `K=4q² exp(x−2q)`,
`S(q)=(8q²−30q+15)/(2(2q−3))+q/250`, and
`J(S,t)=2t(1−2t²)²S+(1−2t²)(14t²−3)`.
For the complete quartic compensation `G_P`, Lean proves:

| Region | Bound |
|---|---|
| `x≥0`, `q≤37/10` | `G_P≥2F²` and `G_P≥−K J(3,25q/157−1/2)(2q−3)²` |
| `37/10≤q≤5` | `G_P≥F²/16` and `G_P≥−K J(S(q),1/4)(2q−3)²` |
| `5≤q≤7` | `G_P≥−K(501/500)² J(S(q),q/14−99/1000)(2q−3)²` |
| `5≤q≤7` | `G_P≥−K{c²J(S(q),T₆)+3(c²−1)}(2q−3)²`, `c=501/500`, `T₆=q/12−22/125` |
| `q=6` | `−126K≤G_P≤−(1251/10)K` |
| `q≥5`, `x²≤1/2` | `G_P>−(3/20)Kq⁴` |

The interval allowances are explicit polynomials. No theta atom is discarded.

For `q≥37/10`, the complete likelihood moment bound `M₁≤1/500`
gives `F≤(501/500)f₁` and `F′≥−S(q)F`. Hence
`G_P≥−J(S(q),x)F²`. The loss is increasing in its center on
`0≤x≤41/100` for `0≤S≤9`. Insert the center bounds
`x≤1/4` below five and `x≤q/14−99/1000` on `[5,7]`.
Below `37/10`, the complete logarithmic-jet error is at most `1/10`,
so `F′≥−3F`; the center bound is `x≤25q/157−1/2≤1/10`.
The positive reserves use `F²≥f₁²=K(2q−3)²`.

On `[5,7]`, `7/2≤S≤9`. At slope `7/2`, writing `t=x−1/2` gives
`13S/40−J(S,x)=1/80−3t/4+15t²+28t²(t+1/2)(1−t−t²)>0`.
Interpolation with the slope-nine bound yields `J≤13S/40`.
Writing `u=7−q∈[0,2]`, the quartic gap is
`641/80+24u/5+63u²/20−8u³/5+3u⁴/20>5`;
mass and slope errors cost at most four. The existing bound covers `q≥7`.

The scale-six tangent is `x≤q/12−22/125`. The bound `J(S,T₆)≥−3`
allows the mass error to be absorbed without assuming the loss is positive.
At `q=6`, the complete likelihood moments give
`F≤(500001/500000)f₁` and `−(3417/500)F≤F′≤−(41/6)F`.
Insert `323/1000≤x≤81/250` and `f₁²=81K` into the quartic correction
to obtain the two-sided bracket.

Namespace `FifthPolynomialCross`: `compensation_initial_positive`,
`compensation_lower_middle_positive`, `compensation_before_five_positive`,
`compensation_initial_polynomial_lower`, `compensation_lower_polynomial_lower`,
`compensation_compact_middle_lower`, `compensation_compact_quartic_lower_five`,
`compensation_compact_six_lower`, `compensation_six_upper`, and `compensation_six_lower`.
Canonical Lean check passed; all ten transitive audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The scale-six load lies beyond the complete matrix capacity; see the
[truncated-profile obstruction](../5-failed/theta-cusp-truncated-quartic-profile.md).
