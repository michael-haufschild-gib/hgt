# W3: a positive-real strip for the arc multiplier

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Statement:** For every probability measure on the modular bottom arc, its shifted-Gamma multiplier has positive real part on `|Im z|≤501/1000` in spectral coordinates.

Write `P_j(z)=∏_{k<j}((k+1/4)²+z²/4)`, `m_j=∫sqrt(y(u)/2)u^(2j)dμ`, and `w_j=4sqrt(2)4^j m_j/(2j)!`. Then `R(z)=Σw_jP_j(z)`. Existing bounds give local uniform convergence and `m_j≤4^(−j)m_0`, with `m_0>0`.

## Proof

Put `b=501/1000`. If `|Re z|≤7/5` and `|Im z|≤b`, then `|z|≤3/2`. Each factor of `Q_j(z)` and `Q_j(−z)` has norm at most `k+1`, so `|P_j(z)|≤(j!)²`. The existing factorial-ratio estimate bounds the tail `Σ_{j≥1}|w_jP_j(z)|` by `3sqrt(2)m_0`. Since `w_0=4sqrt(2)m_0`, `Re R(z)≥sqrt(2)m_0>0`.

For `x=|Re z|≥7/5`, set `y=|Im z|≤b` and `d=sqrt(x²−y²)>0`. Every quadratic factor has positive real part. For any complex number `v` with positive real part,

`|v/|v|−1|≤|Im v|/Re v`.

The triangle inequality for products of unit complex numbers therefore bounds the distance from the normalized product `P_j(z)/|P_j(z)|` to `1` by

`(xy/2) Σ_{k<j} 1/((k+1/4)²+d²/4)`.

For the decreasing function `f(t)=1/(t²+d²/4)`, integral comparison gives

`Σ_{k<j}f(k+1/4)≤f(1/4)+∫_{1/4}^∞f≤(3/4)f(1/4)+π/d`.

Here `∫_0^(1/4)f≥f(1/4)/4`. Thus the normalized-product distance is at most

`y[3x/(2(x²−y²+1/4))+πx/(2d)]`.

On this region, elementary rational inequalities give
`3x/(2(x²−y²+1/4))≤13/12` and `x/d≤43/40`. Using `π<63/20`, the preceding distance is at most
`(501/1000)(13/12+2709/1600)<7/5`.

A unit complex number at distance at most `7/5` from `1` has real part at least `1/50`, because `|u−1|²=2−2Re u`. Consequently `Re P_j(z)≥|P_j(z)|/50>0` for every `j`. Summing the nonnegative weights proves `Re R(z)≥w_0/50>0`.

## Consequence

The principal square root of `R` is holomorphic on a neighborhood of the closed strip. It is even and strictly positive on the real axis. Multiplying it by `Ξ` produces a single candidate whose spectral square equals the twisted-arc mixture. The existing strip growth bounds leave the positive decay rate `3/4−log(3)/2`; selecting the annihilating probability measure supplies integer blindness. These consequences require their own complete Lean assembly; no finished extremal-function claim is made yet.
