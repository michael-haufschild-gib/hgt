# Phase cancellation between separated growing-moment cofactors

- **ID:** b13-growing-cofactor-gram-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean).
- **Obstacle:** B13 / cancellation in the centred cofactor current.

## Statement

Put `F_r(x)=(ε/t)^r x^(2r−1/2−it)exp(−εx²)`,
`α=Re ε>0`, `ξ=Im ε`, and

`L_r(m,k)=Σ_(d≥1)F_r(md)conj(F_r(kd))`.

For every `a,κ>0` and integers `J,N≥0`, put `r=⌊κt/log t⌋`.
For all sufficiently large `t`, uniformly over

- `αexp(2at)=2`, `|ε|≤4αt`, `|ξ|≥αt`;
- positive integers `m,k≤3t^(J+3)` with `m≥2k`,

one has `|L_r(m,k)|≤2/t^N`. The series is absolutely convergent.

## Exact correlation and uniform error

Write `A_m=(ε/t)^r m^(2r−1/2−it)`,
`z=α(m²+k²)+iξ(m²−k²)`, and

`C_r(m,k)=A_m conj(A_k) Γ(2r)/(2z^(2r))`,
`S_r(m,k)=|A_m A_k| Γ(2r)/(2(2αmk)^(2r))`.

For `r≥1`, the continuum integral equals `C_r`, and

`S_r²=|C_r(m,m)||C_r(k,k)|`,
`|C_r|=S_r[1+(1+(ξ/α)²)((m²−k²)/(2mk))²]^(-r)`.

For `t≥1`, `|ε|≤4αt`, and `1≤m,k≤W`,

`|L_r−C_r|≤S_r(2048r³αt²W²)^r`,
`S_r≤(4r)^(2r)`.

If also `m≥2k` and `|ξ|≥αt`, then `|C_r|≤(4r/t)^(2r)`.

## Proof

The long-variable height phases cancel in the product, leaving
`A_m conj(A_k)x^(4r−1)exp(−zx²)`. The Gaussian Mellin integral gives
`C_r`. The identity
`|z|²=(2αmk)²+(α²+ξ²)(m²−k²)²` gives the normalized profile.

The derivative recursion is `D_0(u)=Γ((u+1)/2)/2` and
`D_(j+1)(u)=(|u|+1)D_j(u−1)+8D_j(u+1)`. Its positive integer
Gamma grid gives `D_k(k+2j−1)≤Γ(p)(2p+8)^k/2` when
`j≥1` and `k+j≤p`. Take `k=2r`, `j=r`, `p=3r`.
Since `Γ(3r)≤Γ(2r)(3r)^r` and `6r+8≤14r`, this yields
`D_(2r)(4r−1)≤Γ(2r)(588r³)^r/2≤Γ(2r)(1024r³)^r/2`.
The Bernoulli quotient is at most one. Dividing the lattice remainder by `S_r` and using
`4m²k²/(m²+k²)≤2W²` gives the relative error above.

For separated cofactors, `|z|≥|ξ|mk`, `|ε|≤2|ξ|`, and
`Γ(2r)/2≤(2r)^(2r)` give the absolute continuum bound. At the stated
scale and cutoff, the absolute lattice error has base at most
`589824t^(2J+13)exp(−2at)`, since `r≤t` eventually. It is therefore
at most `exp(−at)`. The inequalities `κt≤2r log t≤2κt` and
`(log t)²/t→0` give `(4r/t)^(2r)≤t^(−N)` eventually. Each error
is at most `t^(−N)`.

## Lean declarations

All modules belong to `GaloisForLFunctions.ExceptionalLayerTheory`.

- `GaussianMomentCofactorCorrelations`: literal product, absolute
  convergence, `integral_gaussianCriticalMoment_pair`,
  `gaussianCofactorOverlap_eq`, `gaussianCofactorCorrelationScale_sq`,
  and the raw lattice remainder; eight clean transitive axiom audits.
- `GaussianCofactorCorrelationBounds`:
  `norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le_scale`,
  `norm_tsum_gaussianHigherPrimeMoment_pair_le`, and the two absolute
  bounds; five clean transitive axiom audits.
- `GaussianGrowingCofactorCancellation`:
  `norm_tsum_gaussianHigherPrimeMoment_pair_far_le` and
  `eventually_gaussianGrowingCofactorPair_rapid_decay`; direct source
  check passed, with two clean transitive axiom audits.

The fifteen axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. All three modules pass final direct source checks
without warnings and are imported by the umbrella.

## Remaining obstacle

These are complete integer pair correlations. Inserting the actual long
prime coefficients, restricting the long variable, or bounding the
near-diagonal contribution requires further estimates. No upper bound
for the centred current below an exceptional-mode rate is proved.
Absolute rapid decay here means every fixed inverse height power;
an absolute `exp(−ct)` bound is not asserted. B13 remains open.
