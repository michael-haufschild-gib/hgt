# Box convolutions pay a fixed cluster depth deficit

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** Exterior mass in the Turán cluster receiver; M7/A78.
- **Status:** Exterior estimate, fixed-deficit receiver, and uniform prime
  and remainder costs formalized. General cluster geometry remains open.

## Exterior mass

Set `w=zetaZeroWidth`, `Bₙ=boxPlateau A h (n+1) r`,
`δₙ=A+(n+1)h+r`, and `Kₙ,y(u)=Bₙ(u-y)exp(-wu)`, with `A,h,r>0`.
The smooth profile `Bₙ` is nonnegative, supported in `[-δₙ,δₙ]`, has
mass `2A`, and is bounded by one. The full zero field is absolutely summable.

For `y≥δₙ`, every finite exterior set whose zeros of depth at least `w-d`
have ordinate distance at least `g>0` has total multiplicity-weighted norm
mass at most

`[(2/h)(1+g²)/g² (hg)⁻ⁿ + (4A+4/h)exp(-d(y-δₙ))] lorentzMass(t)`.

Shallow zeros require no separation. The existing logarithmic Lorentzian
mass estimate supplies the entire height cost.

Lean: `sum_widthCenteredBoxCamera_exterior_le_deep_gap` and
`summable_widthCenteredBoxCamera` in `TheBoxCameraPaysItsExteriorMass`.

## Fixed positive depth deficit

For fixed `A,h,r,g,d>0`, `hg>1`, `N≥1`, and `L≥0`, there is a fixed
`η>0` such that, for all sufficiently large `n` and all centres satisfying
`log(|t|+4)≤L(n+1)`, every core `s` satisfying

- at most `N` distinct zeros, with arbitrary multiplicities;
- `|Im ρ-t|δₙ≤1/10` for every `ρ∈s`;
- some `ρ∈s` has depth at least `w-η`;

has either a lag `y=ν(h+2)(n+1)`, `1≤ν≤N`, at which the full field has norm
at least

`(A/2)κ(N,0) exp(-η[N(h+2)+h+1](n+1))`,

or a zero outside `s` of depth at least `w-d` and ordinate distance less
than `g`. No exterior-mass or gap premise appears in this alternative.

Lean: `exists_fixed_deficit_box_cluster_visible_or_deep_companion` in
`BoxCamerasPayFixedDepthDeficits`.

More generally, suppose `y_min-δₙ≥a(n+1)`, `y_max+δₙ≤b(n+1)`,
`exp(ηb)<hg`, and `ηb<da`. The relative exterior cost tends to zero:
its two ratios are `exp(ηb)/(hg)` and `exp(ηb-da)`, both below one.
For positive `a,b,d` and `hg>1`, one can take
`η=min(log(hg),da)/(2b)`.

Lean: `eventually_box_cluster_visible_or_deep_companion`,
`tendsto_boxRelativeExteriorMajorant`, and
`exists_positive_box_depth_deficit`.

## Uniform arithmetic costs

Write `Pₙ,b=boxCameraPoly A h n r b`. For `δₙ=c log T`, fixed `c₀>0`,
`c₀≤c<1/3`, `b≥0`, `δₙ≤y`, and `y+δₙ≤(1-c)log T`, eventually

`∫_[T,2T] ‖Pₙ,b(y,t)‖² dt ≤ 8T(log T)² exp(-2b(y-δₙ))`.

The threshold is uniform in `n,c,b,y`. Lean:
`eventually_integral_boxCameraPoly_sq_le` in `TheBoxCameraPrimeCost`.

For `δₙ<y`, `t≥1`, and `exp(y+δₙ)≤t`, the actual explicit-formula
remainder satisfies

`‖widthCenteredBoxZeroField + Pₙ,w‖ ≤ C(4A+4/h)exp(-w(y-δₙ))(1+log(2+t))`,

with universal `C`. Lean: `exists_norm_widthCenteredBoxZeroField_add_poly_le`
in `TheBoxCameraRemainder`.

## Mechanism and boundary

Reserve the initial interval and one box factor for a summable Lorentzian
envelope; each remaining box pays `1/(hg)`. Actual-width centering removes
exponential amplification. Exact rescaling connects these profiles to the
existing Turán receiver. The same envelope pays gamma and pole terms;
the unit profile bound pays prime mean square without derivative losses.

Varying convolution order replaces the former `E/log T` deficit by a fixed
positive deficit, respecting the obstruction for a single fixed compact
profile. A bounded core alone gives no uniform deep exterior gap. The
original arbitrary-cluster `ClusterAt` and full A78 remain open.
