# Paying the outside mass of a Turán cluster

- **Stage:** 1-in-progress
- **Target:** Discharge the exterior-mass premise of `ClusterAt`.
- **Status:** Near-top case formalized under a deep ordinate gap;
  arbitrary bounded clusters remain open.

## Formalized exterior estimate

Set `b=zetaZeroWidth` and `K_b(u)=exp(-bu)K(u)`. Every zero has
nonpositive relative depth. If exterior zeros of depth at least `b-d`
have ordinate distance at least `g`, their complete norm mass is at most

`profileMass(v)[(1+g²)/(δ²g²)+exp(-d(y-δ))] lorentzMass(t)`.

All multiplicities are included. Shallow zeros need no separation.
`lorentzMass(t)=O(log |t|)` is supplied by the corpus.

For `δ=c log T`, `y-δ≥a log T`, and positive `a,c,d,g`, the bound is
`C/log T`, with

`C=8 profileMass(v)(Cξ+2)[(1+g²)/(c²g²)+4/(da)²]`.

Lean: `TheDepthCenteredCameraPaysItsExteriorMass`,
`sum_widthCenteredCamera_deep_exterior_le_inv_log` in
`TheCenteredCameraPaysTheTuranLoss`.

## Formalized Turán receiver

A sector cluster of at most `N` distinct zeros, containing a zero of depth
at least `b-E/log T`, is visible at one lag `ν A log T`, `M+1≤ν≤M+N`,
provided `c<(M+1)A` and the stated deep exterior gap holds. For sufficiently
large T its field norm is at least

`(∫v)/4 κ(N,M) exp(-E((M+N)A+c))`.

The full fixed Turán loss is paid; no mass premise remains.
Without the gap assumption: either this visibility holds, or another
zero outside the cluster has depth at least `b-d` and distance less than `g`.

Lean: `eventually_exists_nu_widthCenteredZeroField_ge`,
`eventually_widthCentered_cluster_visible_or_has_deep_companion` in
`TheCenteredCameraPaysTheTuranLoss`.

## Prime side

`TheWidthCenteredCameraPrimeCost` proves the mean-square gain
`exp(-2b(y-δ))`, with an explicit constant uniform in b and the centre.
The arithmetic square-weight bound is supplied, not assumed.

`TheCenteredCameraRemainder` proves the remainder bound
`C_v exp(-b(y-δ))(1+log(2+t)/δ)` under the usual support and length conditions.
Its constant depends only on the original profile; tilting introduces no
uncontrolled profile constant.

## Remaining obstruction

[Varying box profiles](../3-formalized/box-convolutions-pay-a-fixed-cluster-depth-deficit.md)
now pay a **fixed positive depth deficit**, with uniform prime mean-square
and explicit-formula remainder costs. Every eligible sector cluster is
visible or has a deep exterior companion; no mass premise remains in that
alternative. This strengthens the fixed-profile result above.

The original core-cardinality bound controls neither exterior
multiplicities nor surrounding annuli. It does not imply an empty annulus.
The required near-top sector geometry and deep gap have not been proved
for arbitrary ζ clusters. The old `ClusterAt` and full A78 remain open.

[The original mass condition itself forces deep isolation](../3-formalized/cluster-mass-control-forces-deep-isolation.md).
For a target on or right of the critical line, every equally deep or deeper
zero at a different ordinate must satisfy
`4 ≤ κ(N,M)(1+(δ|γq−γρ|+1/10)²)`.
A companion within `1/δ` therefore rules out `ClusterAt`, for every core
bound `N`. The opposite endpoint of the target's centre window puts that
companion outside the sector; its singleton mass exceeds the allowance.
Distinct ordinates of right-half-strip zeros satisfying `ClusterAt` are
automatically more than `1/δ` apart. These statements are formalized in
`ClusterMassControlForcesDeepIsolation`; existence of obstructing ζ pairs
is not asserted.

`eventually_volume_rightDepthMass_gt_le` already controls depth mass outside
a set of window centres of measure `o(T)`. This does not control the selected
cluster centres: every centre containing a zero of fixed positive depth has
a fixed positive depth-mass contribution and may belong to that exceptional set.

Separately, `TheStripPaysTheVeryDeepCameraNoise` removes the hyperbolic
camera's very-deep mass premise when `3c log T≤(1-3c)α`; its Blaschke-product
condition remains.

## Adaptive-camera alternative

`ZeroConfigurationGeometry/NegativeTests/ZetaClusters` supplies actual ζ
clusters by an empty-annulus argument and pays the Fourier exterior mass:
`zeta_cluster_camera_explicit` annihilates every nearby exterior zero,
approximates one on the cluster to `1/4`, and bounds the full distant
multiplicity-weighted Fourier tail by `1/4`. The isolation logarithm is
controlled cubically in log height by `exists_zeta_camera_cluster` for
zeros deeper than `exp(-c log³(T/(2π)))`.

This changes the camera. It does not prove `ClusterAt` for the original
fixed profile or provide its uniform prime mean-square cost. Thus adaptive
annihilation removes exterior interference but does not close A78.

`RHTower/HodgeClusterNyquistExclusion` gives a second replacement: divide
Riemann's kernel by the full cluster divisor, interpolate its nodes, then
truncate. `ClusterSetup.test_off_node` bounds every exterior Fourier value
by the truncation tail, and `re_W_le_nodes_add` sums the full exterior
contribution with its multiplicities. Internal cluster separation is absent.
Its stated horizon is of Nyquist size `T≈2 exp(2a-3/4)`; the interpolation
norm retains an `exp(πT/4)` cost. This supplies neither the original fixed
Turán mass condition nor its shorter-aperture uniform prime estimate.
