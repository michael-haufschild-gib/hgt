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

The original core-cardinality bound controls neither exterior
multiplicities nor surrounding annuli. It does not imply an empty annulus.
The required near-top sector geometry and deep gap have not been proved
for arbitrary ζ clusters. The old `ClusterAt` and full A78 remain open.

Separately, `TheStripPaysTheVeryDeepCameraNoise` removes the hyperbolic
camera's very-deep mass premise when `3c log T≤(1-3c)α`; its Blaschke-product
condition remains.
