# Gamma moving-base capacity congruence

- **ID:** `gamma-moving-base-capacity-congruence`
- **Stage:** 3-formalized
- **Type:** THEOREM / GENERAL HT FILTRATION COMPARISON
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [POSITIVE NO-GO SUCCESSOR] [NOT RH]`
- **Parent:** `gamma-factorial-asymptotic-connection.md`
- **Lean:** `GaloisForLFunctions.HTGeometry.GammaMovingBaseCapacityCongruence`

## Theorem

On the common inverse-Gamma collar, let `B_n` be the normalized inverse branch and let

```text
a_n=s_n/n,
D_n=B_n/(1-a_n B_n).                                      (1)
```

The chart change in `(1)` is the tangent Möbius germ `M_a(z)=z/(1-az)`.  Wherever `1-az!=0`,

```text
dM_a(z)=(1-az)^(-2) dz,                                  (2)
```

and hence its squared Hermitian tangent metric obeys

```text
|dM_a(z)v|^2=|v|^2/|1-az|^4.                             (3)
```

The selected Gamma collar has `|B_n(t)|<1`.  Once `|a_n|<1/2`, equations `(2)--(3)` give the
depth-independent congruence

```text
(16/81)|v|^2 <= |dM_(a_n)(B_n(t))v|^2 <= 16|v|^2.        (4)
```

Since `a_n->0`, the conformal factor in `(3)` tends uniformly to one on the collar.  Thus the
normalized inverse-branch filtration and the intrinsic moving-base filtration carry the same
local capacity geometry up to a uniformly bounded congruence, asymptotically tangent to the
identity.

## Proof

Differentiate the quotient in `(1)`:

```text
d(z/(1-az))=((1-az)+az)/(1-az)^2 dz=(1-az)^(-2)dz.
```

Taking norms proves `(3)`.  If `|az|<1/2`, the triangle inequality gives

```text
1/2<|1-az|<3/2.
```

Taking inverse fourth powers proves `(4)`.  On the Gamma collar, `|a_nB_n(t)|<=|a_n|`, and the
formalized factorial-shell law gives `a_n->0`.  `QED`

## General HT consequence

Uniform convergence of two source charts does not by itself compare their tangent capacity
forms.  For a source-selected Möbius comparison, the missing datum is precisely the conformal
cocycle `(1-az)^(-2)`.  If that cocycle stays in a bounded annulus, the two capacity filtrations
are boundedly congruent; if it escapes, its modulus is a positive **capacity-distortion field**.

This is the positive statement left by the wrong-filtration no-go.  It closes the local metric
comparison for the actual Gamma pole/moving-base charts, but it does not identify the pole-depth
filtration with the full intrinsic Kähler jet filtration and does not prove a zeta Ward estimate.

## RH-facing use

The Gamma chart can no longer be rejected as a possible Ward transport merely because the
normalized inverse branches and moving-base branches might carry unrelated local metrics.  Their
metrics are uniformly congruent by `(4)`.  The remaining zeta problem is global and derived: one
must couple this Gamma comparison to the squarefree Möbius boundary score and the Laurent
first-trace corona, then identify the anti-causal component with the reciprocal-horizon current.

## Gates

- [x] exact Möbius differential proved
- [x] exact Hermitian metric factor proved
- [x] depth-independent two-sided capacity congruence proved
- [x] Gamma common-collar specialization proved
- [x] Lean formalization checked directly
- [ ] full pole-depth to Kähler-jet comparison
- [ ] zeta Laurent/Hardy boundary transgression

