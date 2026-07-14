# Finite-gauge tail-charge topology

- **ID:** `finite-gauge-tail-charge-topology`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOPOLOGICAL-ANALYTIC BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW IN ISOLATION]`
- **Parent route:**
  `../../1-in-progress/finite-euler-gauge-critical-divisor-tail-charge.md`

## Statement

Two general facts support the critical-divisor tail-charge law.

First, let `q` be an invariant on an arbitrary product space such that changing finitely many
coordinates does not change `q`.  Every nonempty fiber of `q` is dense.  If `q` is surjective, the
coinduced topology on its charge space is the indiscrete topology.  Every continuous `T0` readout
that is constant on the charge fibers is therefore constant globally.

Second, for a real prime parameter `p>1`, a complex phase `omega` of norm one, and `Re(s)>0`,

```text
abs(exp(-s log p)) = exp(-Re(s) log p) < 1,
1 - omega exp(-s log p) != 0.
```

Consequently the ratio of two local unimodular Euler factors is a holomorphic nonvanishing
function on the positive half-plane.  Every finite product of such ratios remains holomorphic and
nonvanishing there.

## Proof

Finite modifications of any point are dense in the product topology.  Invariance includes this
dense set in the fiber through the point, proving density.  If `U` has open inverse image under a
surjective charge map and contains one charge, that inverse image is nonempty.  The dense fiber of
every charge must meet it, so `U` contains every charge.  Hence the coinduced topology is
indiscrete.  The `T0` collapse follows by separating two hypothetical readout values with an open
set and intersecting its open inverse image with the opposite dense charge fiber.

For the Euler factor, the exponential norm identity gives the displayed strict inequality.  If
`1-omega exp(-s log p)` vanished, its second term would have norm one, contradicting strict
contractivity.  Differentiability follows from the complex exponential, finite products, and
division by the nonvanishing denominator.

## Scientific role

Neither dense-orbit quotient collapse nor the elementary Euler-factor estimate is new in
isolation.  Together they isolate the reusable mechanism of the parent theorem: a divisor
protected from finite Euler gauges becomes a singular tail charge whose finite-chamber quotient
has no nontrivial separated topology.

## Formal theorem surface

The implementation is
`formal/GaloisForLFunctions/HTGeometry/FiniteGaugeTailCharge.lean` and contains:

- `dense_fiber_of_finiteModification_invariant`;
- `coinduced_eq_indiscrete_of_dense_fibers`;
- `continuous_constant_of_dense_fibers`;
- `positiveHalfPlane`;
- `analyticPrimeDecay`;
- `norm_analyticPrimeDecay`;
- `norm_analyticPrimeDecay_lt_one`;
- `one_sub_phase_mul_analyticPrimeDecay_ne_zero`;
- `localEulerGaugeRatio` and `localEulerGaugeRatio_ne_zero`;
- `finiteEulerGaugeRatio` and `finiteEulerGaugeRatio_ne_zero`;
- differentiability of the local and finite gauges on the positive half-plane.

## Gates

- [x] finite-modification invariant fibers proved dense
- [x] dense-fiber coinduced topology proved indiscrete
- [x] continuous `T0` fiber-readout collapse proved
- [x] prime-decay norm and strict contraction proved
- [x] local and finite Euler gauges proved nonvanishing
- [x] local and finite Euler gauges proved holomorphic on `Re(s)>0`
- [x] direct module check passed
- [x] narrow module build passed
- [x] axiom audit completed
- [x] project lint and generated indexes refreshed
