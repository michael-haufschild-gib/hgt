# Additive Taylor-error route to sharp Bourgain `A₆`

- **Status:** RETIRED AS A ROUTE TO THE SHARP BILINEAR INPUT
- **Date:** 2026-07-25
- **Target:** Bourgain (2.23),
  `globalPairMoment(N,M) ≪ε N^(4+ε) M²` in normalized coordinates,
  equivalently `≪ε N^(10+ε) M²` in physical coordinates.

## Route tested

Replace each exact square-root block on a radius-`O(M²)` physical ball by
its quadratic osculating model. Apply exact planar `L⁶×L⁶` decoupling to
the model, then bound the difference of the two bilinear sixth-power
products by the pointwise additive Taylor-error inequality.

## Structural obstruction

The quadratic main term has the sharp physical size
`N^(10+ε) M²`. The additive error comparison bounds each block-sum error
by a fixed constant times its coefficient `ℓ¹` mass. After sixth powers
and local volume, this contributes at scale `N¹⁰ M^(4+ε)`.

Thus the clean theorem produced by this route,

`localPairMoment ≤ Cε N¹⁰ M^(4+ε)`,

loses two powers of `M` against Bourgain (2.23). A global domain contains
the local ball, so cube covering or periodic averaging cannot recover a
uniform `M⁻²` factor from this nonnegative local estimate. The loss occurs
before multiscale summation.

## Positive survivor

The route did produce unconditional, reusable Lean theorems:

- exact arbitrary-start block localization and phase determinant;
- exact sharp main term `N^(10+ε)M²` before perturbation;
- uniform square-root third-jet and local phase-error bounds;
- translated local pair estimate `N¹⁰M^(4+ε)`;
- complete three-color pair summation and local recurrence interface;
- exact color-fiber simplification and arbitrary-start block partition.

These are formalized in:

- `BourgainA6BlockLocalization.lean`;
- `BourgainA6TaylorErrorAbsorption.lean`;
- `BourgainA6LocalBallGeneral.lean`;
- `BourgainA6LocalMajorant.lean`;
- `BourgainA6LocalRecurrence.lean`;
- `BourgainA6DiagonalRecurrence.lean`.

## Replacement hypothesis

Sharp `M²` requires a perturbation-stable decoupling/localization theorem
that treats the exact normalized curve `(t,t²,φ₃(t),φ₄(t))` directly, as
in Bourgain (2.10)--(2.23). Suitable replacements include weighted
wave-packet/multiplier control or an equivalent robust discrete
decoupling theorem. Pointwise additive comparison of exact and quadratic
sums is insufficient.
