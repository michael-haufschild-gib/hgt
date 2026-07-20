# Exact finite Steinhaus Laplace-product law

- **ID:** `finite-steinhaus-laplace-product`
- **Stage:** 3-formalized
- **Type:** THEOREM / PROBABILITY FOUNDATION / LARGE-DEVIATION INPUT
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Feeds:**
  `../../2-fully-proven/not_new_scientific_knowledge/regular-variation-weighted-steinhaus-ldp.md`

## Theorem surface

Let `U_i` be the first Fourier characters on independent Haar circles and let

```text
S_a(U)=sum_i a_i Re(U_i),
L(r)=integral exp(r Re(U)) dU.
```

For every finite index type, every real weight vector `a`, and every real `r`,

```text
integral exp(r S_a(U)) dU = product_i L(r a_i).
```

The same module proves, without assumptions:

```text
|Re(U)| <= 1,
exp(-|r|) <= L(r) <= exp(|r|),
1 <= L(r),
0 < L(r),
L(-r)=L(r),
0 <= log L(r) <= |r|,
log L is real analytic and strictly convex on R.
```

The half-period identity `Re(U(x+pi))=-Re(U(x))` supplies the exact symmetry.

## Formal artifact

`formal/GaloisForLFunctions/HTGeometry/SteinhausLaplaceProduct.lean`

Principal declarations:

```text
HTGeometry.integral_exp_weightedSteinhausProjection
HTGeometry.exp_neg_abs_le_steinhausLaplace
HTGeometry.steinhausLaplace_le_exp_abs
HTGeometry.steinhausLaplace_pos
HTGeometry.steinhausProjection_add_half_period
HTGeometry.steinhausLaplace_neg
HTGeometry.one_le_steinhausLaplace
HTGeometry.steinhausLogLaplace_nonneg
HTGeometry.steinhausLogLaplace_le_abs
HTGeometry.integrableExpSet_steinhausProjection
HTGeometry.analyticOnNhd_steinhausLogLaplace
HTGeometry.centered_tilted_projection_integral_pos
HTGeometry.iteratedDeriv_two_steinhausLogLaplace_pos
HTGeometry.strictConvexOn_steinhausLogLaplace
```

## Audit

- The source file passes its narrow Lean check.
- The result is an exact finite-product identity, not an asymptotic and not a probabilistic
  heuristic.
- It supplies only the one-circle/product-Haar layer.  It does not prove the triangular-array
  limit, the Gärtner--Ellis step, or the deterministic prime-log entropy-censoring conjecture.
- The mathematics is classical and is therefore recorded as infrastructure rather than novelty.
