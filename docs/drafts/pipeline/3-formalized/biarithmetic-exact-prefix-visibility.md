# Exact prefix visibility within a covariance fibre

- **ID:** biarithmetic-exact-prefix-visibility
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Biarithmetic Geometry foundations](../1-in-progress/biarithmetic-geometry-foundations.md); report research topic 1.
- **Statement:** The covariance fibre of a finite divisor row has exact centered-prefix radius `V=Σ|R_q(M)Y_q|` and diameter `2V`. Covariance determines the prefix exactly when every visible mode vanishes.

## Gates

- [x] Exact finite-row source and readout retained.
- [x] Dependency-closed paper proof.
- [x] Direct Lean leaf check passed.
- [x] Transitive axiom audit passed: only `propext`, `Classical.choice`, `Quot.sound`.

## Theorem and proof

[PROVED HERE] Fix `N,M` and a real divisor row `c`. Write `Y_q` for its Selberg multiples
coordinate and `R_q(M)=Re(pmRamanujanPrimitive q M)`. The corpus supplies the exact signed
expansion

`L_N(M,c)=Σ_(q=2)^N R_q(M)Y_q`.

It also proves that equality of complete-period lag covariances is equivalent to equality of
the squared nonconstant Selberg coordinates. Therefore any row `d` in the covariance fibre of
`c` has the same coordinate magnitudes, and the triangle inequality gives

`|L_N(M,d)|≤V_N(M,c):=Σ_(q=2)^N |R_q(M)Y_q|`.

Choose independent signs on the nonconstant coordinates to agree with the signs of the real
products `R_q(M)Y_q`. The exact inverse Selberg map produces a row attaining `+V`; opposite
signs produce a row attaining `-V`. Set the constant coordinate sign to 1. Both rows preserve
every complete-period lag covariance and the mean. Thus the diameter is exactly `2V`.

If covariance determines the centered prefix, the two extrema must agree, forcing `V=0`.
Conversely `V=0` forces every readout in the fibre to be zero by the universal bound. A sum of
nonnegative absolute values vanishes exactly when every summand vanishes, giving the exact
criterion `R_q(M)Y_q=0` for every active mode.

The fibre is a finite sign image and need not contain every point of the interval `[-V,V]`.
Only its exact extrema, radius, and diameter are asserted.

## Exact Lean statements

Module: `GaloisForLFunctions/BiarithmeticGeometry/ExactPrefixVisibility.lean`.

- `prefix_readout_sign`, `abs_prefix_readout_sign_le`.
- `prefix_visibility_extrema`, `prefix_visibility_diameter`.
- `prefix_sign_periodCovariance`, `prefix_sign_mean`.
- `abs_prefix_readout_le_of_covariance_eq`.
- `prefix_covariance_determines_iff`, `prefixVisibility_eq_zero_iff`.

Direct command passed: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ExactPrefixVisibility.lean`.
The main corpus dependencies are BVI's `sievePrefixDiscrepancy_eq_ramanujan_diagonal` and
`sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq`.

## Contribution and limits

The result upgrades a blindness example to a complete quantitative information criterion at
each finite prefix. It retains the exact mode dependence; a scalar horizon/period ratio does
not encode these products. Its proof is finite signed linear algebra on the actual integer
divisor/Ramanujan system. It is a structural observation theorem for arbitrary real rows,
including parity-modified rows, rather than a source-selective bound for the Möbius row.
No improvement of an analytic band, certified window, or Vaughan off-diagonal estimate follows
without a new bound on the actual source's visibility.
