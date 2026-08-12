# Mass-shifted projective outlier and angular-energy law

- **ID:** `mass-shifted-projective-outlier-angular-energy`
- **Stage:** 3-formalized
- **Type:** unconditional exact identity / positive decomposition
- **Lean module:**
  `GaloisForLFunctions.RHTower.AngularPolynomialLaguerreEnergy`
- **Depends on:** `mass-shifted-projective-gauss-root-renewal`

## Result

For a real polynomial `Q`, its cosine-circle evaluation has exact velocity

```text
v_Q(theta) = -sin(theta) Q'(cos(theta)).
```

Full-period integration by parts proves

```text
2 integral v_Q^2
  = integral [cos(theta) Q(cos(theta)) Q'(cos(theta))
      + sin(theta)^2 L1[Q](cos(theta))],
L1[Q] = (Q')^2 - Q Q''.
```

For real-split `Q`, corpus linear peeling makes `L1[Q]` a root-deletion sum of squares, so its
angular density and full integral are nonnegative.

For any finite root multiset `r`, empirical center `mean`, and `eta>=0`, exact quadratic counting
gives

```text
eta^2 * #{x in r : eta <= |x-mean|} <= quadraticSpread(r).
```

Specialized to current canonical admissions,

```text
eta^2 * projectiveGaussRootOutlierCount <= projectiveGaussRootSpread,
2(2n+1) eta^2 * projectiveGaussRootOutlierCount
  <= projectiveJacobiRetainedInventory.
```

Thus retained adaptive mixed/completed arithmetic source pays the exceptional-root parameter used
by constrained-zero Bernstein theory. This is source-first: no fixed reporter or added
orientation map appears.

## Proof

1. Differentiate `Q(cos(theta))` twice using polynomial evaluation and the cosine chain rule.
2. Integrate the product of evaluation and angular velocity over `[-pi,pi]`. Endpoint velocity is
   zero, so integration by parts has no boundary remainder.
3. Substitute the second derivative and rearrange; the remainder is exactly `L1[Q]`.
4. Apply corpus theorem `laguerreL1_eval_nonneg` for real-split `Q` and integrate its nonnegative
   sine-square multiple.
5. Every root outside radius `eta` contributes at least `eta^2`; sum over the filtered multiset.
6. Expand squares at the empirical mean to identify centered sum exactly with
   `multisetQuadraticSpread`.
7. Apply the already-proved retained-inventory root-spread lower bound.

## Conjecture / failure / pivot audit

- Raw root spread cannot equal angular energy: repeated-root polynomials have zero spread but
  angular energy of order degree.
- A one-line universal upper bound remains unproved and is unnecessary.
- Exact outlier counting supplies `k=o(n)` under empirical spread collapse.
- Sharp constrained-zero `L2` Bernstein theory has correct energy scale `n(k+1)`.
- Remaining nonformalized bridge is analytic localization: the shrinking central root arc must
  have negligible normalized mass, and exterior interval estimates must transfer through the
  original arcsine/Cayley measure.

## Lean capstones

- `HTGeometry.sq_mul_multisetQuadraticOutlierCount_le_centeredSum`
- `HTGeometry.multiset_sum_centered_sq_eq_quadraticSpread`
- `HTGeometry.sq_mul_multisetQuadraticOutlierCount_le_quadraticSpread`
- `RHTower.angularPolynomialEnergy_eq_transport_add_laguerre`
- `RHTower.integral_angularPolynomialLaguerreDensity_nonneg`
- `RHTower.integral_angularPolynomialTransport_le_two_energy`
- `RHTower.XiShiftedCanonicalAdmission.sq_mul_projectiveGaussRootOutlierCount_le_spread`
- `RHTower.XiShiftedCanonicalAdmission.projectiveGaussRootOutlierWork_le_retainedInventory`

## Status

Direct module verification and targeted build pass. Axiom audit contains only standard Mathlib
foundations. No RH claim.
