# Actual elliptic simple roots have exact Iwasawa values

- **Stage:** 2-fully-proven
- **Parent:** [Local Iwasawa kernels](../1-in-progress/local-spherical-kernels-read-normalized-iwasawa-magnitudes.md).
- **Statement:** Every actual adele defines finite and affine negative simple
  root elements in the restricted adelic loop group. Their actual global
  integral–Borel factorizations have local torus valuations `(1,M_v)` and
  `(M_v,M_v⁻¹)`, respectively, at every finite place and infinity, where
  `M_v=max(1,v(a_v))`.

## Proof

An integral scalar gives a determinant-one integral lower-root matrix.
Both simple embeddings carry this matrix into the full coefficient-integral
loop subgroup. An adele has integral finite coordinates outside a finite
set, so both coordinatewise root constructions lie in the actual restricted
loop group.

Apply the audited global integral–Borel decomposition. Evaluation at any
place gives a genuine local factorization. The audited finite and affine
simple-root uniqueness formulas compute its torus valuations. This applies
at every finite place and infinity without any choice of a local uniformizer
or any extra analytic assumption.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticSimpleRoots.lean`:
`exists_adelicFiniteNegativeRoot_iwasawa_values` and
`exists_adelicAffineNegativeRoot_iwasawa_values`. Direct audit pending.
