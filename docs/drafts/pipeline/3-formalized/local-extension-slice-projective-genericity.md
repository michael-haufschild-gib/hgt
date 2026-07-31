# Local-extension slice projective genericity

- **ID:** `local-extension-slice-projective-genericity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LocalExtensionSliceProjectiveGenericity.lean`

## Exact law

Start with a finite maximally projective spectrum. Add one finite local
factor through onsite shifts and a real-symmetric edge matrix, coupled by a
Hermitian old-system transition family whose lifted support graph is
connected. Then some real observable combination gives a maximally
projective extension. In the resulting finite real-affine physical slice,
maximally projective spectra form a set that is simultaneously:

- dense;
- residual;
- full Lebesgue measure.

This replaces an eigenbasis-engineered existence statement by an exact
finite local-extension parameter-space law.

## Formal declarations

- `hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix`;
- `maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket`;
- `hermitianLocalExtensionSliceMaximalSet_eq_realAffine`;
- `hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_family`.

## Scope

This theorem concerns a finite tensor-local extension slice. It does not by
itself prove that a standard random-field XXZ or Anderson--Hubbard ensemble
is localized, that an endpoint transition operator is physically local
after spectral conjugacy, or that the law survives a thermodynamic limit.

## Verification

Direct target compilation passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/LocalExtensionSliceProjectiveGenericity.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LocalExtensionSliceProjectiveGenericity.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
