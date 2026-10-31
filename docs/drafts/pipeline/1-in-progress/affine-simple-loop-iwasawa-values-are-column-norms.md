# Affine simple loop Iwasawa values are column norms

- **Stage:** 1-in-progress
- **Parent:** [Local Iwasawa kernels](local-spherical-kernels-read-normalized-iwasawa-magnitudes.md).
- **Target:** For a valued coefficient field and `g∈SL₂`, the affine-simple
  embedding has Iwasawa torus valuations `(M,M⁻¹)`, where
  `M=max(v(g₀₀),v(g₁₀))`. Every full-loop integral–Borel factorization
  has these values.

## Proof mechanism

The proved coefficient-field integral–upper factorization writes `g=kb`,
with `k` integral, `b` upper triangular, and `v(b₀₀)=M`. The affine-simple
embedding carries `k` into the full integral loop subgroup. Write
`b=diag(a,a⁻¹)U(t)`. Its diagonal maps to the affine coroot, with torus
coordinates `(a,a⁻¹)`; its upper root maps to the positive loop root
`L(Xt)`, whose torus coordinates are one. The Borel valuations are therefore
`(M,M⁻¹)`. The proved uniqueness of full-loop Borel valuations removes
factorization choices. The lower coefficient-field root specializes to
`M=max(1,v(x))`.

The affine-simple embedding reverses the finite root orientation. The raw
shifted constant embedding does not have the stated positive-root convention.

## Lean

Pending: affine-root membership, exact torus coordinates, and assembly with
the already audited integral–upper factorization.
