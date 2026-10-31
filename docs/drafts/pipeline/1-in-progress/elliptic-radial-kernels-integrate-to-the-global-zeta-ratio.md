# Elliptic radial kernels integrate to the global zeta ratio

- **Stage:** 1-in-progress
- **Parent:** [Arithmetic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** The actual adelic radial kernel
  `K_s(a)=∏_v max(1,|a_v|)^(-s-1)` is integrable for `Re(s)>1`,
  with integral `ζ_K(3^(-s))/ζ_K(3^(-s-1))`.
  Restricted-product integrality makes its defining product finite.

## Proof mechanism

The ultrametric inequality gives `max(1,v(x+y))=max(1,v(x))` when
`v(y)≤1`. Hence the kernel is constant on translates of the open integral
adelic subgroup and is continuous.

Each finite cylinder carries normalized local Haar times integral-tail
probability and infinity Haar. The tail kernel is one. Finite-product
Fubini and the audited local spectral integrals therefore give the exact
finite product of local zeta ratios.

For real `s>1`, the kernels restricted to increasing cylinders are
nonnegative and increase to the global kernel. Monotone convergence and
the audited unordered Euler product give its finite global integral.
For complex `s`, its norm is the real kernel at `Re(s)`; domination passes
the finite-cylinder identities to the same zeta ratio.

## Dependencies

- [Actual local spectral integrals](../3-formalized/actual-elliptic-local-spectral-characters-have-exact-integrals.md): audited.
- [Finite-cylinder measure identity](../3-formalized/elliptic-adelic-haar-has-exact-finite-cylinder-products.md): audited.
- [Finite-cylinder spectral integrals](../3-formalized/elliptic-finite-cylinder-spectral-integrals-factor-exactly.md): audited.
- Actual global kernel, integral-translation invariance and exhaustion limit:
  unformalized.

Identifying this radial kernel with the loop Iwasawa section remains a
separate input to arithmetic unfolding.
