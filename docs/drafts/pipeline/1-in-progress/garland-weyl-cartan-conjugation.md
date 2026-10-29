# Actual Weyl conjugation on the central Cartan and degree rotation

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** Identify the abstract affine weight action with conjugation by
  explicit elements of the constructed central loop group.

## Dependency and novelty audit

Corpus search found the proved torus defect, relative Weyl-word formula, and
stable Steinberg Weyl conjugation. The stable statements do not identify the
rank-one Kubota lift, so the latter must be checked directly. The required
inputs are the actual tame pairing, its bilinearity, the proved rotation
automorphism, and the split finite coroot. This is established affine
Kac–Moody structure, with no novelty claim.

## Dependency-closed paper proof

Write `z(c)` for the center, `H(a)=D(const a)` for the finite coroot, and
`N_m=D(X^(-m))`. Bilinearity and `T(const a,X)=a` give

`T(const a,X^n)=a^n`, `T(X^n,const a)=a^(-n)`.

The proved inverse-tame torus defect therefore gives

`N_m H(a) N_m^-1 = z(a^(-2m)) H(a)`.

Degree rotation sends `X^n` to `q^n X^n`. Since
`D(u)D(v)=z(T(u,v)^-1)D(uv)`, it follows that

`rotation(q)(N_m)=z(q^(m²)) H(q^(-m)) N_m`.

In the actual semidirect product, with `mu(q)` the rotation element,

`N_m mu(q) N_m^-1 = z(q^(-m²)) H(q^m) mu(q)`.

Combining the identities, conjugation by `N_m` sends the full Cartan triple

`(c,a,q)` to `(c * a^(-2m) * q^(-m²), a * q^m, q)`.

The finite Weyl lift `W(1)` inverts `H(a)`, fixes the center, and commutes
with degree rotation. Its matrix identity is direct. Its central defect is
zero: the only extra symbol is twice a self-pairing, which vanishes by
antisymmetry (equivalently its multiplicative square is one).

Pullback along inverse translation therefore sends a weight
`(kappa,b,d)` to `(kappa,b+2m*kappa,d-m*b-m²*kappa)`, matching the
previously proved abstract affine action. The finite reflection reverses
the finite coordinate. Representatives need not multiply exactly:
their central defects cancel in conjugation, and no representative
homomorphism is asserted.

## Status

Paper identities recorded. Lean implementation and dependency audit pending.
These identities do not supply global Iwasawa decomposition, an arithmetic
lattice, or Eisenstein convergence and unfolding.
