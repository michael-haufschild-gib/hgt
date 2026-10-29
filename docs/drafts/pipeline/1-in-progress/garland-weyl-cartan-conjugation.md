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

## Character comparison

The extended Cartan embedding `(c,a,q) ↦ z(c)H(a)mu(q)` is an injective
homomorphism: rotation fixes the first two factors, and projection onto the
degree group followed by the previously proved Cartan injection recovers all
three coordinates. Thus its image has a genuine multiplicative coordinate
map, without an assumed decomposition outside that subgroup.

For real units define `ell(a)=log|a|`. This is additive on multiplication
and satisfies `ell(a^n)=n ell(a)` for every integer `n`. For a complex
weight `L=(kappa,b,d)`, the character is

`chi_L(c,a,q)=exp(kappa*ell(c)+b*ell(a)+d*ell(q))`.

Substitution into the proved conjugation formulas yields
`chi_L(N_(-m) g N_(-m)^-1)=chi_(translateWeight m L)(g)` and
`chi_L(W g W^-1)=chi_(reflectWeight L)(g)` for every element of the actual
extended Cartan subgroup. In positive exponential coordinates
`c=exp(z), a=exp(t), q=exp(-exp(r))`, the exponent equals the existing
`rotatedEvaluation L t z r`. This identifies the Weyl-sum exponent with a
character of the constructed group, while leaving the spherical extension
and Eisenstein-series theorem open.

## Status

Paper identities recorded. `LaurentMonomialTorus`, `SL2WeylConjugation`, and
`ExtendedCartanConjugation` compile at ordinary limits. They prove the actual
quadratic translation and finite-reflection formulas, with injective extended
Cartan embedding. `RealCartanCharacters` is being implemented to connect these
identities with the existing affine weight evaluation. Final direct source
checks and transitive axiom audit remain pending.
These identities do not supply global Iwasawa decomposition, an arithmetic
lattice, or Eisenstein convergence and unfolding.
