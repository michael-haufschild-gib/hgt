# Pointwise moment quotient signed-ghost obstruction

- **ID:** `pointwise-moment-quotient-signed-ghost`
- **Stage:** 3-formalized
- **Type:** `[POSITIVE NO-GO] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/MomentTowerQuotientGhost.lean`
- **Parent:** `../../1-in-progress/prime-arch-dual-cauchy-rsk-fredholm-rh.md`

## Statement

Positive moment towers are closed under pointwise multiplication but not under pointwise division.
For the positive two-atom tower

```text
m_x(n)=1+x^n,
```

the tensor product identity is

```text
m_x(n)m_y(n)=1+x^n+y^n+(xy)^n,
```

the moment tower of the positive four-atom product measure.  Scalar deconvolution instead has the
exact signed decomposition

```text
(1+X)/(1+Y)=1+X-Y+Y(Y-X)/(1+Y).                         (1)
```

If `0<Y<X`, the last term is strictly negative.  The sign is not merely a bad presentation: for
`x=1/2`, `y=1/3`, the shifted `3 x 3` Hankel determinant of

```text
q_n=(1+x^n)/(1+y^n)
```

is strictly negative already at shift one.  Hence `q` is not a positive moment tower although its
numerator and denominator both are.

## Positive theorem extracted from the obstruction

The universally positive operation is tensor multiplication, not scalar spectral division.  A
prime--archimedean determinant construction may therefore use pair products of source-built
positive spectra directly.  If a scalar quotient is introduced as a diagnostic coordinate, every
negative quotient mode must be retained as a graded or signed channel and cancelled by an explicit
source differential before passing to positive cohomology.  It cannot be discarded by asserting a
positive representing measure.

For the model quotient with `0<y<x<1`, expansion of `(1)` at powers gives the ordered leading
virtual atoms

```text
1 with weight +1,
x with weight +1,
y with weight -1.
```

Consequently the shifted `3 x 3` determinant is eventually governed by

```text
-(xy)^N ((1-x)(1-y)(x-y))^2,
```

which explains the negative chamber.  This asymptotic refinement is proved on paper by expanding
`1/(1+y^n)` as a geometric series; the Lean file banks the exact signed decomposition, the strict
ghost sign, the positive tensor law, and an exact rational Hankel counterexample.

## Lean surface

```text
twoAtomMomentTower
twoAtomMomentQuotient
shiftedHankelDetThree
twoAtomMomentTower_mul
twoAtomMomentQuotient_eq_signedGhost
signedGhostRemainder_neg
twoAtomMomentQuotient_half_third_hankelDetThree_neg
```

## Gates

- [x] exact positive tensor-product law formalized
- [x] exact signed quotient decomposition formalized
- [x] negative ghost sign formalized
- [x] explicit negative shifted Hankel determinant formalized
- [ ] abstract eventual-negative determinant asymptotic formalized

