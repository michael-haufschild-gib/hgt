# The semilocal Gamma characteristic is not a positive sum-Hankel kernel

- **ID:** `gamma-characteristic-sum-hankel-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean core:** `formal/GaloisForLFunctions/RHTower/SoninSemilocalTwoPlaceAssociation.lean`
- **Statement:** The archimedean characteristic
  `phi(t)=(cosh t)^(-1/2)` has the exponential decay needed to damp prime-log frequencies, but
  `K(u,v)=phi(u+v)` is not positive semidefinite: its Gram determinant on `{0,t}` is strictly
  negative for every `t!=0`.

## Goal

Test the most direct sewing suggested by the prime-log Herglotz half-weight obstruction.  The
archimedean cyclic measure has characteristic function `phi(t)=(cosh t)^(-1/2)`, with
`phi(t)` asymptotic to a constant times `exp(-|t|/2)`.  This is exactly the missing exponential
scale at the critical half-weight.  If the sum-frequency kernel `phi(u+v)` were positive, it could
be used as a Gamma-damped Hankel Gram on the positive prime-log semigroup.

## Theorem

For every real `t!=0`,

```text
phi(2t)<phi(t)^2.
```

Consequently the two-point matrix

```text
[ phi(0)  phi(t)  ]
[ phi(t)  phi(2t) ]
```

has determinant

```text
phi(0)phi(2t)-phi(t)^2<0.
```

It is therefore indefinite.

## Proof

The addition formula gives

```text
cosh(2t)=cosh(t)^2+sinh(t)^2>cosh(t)^2
```

when `t!=0`.  The function `x |-> x^(-1/2)` is strictly decreasing on the positive half-line, so

```text
(cosh(2t))^(-1/2)<(cosh(t)^2)^(-1/2)=(cosh(t)^(-1/2))^2.
```

Since `phi(0)=1`, this is the asserted negative determinant.

## Route consequence

The Gamma characteristic supplies the right decay but in the wrong positivity geometry.  It is
positive definite as a difference-frequency kernel `phi(u-v)`, because it is a characteristic
function; that kernel has diagonal `1` and supplies no exponential damping.  The damped
sum-frequency kernel `phi(u+v)` is already indefinite on two nodes.

Thus Gamma cannot repair the prime-log positive-transport wall by scalar Hankel damping.  The
surviving object must retain a genuine cross-channel covariance, a relative trace, or an
operator-valued contraction in which the prime and archimedean components are sewn before the
positive square is taken.

## Lean certificate

The formal declarations are:

```text
semilocalArchimedeanCharacteristic_two_mul_lt_sq
semilocalArchimedeanCharacteristic_hankelDet_neg
```

The module builds with no `sorry`, `admit`, or added axiom.  The proof uses the exact hyperbolic
addition law and monotonicity of negative real powers.

## Gates

- [x] 0 -> 1: source-pure candidate isolated
- [x] 1 -> 2: complete two-point determinant proof
- [x] 2 -> 3: Lean declarations compile in the project toolchain
- [ ] 3 -> 4: not publication-significant as a standalone result

