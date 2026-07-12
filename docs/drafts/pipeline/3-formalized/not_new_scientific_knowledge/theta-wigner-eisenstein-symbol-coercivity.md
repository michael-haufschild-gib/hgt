# The theta Wigner--Eisenstein archimedean symbol is sharply coercive

- **ID:** `theta-wigner-eisenstein-symbol-coercivity`
- **Stage:** 3-formalized
- **Type:** THEOREM / HILBERT--POLYA SOURCE INFRASTRUCTURE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaWignerEisensteinSymbol.lean`

## Statement

The Wigner--Eisenstein calculation for the Hedenmalm theta source produces the conjugate
fourth-order dilation factors

```text
((D-1/2)^2+b^2)((D+1/2)^2+b^2).
```

At logarithmic Fourier frequency `tau`, their scalar symbol is

```text
p_b(tau)=|(i tau-1/2)^2+b^2|^2
        =(b^2+1/4-tau^2)^2+tau^2.                        (1)
```

Its exact lower edge is

```text
m(b)= (b^2+1/4)^2,  |b|<=1/2,
      b^2,            |b|>1/2.                           (2)
```

For every real `b,tau`,

```text
0<m(b)<=p_b(tau),                                        (3)
```

and equality is attained at

```text
tau=0,                         |b|<=1/2,
tau=+-sqrt(b^2-1/4),           |b|>1/2.                  (4)
```

The same module identifies the elementary centered completion weight

```text
q_b(a)=|((a+i b)^2-1/4)|^2
      =((a-1/2)^2+b^2)((a+1/2)^2+b^2)                    (4a)
```

and proves

```text
q_b'(a)=4a(a^2+b^2-1/4).                                  (4b)
```

Thus for `a>0` the completion points toward the Euler half-plane exactly outside the radius-`1/2`
central disk, and points oppositely inside it.

The ordered-pair polynomial in the theta Wigner expansion is also formalized:

```text
(c^2 e^(4v)-3c e^(2v))(c^2 e^(-4v)-3c e^(-2v))
 =c^4-6c^3 cosh(2v)+9c^2.                                (4c)
```

This is the algebraic collapse that removes the theta-index ratio from the Bessel kernel; the
ratio survives only in the separate divisor-character phase.

## Proof

Equation `(1)` is direct complex algebra.  Put `u=tau^2` and `A=b^2+1/4`.  Then

```text
p_b(tau)=(A-u)^2+u.
```

If `b^2<=1/4`,

```text
p_b(tau)-A^2
 =u(u+1/2-2b^2)>=0.                                     (5)
```

If `b^2>1/4`,

```text
p_b(tau)-b^2
 =(u-(b^2-1/4))^2>=0.                                   (6)
```

Equations `(4)` follow by equality in `(5)` and `(6)`.

## Hilbert--Polya consequence

The archimedean differential operator in the Wigner--Eisenstein orientation current has no null
frequency and no negative spectral direction.  Its inverse is bounded on each fixed Eisenstein
frequency fiber by `m(b)^(-1)` at the scalar-symbol level.

This does not orient the Xi Bezoutian.  The remaining sign lies in the mixed pairing of this
coercive archimedean image with the divisor-character coefficients

```text
tau_b(n)=n^(i b)sigma_(-2 i b)(n)
```

and the cofinal radial test.  Positivity of the operator symbol is therefore infrastructure for
the source carrier, not a replacement for the arithmetic orientation theorem.

## Formal declarations

- `thetaWignerEisensteinSymbol_eq_normSq`
- `thetaWignerEisensteinSymbol_neg`
- `thetaWignerEisensteinFloor_pos`
- `thetaWignerEisensteinFloor_le_symbol`
- `thetaWignerEisensteinSymbol_pos`
- `exists_thetaWignerEisensteinSymbol_eq_floor`
- `thetaWignerEisensteinFloor_eq`
- `thetaXiCompletionRadialWeight_eq_normSq`
- `hasDerivAt_thetaXiCompletionRadialWeight`
- `deriv_thetaXiCompletionRadialWeight`
- `deriv_thetaXiCompletionRadialWeight_pos`
- `deriv_thetaXiCompletionRadialWeight_neg`
- `thetaWignerAtomPair_polynomial`

## Novelty verdict

The sharp minimum is elementary completion of squares.  Its role in the Wigner--Eisenstein route
is useful, but the theorem does not clear the novelty gate independently.
