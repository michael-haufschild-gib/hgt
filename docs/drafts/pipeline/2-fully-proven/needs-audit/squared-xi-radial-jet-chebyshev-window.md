# Squared-Xi radial jets are completed Chebyshev windows

- **ID:** squared-xi-radial-jet-chebyshev-window
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / cancellation-preserving moving-source reduction
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [NOT FORMALIZED]`
- **Parents:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`; `reverse-bessel-fixed-frequency-blindness.md`
- **Statement:** The polar jet and the sign-aligned von Mangoldt jet are the Lebesgue and Chebyshev--Stieltjes integrals of one positive reverse-Bessel kernel; at fixed Euler base point, its normalized polar mass concentrates at `log x = n/(s(s-1))`.

## Exact pole--prime identity

Fix real `s>1`, put `w=s-1/2`, `a=s-1`, and let

```text
B_n(z)=sum_(j=0)^n b_(n,j) z^j,
f_(n,s)(x)=x^(-s) B_n(w log x),    x>=1.                (1)
```

Let

```text
psi(x)=sum_(m<=x) Lambda(m)
```

be the Chebyshev function.  Then

```text
sum_(j=0)^n b_(n,j) j! w^j/a^(j+1)
  = integral_1^infinity f_(n,s)(x) dx,                 (2)

sum_(m>=2) Lambda(m) m^(-s) B_n(w log m)
  = integral_[1,infinity) f_(n,s)(x) d psi(x).         (3)
```

Consequently the alternating radial jet of
`1/(s-1)+zeta'(s)/zeta(s)` is exactly

```text
integral_[1,infinity) f_(n,s)(x) d(x-psi(x)).          (4)
```

No estimate and no separation of divergent boundary pieces occurs in `(4)`.

### Proof `[PROVED HERE]`

For `(2)`, substitute `x=exp(t)`:

```text
integral_1^infinity x^(-s)B_n(w log x) dx
  = integral_0^infinity exp(-a t)B_n(wt) dt
  = sum_(j=0)^n b_(n,j)w^j integral_0^infinity
      exp(-a t)t^j dt
  = sum_(j=0)^n b_(n,j)j!w^j/a^(j+1).
```

Equation `(3)` is the defining Stieltjes integral of the step function
`psi`, since its jump at the integer `m` is `Lambda(m)`.  Subtraction proves
`(4)`.  Absolute Euler convergence justifies every finite-polynomial
interchange.

## Full completed jet

Let

```text
C_n(s)=sum_(j=0)^n (-1)^j b_(n,j)w^j
  * d^j/ds^j [1/s-log(pi)/2+(1/2)digamma(s/2)].         (5)
```

The completed squared-Xi source polynomial is therefore

```text
Q_n(w)
  = C_n(s)
    + integral_[1,infinity) f_(n,s)(x) d(x-psi(x)).    (6)
```

Equation `(6)` is the exact source object whose strict negativity would
disprove RH.  The first term is the trivial-zero/archimedean correction; the
second is one smoothed prime-counting discrepancy.

## Exact modal scale and concentration

Normalize the positive polar density in logarithmic coordinates:

```text
d nu_(n,s)(t)
  = exp(-a t)B_n(wt)dt
    / integral_0^infinity exp(-a u)B_n(wu)du.           (7)
```

Expanding `B_n`, this is a finite mixture of Gamma laws with shape `j+1`
and rate `a`.  The unnormalized mixture weights are

```text
c_(n,j)=b_(n,j)j!(w/a)^j,                               (8)
```

and their adjacent ratio is exactly

```text
c_(n,j+1)/c_(n,j)
  = 2(n-j)w/((2n-j)a).                                  (9)
```

Since `w=a+1/2` and `s=w+1/2`, ratio `(9)` is greater than one exactly when

```text
j < n/s.                                                (10)
```

Thus the Gamma-mixture index is unimodal at the integer(s) adjacent to
`n/s`.

More strongly, if `T_n` has law `nu_(n,s)`, then

```text
T_n/n -> 1/(s(s-1))                                    (11)
```

in probability as `n->infinity` with `s` fixed.

To prove `(11)`, use `(9)`: outside any fixed relative neighborhood of
`j=n/s`, the adjacent ratios are uniformly separated from one, so products
of the ratios make both mixture tails exponentially smaller than the modal
weight.  Hence `J_n/n->1/s` for the random mixture index.  Conditional on
`J_n=j`, the Gamma law has mean `(j+1)/a` and variance `(j+1)/a^2`.
Chebyshev's inequality, uniformly for `0<=j<=n`, then gives
`T_n/n-J_n/(an)->0` in probability.  Since `a=s-1`, `(11)` follows.

In the original prime variable, the polar cancellation window is therefore

```text
x = exp(n/(s(s-1)) + o(n)).                             (12)
```

## RH-false route consequence

The fixed-frequency theorem showed that no finite Euler prefix controls the
growing-order limit.  Equation `(12)` identifies where the mass goes.  A
growing-order disproof must prove a signed asymptotic for the completed
Chebyshev discrepancy `(6)` on this exponential window.  Pointwise prime
bounds, least-prime dominance, and estimates that separate the zeta pole
from the prime sum cannot decide it.

`[OPEN CORE]` Derive a one-sided asymptotic for `(6)` that retains the
archimedean correction and is strict in the negative direction for some
order/base-point sequence.  An asymptotic for the Lebesgue model alone merely
reconstructs the cancelled pole.

## Gates

- [x] exact common-kernel pole--prime identity
- [x] exact Chebyshev--Stieltjes discrepancy
- [x] full completed radial source formula
- [x] exact mixture ratio and modal index
- [x] logarithmic-window concentration
- [ ] completed signed asymptotic on the window `(12)`
- [ ] strict negative source witness
- [ ] Lean formalization only after the signed asymptotic is proved

