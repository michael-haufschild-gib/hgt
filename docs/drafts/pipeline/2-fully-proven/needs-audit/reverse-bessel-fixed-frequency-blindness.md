# Reverse-Bessel radial jets are blind to every fixed Euler frequency

- **ID:** reverse-bessel-fixed-frequency-blindness
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / growing-order route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [NOT FORMALIZED]`
- **Parent:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`
- **Statement:** After normalization by its constant coefficient, the order-`n` reverse-Bessel radial polynomial converges at every fixed nonnegative frequency to the exponential that exactly cancels the Euler damping; hence no finite set of primes can dominate the growing-order squared-Xi source.

## Theorem

Let

```text
b_(n,j) = (2*n-j)!/(2^(n-j)*(n-j)!*j!),
B_n(x)  = sum_(j=0)^n b_(n,j)*x^j.
```

For every `n>=0` and `x>=0`,

```text
B_n(x) = (1/n!) integral_0^infinity
           exp(-u) u^n (x+u/2)^n du.                    (1)
```

Moreover,

```text
0 <= exp(-x) B_n(x)/b_(n,0) <= 1,                       (2)
lim_(n->infinity) exp(-x) B_n(x)/b_(n,0) = 1            (3)
```

for every fixed `x>=0`.

Consequently, at any fixed `w>0` and any fixed integer `m>=2`,

```text
m^(-1/2-w) B_n(w log m)/b_(n,0) -> m^(-1/2).            (4)
```

## Proof `[PROVED HERE]`

Expand the last factor in `(1)` and integrate termwise.  The coefficient of
`x^j` is

```text
(1/n!) * choose(n,j) * 2^(-(n-j))
  * integral_0^infinity exp(-u) u^(2*n-j) du
= (2*n-j)!/(2^(n-j)*(n-j)!*j!)
= b_(n,j).
```

For the normalized coefficients, direct cancellation gives

```text
b_(n,j)/b_(n,0)
  = (1/j!) product_(r=0)^(j-1) 2*(n-r)/(2*n-r).         (5)
```

Every factor in the product lies in `[0,1]`, and for fixed `j` it tends to
one as `n->infinity`.  Therefore

```text
0 <= b_(n,j)/b_(n,0) <= 1/j!,
b_(n,j)/b_(n,0) -> 1/j!.
```

Extend the coefficient sequence by zero for `j>n`.  Dominated convergence
against `x^j/j!` yields

```text
B_n(x)/b_(n,0) -> sum_(j>=0) x^j/j! = exp(x),
```

and the same coefficient bound gives `B_n(x)/b_(n,0)<=exp(x)`.  This proves
`(2)`--`(3)`.  Substituting `x=w log m` in `(3)` and using
`m^(-w)=exp(-x)` gives `(4)`.

## RH-false route consequence

The normalized prime part of the squared-Xi jet is

```text
sum_(m>=2) Lambda(m) m^(-1/2-w)
  B_n(w log m)/b_(n,0).                                 (6)
```

Equation `(4)` shows that each fixed prime-power atom loses its Euler damping
as `n` grows.  The limiting fixed-frequency weights are
`Lambda(m)/sqrt(m)`, whose total mass is not summable.  Thus the limit cannot
be exchanged with the Euler sum: the mass necessarily escapes through a
prime window whose location grows with `n`.

This kills a least-prime or finite-prime growing-order argument.  It does not
kill the growing-order route itself.  A viable proof must obtain a uniform
moving-window comparison with the completed Gamma/polar source before taking
the order limit.

## Gates

- [x] exact positive integral representation
- [x] normalized coefficient domination
- [x] fixed-frequency limit
- [x] finite-prime localization ruled out
- [ ] determine the moving prime-window scale uniformly in `n` and `w`
- [ ] compare that window with the cancellation-preserving completed source
- [ ] formalize only if the moving-window comparison becomes source-bearing

