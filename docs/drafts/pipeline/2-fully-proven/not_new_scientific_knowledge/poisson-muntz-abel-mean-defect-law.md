# The Poisson--Muntz Abel boundary has one exact mean defect

- **ID:** `poisson-muntz-abel-mean-defect-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SOURCE-SAMPLING INFRASTRUCTURE
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** At every symmetric Lebesgue point of an L1 periodization, the one-sided Abel sum
  of the sampled Fourier transform is exactly half the physical lattice value minus the unique
  zero-frequency mean defect.

## Exact theorem

Let `f:R->R` be integrable and even, let `a>0`, and use

```text
Ff(w)=integral_R exp(-2*pi*i*x*w) f(x) dx.
```

Define the scaled periodization and its angular form by

```text
P_(f,a)(x)=sum_(k in Z) f((x+k)/a),
phi_(f,a)(t)=P_(f,a)(t/(2*pi)).                                (1)
```

The periodization is integrable on every unit cell. Suppose zero is a symmetric Lebesgue point of
`phi_(f,a)`. For `0<=r<1` put

```text
A_(f,a)(r)=sum_(n>=1) r^n Ff(a*n).                             (2)
```

Then `(2)` is absolutely convergent and

```text
A_(f,a)(r) -> [P_(f,a)(0)-a*Ff(0)]/(2*a),    r->1-.            (3)
```

In particular, if `integral_R f=0`, then

```text
A_(f,a)(r) -> P_(f,a)(0)/(2*a).                               (4)
```

If the positive lattice values are summable, evenness further gives

```text
P_(f,a)(0)=f(0)+2*sum_(n>=1)f(n/a),                            (5)
```

and hence

```text
sqrt(a) A_(f,a)(r)
 -> f(0)/(2*sqrt(a))
    +1/sqrt(a)*sum_(n>=1)f(n/a).                               (6)
```

For a compactly supported source, the physical sum in `(5)` is finite. Formula `(6)` is the
endpoint-safe Abel form of the one-sided Poisson--Muntz identity.

## Complete proof

Complexify `f`. The L1 periodization theorem and the scaling identity give, for every integer `m`,

```text
integral_(x0,x0+1] exp(-2*pi*i*m*x) P_(f,a)(x) dx
  =a*Ff(a*m),                                                  (7)
```

independently of the unit-cell origin `x0`. The origin-independence follows because both the
periodization and the Fourier character are one-periodic. Taking `x0=-1/2`, substituting
`t=2*pi*x`, and replacing `m` by `-m` gives

```text
(2*pi)^(-1) integral_(-pi)^pi exp(i*m*t) phi_(f,a)(t) dt
  =a*Ff(-a*m).                                                 (8)
```

The Fourier transform of an even function is even. Indeed, applying the Fourier transform's
orthogonal-change-of-variables formula to the reflection `x|->-x` gives

```text
F(f o neg)(w)=Ff(-w),
```

while evenness says `f o neg=f`. Thus the right side of `(8)` is `a*Ff(a*m)`.

For `0<=r<1`, `|Ff(w)|<=||f||_1`; consequently the bilateral series obtained by multiplying `(8)`
by `r^|m|` is absolutely convergent. The exact Poisson-kernel expansion and dominated
sum--integral interchange give

```text
(2*pi)^(-1) integral_(-pi)^pi P_r(t) phi_(f,a)(t) dt
 =sum_(m in Z) r^|m| a*Ff(a*m).                                (9)
```

Splitting the integers into `0`, the positive integers, and their negatives, and using Fourier
evenness, turns `(9)` into

```text
(2*pi)^(-1) integral_(-pi)^pi P_r(t) phi_(f,a)(t) dt
 =a*Ff(0)+2*a*A_(f,a)(r).                                     (10)
```

The Poisson--Fatou boundary theorem at a symmetric Lebesgue point sends the left side of `(10)` to
`phi_(f,a)(0)=P_(f,a)(0)`. Since `a>0`, solving `(10)` for `A_(f,a)(r)` and passing to the limit
proves `(3)`. Also

```text
Ff(0)=integral_R f,
```

so zero mean proves `(4)`.

Finally split the absolutely convergent integer lattice series defining `P_(f,a)(0)` into zero,
positive, and negative indices. Evenness identifies the two nonzero halves, proving `(5)`.
Multiplying `(4)` by `sqrt(a)` and substituting `(5)` proves `(6)`. Compact support makes the
positive physical lattice sequence eventually zero, hence summable. Every interchange above is
therefore justified either by L1 periodization, geometric Abel domination, or a finite physical
sum.

## Route role

The theorem isolates the unique obstruction to the desired one-sided identity: the zero-frequency
mean. The constrained two-mode prolate source is designed to kill precisely this defect. What
remains route-specific is to instantiate the symmetric Lebesgue condition for the zero-extended
source away from endpoint-hit apertures, and then to justify replacement of the Abel limit by the
ordinary Fourier-tail sum using its endpoint oscillation law.

