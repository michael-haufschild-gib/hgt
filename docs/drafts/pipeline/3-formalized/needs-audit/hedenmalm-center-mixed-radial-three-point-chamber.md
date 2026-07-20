# Hedenmalm center-mixed radial three-point chamber

- **ID:** `hedenmalm-center-mixed-radial-three-point-chamber`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / FINITE-ORDER POSITIVITY FRONTIER
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC PROJECT KNOWLEDGE] [BRIDGE]`
- **Parent:** `../../1-in-progress/hedenmalm-center-mixed-double-positivity-law.md`
- **RH status:** `[NOT AN RH PROOF]`

## Exact source

Let `k=thetaCuspFullSource`, let `0<a<1/2`, and write

```text
M_a(t)=integral_(0,infinity)
  r sinh(a r) k(r/2+t)k(r/2-t) dr.                       (1)
```

The project already proves that `k` is strictly positive and that `log k` is strictly concave on
the whole real line.  It also proves that `M_a` is even, strictly positive, continuous,
integrable, and satisfies `M_a(t)<=M_a(0)`.

## Theorem A: radial monotonicity

For every `u in R`, the reflection product

```text
P_u(t)=k(u+t)k(u-t)                                      (2)
```

is strictly decreasing for `t>=0`.  Consequently `M_a` is nonincreasing on `[0,infinity)`:

```text
0<=s<=t  ==>  M_a(t)<=M_a(s).                            (3)
```

### Proof

Put `L=log k`.  Since `L` is differentiable and strictly concave, `L'` is strictly decreasing.
For fixed `u`,

```text
d/dt [L(u+t)+L(u-t)] = L'(u+t)-L'(u-t)<0                (4)
```

for `t>0`.  Hence the logarithm of `(2)`, and therefore `(2)` itself, is strictly decreasing on
the nonnegative half-line.  The radial weight in `(1)` is nonnegative.  Pointwise comparison of
the two reflection products, followed by the already established exponential domination, gives
the integral comparison `(3)`.

The conclusion is stated non-strictly because that is the exact fact needed below and avoids
using strict-integral machinery.  Pointwise strictness of `(2)` remains available.

## The universal three-point determinant

For real numbers `d,p,q,r`, put

```text
C(d,p,q,r) = [[d,p,r],
              [p,d,q],
              [r,q,d]],                                  (5)

D(d,p,q,r) = d^3+2pqr-d(p^2+q^2+r^2).                   (6)
```

If `d>0` and `0<=p<d`, then

```text
C(d,p,q,r) is positive semidefinite  <=>  D(d,p,q,r)>=0. (7)
```

Indeed, with `A=d^2-p^2>0` and `B=dq-pr`, the quadratic form has the exact `LDL*` decomposition

```text
d x^2+d y^2+d z^2+2pxy+2rxz+2qyz
 = d (x+(p/d)y+(r/d)z)^2
   +(A/d)(y+(B/A)z)^2
   +(D/A)z^2.                                             (8)
```

Thus `D>=0` implies positive semidefiniteness.  Conversely, evaluate the quadratic form at

```text
(x,y,z)=(pB-rA,-dB,dA).                                  (9)
```

Both squares in `(8)` vanish and the value is `d^2 A D`.  Positivity and `d^2 A>0` force
`D>=0`.  This proves `(7)` without a determinant library assumption.

## Theorem B: an unconditional far-separated three-node chamber

Let `x,y>0` and set

```text
d=M_a(0),  p=M_a(x),  q=M_a(y),  r=M_a(x+y).             (10)
```

Then positivity, the strict reflection-product inequality, and `(3)` give

```text
0<d,  0<=p<d,  0<=q<=d,  0<=r<=min(p,q).                (11)
```

Whenever

```text
p^2+q^2<=d^2,                                            (12)
```

the three-node Bochner matrix at the ordered nodes `0,x,x+y` is positive semidefinite.

### Proof of the scalar chamber

For fixed `d,p,q`, write

```text
f(r)=D(d,p,q,r)=d(d^2-p^2-q^2)+2pqr-dr^2.               (13)
```

The first endpoint satisfies `f(0)>=0` by `(12)`.  Suppose first that `p<=q`, so
`0<=r<=p`.  The other endpoint factors as

```text
f(p)=(d-q)(d(d+q)-2p^2)>=0,                              (14)
```

because `p<=q<=d` and

```text
d(d+q)-2p^2 >= d(d+q)-2q^2=(d-q)(d+2q)>=0.              (15)
```

The exact chord identity

```text
p f(r)=(p-r)f(0)+r f(p)+p d r(p-r)                      (16)
```

proves `f(r)>=0` when `p>0`; if `p=0`, then `r=0` and the conclusion is `f(0)>=0`.
The case `q<=p` is symmetric.  Hence `D>=0`, and `(7)` proves the matrix claim.

## Exact remaining order-three wall

The new theorem discharges all ordered three-node packets satisfying `(12)`.  For the remaining
near-center chamber

```text
M_a(x)^2+M_a(y)^2>M_a(0)^2,                              (17)
```

order-three positive definiteness is exactly the source inequality

```text
M_a(0)^3+2 M_a(x)M_a(y)M_a(x+y)
  >= M_a(0)(M_a(x)^2+M_a(y)^2+M_a(x+y)^2).               (18)
```

No theorem here proves `(18)` in the near-center chamber.  No finite-order extrapolation is made.
Full positive definiteness of every node packet remains equivalent to the Hedenmalm Fourier sign
and hence to RH.

## Hostile tests and parent-theory boundary

1. Strict or even uniformly strong log-concavity alone cannot prove order three or Fourier
   positivity.  The failed-route card
   `../../5-failed/positive-even-schwartz-source-does-not-orient-fourier-current.md` gives an
   explicit strongly log-concave positive even Schwartz source with a nonreal Fourier zero.
2. The radial monotonicity argument is a standard calculus consequence of strict log-concavity.
   It is new source-specific project knowledge, not a publication-level general theorem.
3. The `3 x 3` `LDL*` criterion is elementary correlation-matrix algebra and belongs to the
   Schoenberg/Bochner parent theory.  It is classified `[BRIDGE]`.
4. The far-separated chamber is a new unconditional application to the actual theta source in
   this coordinate.  It narrows the order-three wall but does not discharge the near-center
   determinant, all finite orders, the Fourier sign, or RH.
5. Gershon's 2026 revision explicitly stops at `TP_2`; its discussion identifies the
   `TP_2/TP_infinity` gap.  Hedenmalm's 2026 paper identifies the theta boundary-value spectral
   problem but supplies no center-mixed three-node positivity theorem.

Primary comparison points:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494.
- A. Gershon, *On the Log-Concavity of the Riemann Xi Kernel*, v2,
  doi:10.20944/preprints202604.0159.v2.
- D. K. Dimitrov and Y. Xu, *Wronskians of Fourier and Laplace Transforms*,
  arXiv:1606.05011.
- I. J. Schoenberg, *Metric spaces and positive definite functions*, Trans. Amer. Math. Soc. 44
  (1938), 522-536.

## Formalization gates

- [x] dependency-closed paper proof of radial monotonicity
- [x] dependency-closed `3 x 3` `LDL*` equivalence
- [x] dependency-closed far-separated chamber proof
- [x] exact near-center scalar wall stated
- [x] generic correlation algebra formalized in `HilbertMetric`
- [x] source specialization formalized in `RHTower`
- [x] representative axiom audit: all eight capstones use only `propext`, `Classical.choice`, and
      `Quot.sound`
- [x] SOTA ledger and typed frontier connected

## Honest significance score

**58/100.**  The package adds a real unconditional finite-order chamber and localizes the first
open three-node region.  Its analytic and matrix cores are classical, it does not solve the
near-center determinant, and it does not imply RH.
