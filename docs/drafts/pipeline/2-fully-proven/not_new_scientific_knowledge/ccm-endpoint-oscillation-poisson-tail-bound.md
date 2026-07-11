# CCM endpoint-oscillation Poisson-tail bound

- **ID:** `ccm-endpoint-oscillation-poisson-tail-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** classical Poisson summation, Fourier series of the sawtooth, and fixed-mode
  prolate concentration asymptotics
- **Statement:** On an even compactly supported smooth source, the CCM arithmetic sum of the
  exterior Fourier tail is controlled by endpoint jets. Its leading `1/y` tail produces the
  uniformly bounded sine series, so the generic coherent-growth obstruction is absent on this
  source class.

## Theorem

Let `f` be even and `C2` on `[-lambda,lambda]`, extend it by zero, and suppose

```text
integral_R f(x)dx=0.                                   (1)
```

Use the Fourier convention

```text
Ff(y)=integral_R f(x)exp(2*pi*i*x*y)dx.
```

For almost every `v>=lambda`, Poisson summation and endpoint Fourier expansion give

```text
E(f)(1/v)
 =sqrt(v) sum_(n>=1) Ff(nv)-f(0)/(2sqrt(v)),           (2)
```

and

```text
|E(f)(1/v)|
 <= (|f(lambda)|+|f(0)|)/(2sqrt(v))
    +( |f'(lambda)|+||f''||_L1(0,lambda) )/(12v^(3/2)). (3)
```

Consequently,

```text
||1_(0,lambda^(-1)) E(f)||_(L2(d*u))
 <= (|f(lambda)|+|f(0)|)/(2sqrt(lambda))
    +( |f'(lambda)|+||f''||_1 )/(12sqrt(3)lambda^(3/2)). (4)
```

The formula is unchanged as an `L2` statement if the exceptional values at which a lattice point
hits an endpoint are assigned either one-sided value.

## Proof

For values of `v` at which the periodization is continuous at the sampling point, Poisson summation
gives

```text
sum_(m in Z) f(m/v)=v sum_(n in Z) Ff(nv).             (5)
```

Both functions are even, and `(1)` says `Ff(0)=0`. Separating the zero terms in `(5)` and dividing
by `2sqrt(v)` proves `(2)`. The usual midpoint convention proves the same identity at the remaining
values, which form a null set for the norm estimate.

Twice integrating by parts on `[0,lambda]`, using `f'(0)=0`, gives for `y!=0`

```text
Ff(y)
 = f(lambda)sin(2*pi*lambda*y)/(pi*y)
   +f'(lambda)cos(2*pi*lambda*y)/(2*pi^2*y^2)
   -1/(2*pi^2*y^2)
      integral_0^lambda f''(x)cos(2*pi*x*y)dx.         (6)
```

Substitute `y=nv` and sum. The leading endpoint jump is not estimated term by term: the exact
sawtooth Fourier series gives

```text
|sum_(n>=1) sin(n*theta)/n|<=pi/2.                    (7)
```

The remaining terms are absolutely summable, and

```text
sum_(n>=1) 1/n^2=pi^2/6.                              (8)
```

Multiplication by `sqrt(v)` in `(2)` now gives `(3)`. Under `u=1/v`, the measure `d*u` is invariant.
Minkowski's inequality and

```text
integral_lambda^infinity v^(-1) d*v=1/lambda,
integral_lambda^infinity v^(-3) d*v=1/(3lambda^3)
```

give `(4)`.

## Deficit-scale central correction for the CCM seed

Let `e_0=h_(0,lambda)`, `e_1=h_(4,lambda)`, with compressed-Fourier eigenvalues `chi_0>chi_1`, and
put

```text
ell_j=integral_R e_j=chi_j e_j(0),
d_j=1-chi_j^2.
```

The normalized zero-integral CCM two-mode source is

```text
g_lambda=(ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2). (9)
```

Direct evaluation at zero gives the exact identity

```text
g_lambda(0)
 =ell_0 ell_1(chi_1-chi_0)
   /(chi_0 chi_1 sqrt(ell_0^2+ell_1^2)).               (10)
```

The fixed-mode asymptotics proved in `constrained-prolate-two-mode-ground-state.md` imply

```text
d_0/d_1->0,
ell_0->2^(1/4),
ell_1->sqrt(3)/2^(5/4),
chi_0-chi_1~d_1/2.
```

Therefore, for the orientation in `(9)`,

```text
g_lambda(0)/d_1
 ->-2^(-3/4)sqrt(3/11).                               (11)
```

Thus the Poisson zero-mode correction in `(2)` is of concentration-deficit order `d_1`, not
square-root-leakage order `sqrt(d_1)`. This is the exact first-order cancellation created by the
zero-integral combination.

## Route consequence

`ccm-poisson-tail-l2-unboundedness.md` proves that the arithmetic tail map is unbounded on the
ambient leakage space because coherent slowly varying logarithmic packets make the Dirichlet sum
grow. Equations `(3)`--`(7)` show that this mechanism is absent for a fixed smooth compact source:
its leading Fourier leakage oscillates as an endpoint sine series and is uniformly summable.

This does not yet prove the CCM comparison. Equation `(4)` replaces the generic operator norm by
the exact source quantities that must now be estimated:

```text
g_lambda(lambda),
g_lambda'(lambda),
||g_lambda''||_1,
```

or higher endpoint jets after further integrations by parts. The central term is already at the
correct deficit scale by `(11)`. What remains is to show that the endpoint-jet remainder enters the
closed Weil residual quadratically, or otherwise below the constrained gap, and then to obtain the
projective rate required for locally uniform determinant convergence.

## Novelty and significance verdict

The bound is assembled from classical Poisson summation, two integrations by parts, and the
sawtooth Fourier series. Identity `(11)` is an algebraic consequence of the fixed-mode theorem and
Fuchs asymptotics. The combination materially sharpens the CCM open core by proving that its
special leakage does not realize the generic coherent-growth obstruction, but the mathematical
ingredients do not clear the dual novelty/significance gate. It is classified as a bridge.

## References

- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.

## Lean decision

The formal tree has no Poisson summation theorem at this regularity, no Mellin realization of the
CCM tail, and no fixed-mode prolate eigenvalue interface. Formalizing only the sawtooth estimate
would be a wrapper. No Lean file is added.

## Gates

- [x] exact positive-half Poisson correction proved
- [x] endpoint-oscillation arithmetic-tail bound proved
- [x] CCM central correction shown to be deficit-scale
- [ ] fixed-mode endpoint-jet asymptotics at the required cofinal strength
- [ ] closed-Weil residual estimate relative to the constrained gap
- [ ] projective determinant transfer to `Xi`
