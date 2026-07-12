# Xi Taylor theta-tail finite coefficient telescope

- **ID:** `xi-taylor-theta-tail-finite-coefficient-telescope`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../1-in-progress/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

Let

```text
T(x) = thetaCuspTailDerivative 0 x,
Phi(x) = thetaCuspFullSource x = T''(x) - T(x)/4,
```

and define

```text
r_n = 2 integral_(0,infinity) x^(2n) Phi(x) dx,
t_n = 2 integral_(0,infinity) x^(2n) T(x) dx,
b_n = r_n/(2n)!,
c_n = t_n/(2n)!.
```

Then

```text
b_0     = 1/2 - c_0/4,
b_(n+1) = c_n - c_(n+1)/4.                               (1)
```

Consequently, for

```text
B_d(w) = sum_(k=0)^d b_k w^k,
Q_d(w) = sum_(k=0)^d c_k w^k,
```

one has the exact finite identity

```text
B_(d+1)(w)
 = 1/2 + (w-1/4) Q_d(w) - (c_(d+1)/4) w^(d+1).           (2)
```

The canonical Xi Taylor section through order `2d` is

```text
xiCTaylorApprox(2d+1,z) = B_d(-z^2).                     (3)
```

Thus the section through order `2d+2` has the source form

```text
xiCTaylorApprox(2d+3,z)
 = 1/2 - (z^2+1/4) Q_d(-z^2)
   - (c_(d+1)/4)(-z^2)^(d+1).                            (4)
```

Equation `(4)` uses only finitely many moments of the explicit positive one-sided theta tail and
one explicit top-degree defect.

## Proof

Every polynomially weighted derivative of `T` is integrable on `(0,infinity)`.  The exponential
tail estimate also gives

```text
x^k T^(m)(x) -> 0                                        (x -> infinity).
```

For `k >= 2`, two integrations by parts have no boundary contribution and give

```text
integral x^k T''(x) dx
 = k(k-1) integral x^(k-2) T(x) dx.                      (5)
```

At `k=0`, the seam slope is exceptional:

```text
T'(0) = -1/4.
```

Equivalently, the already proved half-line Fourier identity at frequency zero gives

```text
integral Phi = 1/4 - (1/4) integral T.                    (6)
```

Equations `(5)` and `(6)`, together with `Phi=T''-T/4`, yield

```text
r_0 = 1/2 - t_0/4,
r_(n+1) = (2n+2)(2n+1)t_n - t_(n+1)/4.
```

Division by the two factorials proves `(1)`.  Summing `(1)` from `0` through `d+1` proves `(2)` by
a finite index shift.  The even Xi jet identity

```text
XiC^(2n)(0) = (-1)^n r_n
```

and vanishing of all odd central jets prove `(3)`, hence `(4)`.

## Orientation consequence and remaining sign

The identity is orientation-sensitive only after evaluation at `w=-z^2` and insertion into

```text
J_P(z) = Im(P'(z) conjugate(P(z))).
```

It does not make `J_P` sign-definite.  The polynomial `Q_d` has positive coefficients, but that
alone does not orient its values off the real axes, and the top defect is not uniformly negligible
relative to `|P(z)|^2` near a hypothetical Xi zero.  Therefore `(2)` is a genuine finite source
constraint, but it is not the missing sublinear-flux producer.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTelescope.lean
```

Principal declarations:

```text
integrableOn_pow_mul_thetaCuspTailDerivative
integral_pow_mul_thetaCuspTailDerivative_two
thetaCuspRawEvenMoment_zero_eq_tail
thetaCuspRawEvenMoment_succ_eq_tail
thetaCuspRawEvenCoefficient_succ_eq_tail
cauchyPowerSeries_XiC_coeff_two_mul
xiCTaylorEvenMagnitudePolynomial_succ
xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval
```

The three capstones report only the standard mathlib axioms
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.

## Gates

- [x] all polynomially weighted tail derivatives integrable
- [x] boundary terms controlled
- [x] all-order raw moment recurrence proved
- [x] normalized finite coefficient telescope proved
- [x] canonical Cauchy coefficients identified
- [x] actual odd-cutoff Xi Taylor section identified with `B_d(-z^2)`
- [x] Lean file compiles without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] source sign/defect estimate forcing sublinear upper oriented current
