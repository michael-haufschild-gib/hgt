# Xi Taylor theta-tail positive second-density convex core

- **ID:** `xi-taylor-theta-tail-positive-second-density-convex-core`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../5-failed/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

Let `T(x)=thetaCuspTailDerivative 0 x` be the positive one-sided theta tail and define

```text
rho(x) = 4 T''(x),    x > 0.
```

Then

```text
rho(x) > 0,
integral_0^infinity rho(x) dx = 1.                         (1)
```

The factorially normalized tail coefficients have the shifted positive-moment representation

```text
c_k = (1/2) integral_0^infinity
        rho(x) x^(2k+2)/(2k+2)! dx.                        (2)
```

Define the finite shifted-cosine section and its core atom by

```text
S_d(z,x) = sum_(k=0)^d (-1)^k z^(2k)x^(2k+2)/(2k+2)!,
H_d(z,x) = 1 - (z^2+1/4)S_d(z,x).
```

The remaining finite theta-tail core has the exact convex representation

```text
U_d(z) = (1/2) integral_0^infinity rho(x) H_d(z,x) dx.       (3)
```

All statements are finite-source identities.  They use neither Xi zero locations nor a limiting
measure.

## Proof

The second tail derivative is the positive termwise series associated to

```text
P_2(u) = 4 pi^2 u^4 - 6 pi u^2 + 1/4.
```

For `u >= 1`, `pi > 3` implies `P_2(u)>0`; hence every theta atom, and therefore `T''(x)`, is
strictly positive on `x >= 0`.  The source identity

```text
thetaCuspFullSource = T'' - T/4
```

at zero frequency, together with the already proved source and tail masses, gives

```text
integral_0^infinity T''(x) dx = 1/4,
```

which proves `(1)`.

For `m=2k+2`, two integrations by parts give

```text
integral x^m T''(x) dx = m(m-1) integral x^(m-2)T(x) dx.
```

After the factorial normalization this is exactly `(2)`.  Substitute `(2)` into the finite
polynomial `Q_d(-z^2)`, interchange only a finite sum with the integral, and use
`(-z^2)^k=(-1)^kz^(2k)`.  This gives

```text
Q_d(-z^2) = (1/2) integral rho(x)S_d(z,x)dx.
```

Finally insert this identity and the mass `(1)` into

```text
U_d(z)=1/2-(z^2+1/4)Q_d(-z^2)
```

to obtain `(3)`.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailConvexCore.lean
```

Principal declarations:

```text
thetaCuspTailDerivativePolynomial_two_eval_pos
thetaCuspTailDerivative_two_pos
integral_Ioi_thetaCuspTailDerivative_two
thetaCuspTailSecondDensity_pos
integral_thetaCuspTailSecondDensity
thetaCuspTailEvenCoefficient_eq_second_integral
thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_second_integral
xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral
exists_thetaCuspTailSecondCoreAtom_zero_current_pos
```

## Orientation boundary

Convexity of `(3)` is linear, whereas the oriented current is quadratic.  Polarization introduces
a two-point kernel.  The positive density in `(1)` does not by itself sign that kernel: individual
atoms `H_d(.,x)` need not have favorable upper-half-plane current.  At `d=0`, `x=4`, and
`z=i/4`, the atom current is strictly positive; this counterexample is formalized.  A producer
must therefore use an additional correlation identity specific to the exact theta density, not
probability positivity alone.

## Gates

- [x] strict positivity of the second theta-tail density proved
- [x] probability normalization proved
- [x] shifted coefficient moment identity proved
- [x] finite shifted-section integral identity proved
- [x] finite convex-core identity proved
- [x] pointwise atom-orientation shortcut explicitly refuted
- [x] formalized in Lean
- [ ] exact theta correlation or residual identity orients the mixed current
