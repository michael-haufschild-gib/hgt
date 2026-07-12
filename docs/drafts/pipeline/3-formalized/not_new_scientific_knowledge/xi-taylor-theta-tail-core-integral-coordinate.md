# Xi Taylor theta-tail core integral coordinate

- **ID:** `xi-taylor-theta-tail-core-integral-coordinate`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../1-in-progress/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

Define the finite cosine section

```text
C_d(z,x) = sum_(k=0)^d (-1)^k (zx)^(2k)/(2k)!.
```

For the positive one-sided theta tail `T(x)=thetaCuspTailDerivative 0 x`, the finite tail-moment
polynomial has the exact integral evaluation

```text
Q_d(-z^2) = 2 integral_0^infinity T(x)C_d(z,x)dx.          (1)
```

Consequently the reduced theta-tail core from the finite coefficient gate is

```text
U_d(z)
 = 1/2 - (z^2+1/4)
     2 integral_0^infinity T(x)C_d(z,x)dx.                (2)
```

Both identities are finite: no limiting measure, divisor, zero location, or real-rootedness is
used.

## Proof

The coefficient of `w^k` in `Q_d` is

```text
c_k = 2/(2k)! integral_0^infinity x^(2k)T(x)dx.
```

Substitute `w=-z^2`, distribute the finite sum through the integral, and use
`(-z^2)^k=(-1)^kz^(2k)`.  This proves `(1)`.  Substitution into

```text
U_d(z)=1/2-(z^2+1/4)Q_d(-z^2)
```

proves `(2)`.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreIntegral.lean
```

Principal declarations:

```text
truncatedCosineSection
thetaCuspTailEvenCoefficient_eq_complex_integral
thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral
xiCTaylorThetaTailCorePolynomial_eval_eq_integral
```

## Orientation boundary

Equation `(2)` is the smallest direct source coordinate for the remaining core-current theorem.
It does not orient the current: differentiation and polarization produce a mixed two-point kernel,
and positivity of `T` cannot sign that kernel pointwise.  Any successful next theorem must use a
theta-specific correlation constraint rather than only the positive weights in `(1)`.

## Gates

- [x] finite cosine section defined
- [x] coefficient-to-complex-integral identity proved
- [x] finite tail polynomial integral identity proved
- [x] core evaluation identity proved
- [x] formalized in Lean
- [ ] mixed core-current kernel oriented from theta-specific source constraints
