# Xi Taylor theta-tail arbitrary exponential decay

- **ID:** `xi-taylor-theta-tail-arbitrary-exponential-decay`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../1-in-progress/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

Let

```text
T(x) = thetaCuspTailDerivative 0 x
     = sum_(q>=1) exp(x/2) exp(-pi q^2 exp(2x)).
```

For every natural rate `p`, there is an explicit finite constant

```text
C_p = exp((p+1)^2/(2pi))
      sum_(q>=1) exp(-(pi/2)q^2)
```

such that, for `x>=0`,

```text
|T(x)| <= C_p exp(-p x).                                 (1)
```

Consequently, for every positive natural `p`, the factorially normalized even tail moments

```text
c_n = 2/(2n)! integral_0^infinity x^(2n)T(x) dx
```

satisfy

```text
|c_n| <= 2 C_p / p^(2n+1).                               (2)
```

Thus the top coefficient in the finite theta-tail telescope decays geometrically at every
prescribed fixed spatial scale.  More precisely, if `E_d` is the explicit top-defect polynomial,
then on every fixed closed ball

```text
sup_(|z|<=R) |E_d(z)|  -> 0,
sup_(|z|<=R) |E_d'(z)| -> 0.                              (3)
```

## Proof

For the `q`-th theta atom put `y=q exp(x)`.  On `x>=0` and `q>=1`,

```text
exp(px)exp(x/2) <= y^(p+1).
```

Split the Gaussian into two halves.  The first half absorbs the polynomial uniformly by

```text
y^(p+1) exp(-(pi/2)y^2) <= exp((p+1)^2/(2pi)),
```

while the second satisfies

```text
exp(-(pi/2)y^2) <= exp(-(pi/2)q^2).
```

Summing the Gaussian majorant proves `(1)`.  Multiplying by `x^(2n)`, integrating, and using

```text
integral_0^infinity x^k exp(-p x) dx = k!/p^(k+1)
```

proves `(2)` after division by `(2n)!`.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailRapidDecay.lean
```

Principal declarations:

```text
thetaCuspTailNatExpConstant
exp_nat_mul_abs_thetaCuspTailAtom_le
abs_thetaCuspTailDerivative_zero_le_nat_exp_neg
integral_pow_mul_exp_nat_neg
abs_thetaCuspTailEvenCoefficient_le_nat_rate
norm_xiCTaylorThetaTailTopDefectPolynomial_eval
norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval
tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_eval_of_norm_lt_nat
tendsto_norm_xiCTaylorThetaTailTopDefectPolynomial_derivative_eval_of_norm_lt_nat
eventually_norm_xiCTaylorThetaTailTopDefect_lt_on_closedBall
```

The module builds without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## Gates

- [x] arbitrary natural exponential tail bound proved
- [x] exact exponential moment integral proved
- [x] arbitrary geometric normalized-moment bound proved
- [x] all statements formalized in Lean
- [x] top-defect value and derivative decay packaged uniformly on compact sets
- [ ] theta-tail core current proved sublinear on the anisotropic mesh
