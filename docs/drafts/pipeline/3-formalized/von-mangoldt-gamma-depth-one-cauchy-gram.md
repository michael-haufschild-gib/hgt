# The depth-one von Mangoldt--Gamma descent anomaly has a positive Cauchy Gram

- **ID:** `von-mangoldt-gamma-depth-one-cauchy-gram`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [SOURCE-SPECIFIC FINITE HT BOUNDARY CELL] [RH INFRASTRUCTURE]`
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [NOT RH]`
- **Lean:** `GaloisForLFunctions.RHTower.VonMangoldtGammaDepthOneCauchy`
- **Parents:**
  - `clock-shadow-curvature-bianchi.md`;
  - `../1-in-progress/calibrated-residual-core-green-hodge-rh.md`;
  - `../1-in-progress/ht-capacity-ward-holonomy-rh.md`.

## Finite theorem

Let a finite exponential source have weights `b_p`, frequencies `lambda_p`, and source shift

```text
(Sa)_p=exp(-lambda_p)a_p.
```

At Gamma depth one the Taylor shadow is the identity.  The exact descent anomaly is therefore

```text
alpha_1(a;x)
 =sum_p b_p a_p(1-exp(-lambda_p))exp(-x lambda_p).       (1)
```

Its resolvent/Laplace feature at a right-half-plane packet node `w` is

```text
A_w(p)=b_p(1-exp(-lambda_p))/(w+lambda_p).               (2)
```

For any finite node packet define

```text
G_1(i,j)=sum_p A_(w_i)(p) conj(A_(w_j)(p)).              (3)
```

Then `G_1` is positive semidefinite because it is the literal Gram matrix of the finite source
vectors `(conj(A_w(p)))_p`.  Lean proves `(1)`, the resolvent identity behind `(2)`, the entrywise
formula `(3)`, and positivity.

For the resolved von Mangoldt source, put

```text
b_n=sqrt(Lambda(n)/n),       lambda_n=log n.             (4)
```

Lean proves

```text
b_n^2=Lambda(n)/n,
exp(-lambda_n)=1/n.                                      (5)
```

Consequently the actual feature is

```text
A_w(n)=sqrt(Lambda(n)/n)(1-1/n)/(w+log n),              (6)
```

and every finite natural-number aperture gives a positive source-derived Cauchy Gram with the
unsquared von Mangoldt mass.

## What this changes

The finite positive square root proposed in the Green--Ward route is now an actual source
operator: it is the resolvent of the depth-one Gamma descent anomaly.  It is not manufactured from
the desired Ward matrix and it contains no Xi zero or divisor packet.

This still does not prove the Ward estimate.  The raw Gram `(3)` is a prime Stieltjes Gram, not the
universal Hardy Gram

```text
G_H(i,j)=1/(w_i+conj(w_j)).                              (7)
```

The exact polar and critical-Mellin channels must be reduced together with `(3)`.  A successful
calibrated harmonic reduction must prove that its quotient metric is `(7)`, not the weaker graph
metric `(I+TT*)^(-1)`, and that the Gamma contact response becomes the source current `r_P`.

## Positive failure statement

If the reduced depth-one Gram does not equal `(7)`, the difference is a concrete general-HT
invariant:

```text
Delta_P=G_H-G_(red,1).                                   (8)
```

It measures the metric distortion between an exact source descent anomaly and the universal
Hardy boundary polarization.  Unlike an abstract Ward defect, every finite entry of `(8)` is then
defined from two already constructed source kernels.

## Gates

- [x] exact depth-one Gamma descent anomaly formula
- [x] source resolvent/Cauchy feature constructed
- [x] arbitrary finite feature Gram proved positive semidefinite
- [x] von Mangoldt square-root amplitude proved to retain `Lambda(n)/n`
- [x] actual finite von Mangoldt depth-one Cauchy Gram constructed and formalized
- [ ] reduce the shifted-polar and critical-Mellin exact channels
- [ ] identify the reduced metric with the universal Hardy Gram
- [ ] identify the reduced Gamma contact response with `r_P`
- [ ] cofinal limit and RH

