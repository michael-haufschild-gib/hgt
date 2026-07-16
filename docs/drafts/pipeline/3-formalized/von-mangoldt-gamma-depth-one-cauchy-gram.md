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

## Julia/Stinespring factorization

For any positive scalar source shift `0<=q<=1`, the depth-one displacement has the exact
factorization

```text
1-q=sqrt(1-q^2) sqrt((1-q)/(1+q)).                       (7a)
```

The first factor is the canonical Julia defect of the contraction `q`; the second lies in
`[0,1]`.  Both assertions, and the specialization `q=exp(-lambda)` for every nonnegative real
frequency, are Lean-formalized in `HTGeometry.DepthOneJuliaDefect`.

Thus the depth-one anomaly is not merely a positive Gram chosen after the fact.  It factors through
the canonical finite Stinespring environment of the source shift.  The local Markov cell required
by a conormal-corona dilation is therefore constructed; compatibility and phase-bearing gluing
remain open.

Lean also proves the full finite observation identity

```text
alpha_1=V_1 D_S R_S,                                     (7b)
```

where `V_1` is the actual finite exponential jet observation, `D_S` is the coordinate Julia
defect, and `R_S` is the residual coordinate from `(7a)`.  Thus the factorization is not only a
scalar coefficient identity.

At every depth Lean proves the sharper decomposition

```text
alpha_N=(E_N-I)V_N+V_N D_S R_S.                          (7c)
```

The source-Julia leg is exactly compatible under adjacent Gamma truncation.  Its Bianchi defect is
zero.  Consequently all adjacent-depth anomaly curvature lies in the universal Gamma
clock-displacement leg `(E_N-I)V_N`.  This is a genuine separation: positive Markov geometry is
already assembled along the finite clock, while phase-bearing completion topology can occur only
in the remaining Gamma/first-trace corona channel.

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

## Stieltjes phase no-go

Every raw source frequency in `(6)` is the nonnegative real number `log n`.  Lean therefore proves
the exact pole-location statement

```text
w+log n=0  and  n>=1    implies    Im(w)=0 and Re(w)<=0. (8)
```

Thus the depth-one anomaly cell cannot by itself create the imaginary phase of an off-critical Xi
zero.  This rules out the tempting claim that positivity of `(3)` alone is the missing RH Ward
estimate.

The positive successor is precise: the critical-Mellin/Laurent apartment channel must be the
phase-bearing part of the HT boundary complex, while the depth-one Gamma anomaly supplies its
positive arithmetic amplitude.  The next theorem must construct that channel and prove that the
phase-bearing reduction preserves the calibrated conormal norm.  Merely identifying its final
kernel with `(7)` would restate the target rather than produce it.

## Positive failure statement

If the reduced depth-one Gram does not equal `(7)`, the difference is a concrete general-HT
invariant:

```text
Delta_P=G_H-G_(red,1).                                   (9)
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
- [x] depth-one anomaly factored through the canonical Julia defect and a contraction
- [x] full finite depth-one observation map factored as `V_1 D_S R_S`
- [x] all-depth anomaly split into Gamma-clock and source-Julia legs
- [x] source-Julia leg proved Bianchi-flat under clock truncation
- [x] raw Stieltjes pole locus proved real and nonpositive
- [ ] reduce the shifted-polar and critical-Mellin exact channels
- [ ] identify the reduced metric with the universal Hardy Gram
- [ ] identify the reduced Gamma contact response with `r_P`
- [ ] cofinal limit and RH
