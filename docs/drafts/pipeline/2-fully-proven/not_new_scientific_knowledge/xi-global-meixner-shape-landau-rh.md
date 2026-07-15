# One global Gamma--Meixner shape trace has a Landau boundary exactly off RH

- **ID:** `xi-global-meixner-shape-landau-rh`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / TOP-DOWN BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parents:** `archimedean-meixner-root-seam-scale.md`,
  `XiHurwitzOrientationEnergy.lean`, and Landau's theorem for general Dirichlet series with
  nonnegative coefficients
- **Statement:** `[PROVED HERE]` The complete Xi divisor and the canonical prime seam define one
  nonnegative general Dirichlet series in the archimedean Gamma convolution-time variable.  RH is
  equivalent to holomorphic continuation of its safely convergent source germ from `Re z>1` to
  `Re z>0`.  Thus a single scalar Gamma-shape value relation can replace separate continuation or
  summability assertions on every zero fibre.

## Canonical divisor coefficient at each prime

Let `Z_Xi` be the support of the Xi divisor.  Retain multiplicity through the positive formalized
weight

```text
b(rho)
 =mult_Xi(rho)/|rho-1/2|^2
 =xiHurwitzOrientationWeight(rho).                       (1)
```

Lean already proves

```text
b(rho)>0,
sum_(rho in Z_Xi)b(rho)<infinity.                        (2)
```

For a rational prime `p`, define the global seam coefficient

```text
A_p=sum_(rho in Z_Xi)b(rho)|C_p(rho)|^2,                 (3)

C_p(rho)=orbitwiseNatPrimeSeamCharge p rho.
```

Every Xi zero lies in the open critical strip.  Hence

```text
|C_p(rho)|
 <=log(p)(p^(-Re rho)+p^(-(1-Re rho)))
 <=2log p.                                               (4)
```

Equations `(2)`--`(4)` show that every `A_p` is finite and

```text
0<=A_p<=4(log p)^2 sum_rho b(rho).                       (5)
```

Moreover, because every `b(rho)` is strictly positive,

```text
A_p=0 for every p
 iff C_p(rho)=0 for every p,rho
 iff RH.                                                 (6)
```

The final equivalence can use any one prime seam zero-locus theorem, but the full family is kept
because its Gamma-shape transform has a positive Dirichlet boundary.

## The one scalar shape trace

Put

```text
lambda_p=(1/2)log(cosh(2log p))>0.                        (7)
```

The sequence `lambda_p` is strictly increasing and tends to infinity.  Define on its convergence
half-plane

```text
G_Xi(z)=sum_p A_p exp(-z lambda_p).                       (8)
```

For real `theta>0`, the exponential is exactly the Gamma--Meixner root diagonal:

```text
exp(-theta lambda_p)
 =(cosh(2log p))^(-theta/2)
 =w_theta(p).                                            (9)
```

By `(5)` and `w_theta(p)<=2^(theta/2)p^(-theta)`, the series `(8)` converges absolutely and locally
uniformly on

```text
Re z>1.                                                  (10)
```

Thus `G_Xi` is a canonical holomorphic source germ there.  Tonelli also gives, for real
`theta>1`,

```text
G_Xi(theta)
 =sum_rho b(rho)
    sum_p w_theta(p)|C_p(rho)|^2.                        (11)
```

No enumeration of zeros or choice of one exceptional fibre enters `(8)`.

## Positive abscissa forced by one off-line zero

Let `alpha` be the abscissa of convergence of `(8)`.  Equation `(10)` gives `alpha<=1`.

Suppose RH fails.  Choose one divisor point `rho_0` with

```text
delta=|2Re(rho_0)-1|>0.                                  (12)
```

The root-seam threshold theorem says

```text
sum_p w_theta(p)|C_p(rho_0)|^2=infinity
  for every 0<theta<=delta.                              (13)
```

Since all terms in `(3)` are nonnegative and `b(rho_0)>0`, equations `(11)`--`(13)` imply

```text
G_Xi(theta)=infinity for every 0<theta<=delta,
alpha>=delta>0.                                          (14)
```

Thus one off-line divisor point forces a positive convergence boundary for the single global
trace.  No cancellation between different zeros or primes can move it leftward.

## Landau continuation theorem

Landau's theorem for a general Dirichlet series

```text
sum_n a_n exp(-lambda_n z),
a_n>=0,
0<=lambda_n increasing to infinity,                      (15)
```

states that a finite abscissa of convergence is a singular point on the real axis unless all
coefficients vanish.  Apply it to `(8)`.

If RH fails, `(14)` gives `0<alpha<=1`, so the holomorphic germ on `Re z>1` cannot continue
holomorphically through `z=alpha`.  Conversely, under RH every seam vanishes, every `A_p=0`, and
`G_Xi=0` is entire.  Therefore

```text
RH
 iff the germ G_Xi on Re z>1 has a holomorphic continuation
      to the complete half-plane Re z>0.                 (16)
```

It is enough to continue along any connected open domain containing `Re z>1` and a neighborhood
of every point of the real interval `(0,1]`.  Meromorphic continuation is insufficient unless the
source theorem also proves absence of poles or other singularities on that interval.

## Top-down chain and source target

The resulting chain is

```text
one completed Euler--Gamma value formula for G_Xi
  which is holomorphic in Gamma shape on Re z>0

  -> the positive general Dirichlet series has no Landau boundary in (0,1]
  -> its abscissa is nonpositive
  -> no Xi divisor fibre has positive horizontal charge
  -> xiHurwitzOrientationEnergy=0
  -> RH.                                                 (17)
```

This is weaker as an input than proving convergence of every fibre energy for every real
`theta>0`: analytic continuation may assign finite values left of the original convergence
boundary.  Positivity is used only once, through Landau, to show that an off-line boundary cannot
be crossed holomorphically.

The open source theorem is precise:

```text
identify the safe trace (8), initially for Re z>1, with a completed
prime--Gamma/theta or relative-resolvent expression that is holomorphic for Re z>0. (18)
```

The expression must preserve the exact coefficients `(3)` or an independently proved equal trace.
Writing down an unrelated holomorphic interpolation of the integer values, or subtracting the
Landau singularity by hand, does not discharge `(18)`.

## Relation to the existing scalar orientation vector

`XiHurwitzOrientationEnergy.lean` already compresses RH to the vanishing of one nonnegative scalar
and realizes it as the negative sector of a canonical Hilbert vector.  The present theorem does not
replace that vector.  It equips the same faithfully weighted Xi divisor with a new analytic
coordinate: the abscissa of the global Gamma-shape trace.

The two scalarizations have complementary jobs:

```text
orientation energy:  zero value <-> RH;
shape trace:          holomorphic crossing of a positive Landau boundary <-> RH. (19)
```

The second form is designed to consume a value relation or Gamma-shape reflection.  If a completed
source identity can continue `(8)`, Landau supplies the missing orientation conclusion without a
separate small-loss estimate on each zero.

## Literature boundary

- The general positive-coefficient singularity theorem belongs to Hardy--Riesz,
  [*The General Theory of Dirichlet's Series*](https://doi.org/10.1038/096312a0).
- A modern account of the classical nonnegative-coefficient Landau theorem and extensions is
  Maurizi, [*Extending Landau's Theorem on Dirichlet Series with Non-Negative
  Coefficients*](https://arxiv.org/abs/1009.0228).
- The Gamma-shape frequencies and their positive convolution-root meaning come from Ramanujan's
  transform as presented in Chakrabarti--Srinivasan,
  [*On a remarkable formula of Ramanujan*](https://arxiv.org/abs/1206.5122).

The mechanism is an assembly of standard positive Dirichlet-series and Gamma Fourier theory with
the formalized Xi divisor weight and seam zero locus.  It is classified as bridge infrastructure,
not new scientific knowledge.

## Gates

- [x] define one finite nonnegative divisor coefficient at every prime
- [x] prove safe holomorphy of the global Gamma-shape trace on `Re z>1`
- [x] prove that any off-line zero forces a positive abscissa
- [x] apply Landau to obtain the one-scalar continuation criterion `(16)`
- [x] separate holomorphic continuation from mere meromorphic interpolation
- [ ] identify `(8)` with a completed source expression holomorphic on `Re z>0`
- [ ] formalize the global coefficients, safe domain, and Landau consumer in Lean
- [ ] RH

