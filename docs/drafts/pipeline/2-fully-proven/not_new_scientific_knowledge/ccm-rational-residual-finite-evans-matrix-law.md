# The reconstructed CCM rational residual has an exact finite Evans matrix

> **2026-07-22 domain correction.** This finite Evans matrix detects only raw
> `ker(G_a:L2_0->L2_0)`. Any statement below promoting its injectivity to RH requires the
> completion-corona regularity lift in `suzuki-completed-zero-mode-corona-seam-law.md`.

- **ID:** `ccm-rational-residual-finite-evans-matrix-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** one-dimensional Bessel-potential kernels and
  `ccm-log-symbol-dirichlet-exterior-reconstruction-law.md`

## Statement

Fix an aperture with nonempty real characteristic set. Let

```text
p_a(xi)=product_(tau in Z_a)(xi-tau)^(nu_tau),
d_a=degree p_a=2L_a,
b_a(xi)=p_a(xi)/(1+xi^2)^(L_a).                           (1)
```

Let `F_a` be the `d_a`-dimensional space of solutions of

```text
p_a(D)f=0 on I=(-a,a).                                    (2)
```

For `f in F_a`, let the logarithmic Dirichlet theorem reconstruct

```text
u_f=C_(a,I)^(-1)f,
v(f)=c_a(D)u_f=f+v_E(f),
supp u_f subset [-a,a].                                   (3)
```

Define the residual

```text
rho_a(f)=1_I b_a(D)v(f).                                  (4)
```

Then

```text
rho_a(f) in R_(L_a)
 :=span_C{x^j exp(x),x^j exp(-x):0<=j<L_a}.               (5)
```

Thus the exact rational-factor residual has dimension at most `2L_a=d_a`, despite depending on
the infinite-dimensional exterior reconstruction.

Choose bases of `F_a` and `R_(L_a)`, and append the mean-zero and two affine-anchor functionals.
This gives a source-defined linear map

```text
M_a:F_a -> R_(L_a) direct_sum C^3.                        (6)
```

Let `Gram_a=M_a^*M_a` in any positive Hermitian coordinates on the target. Then

```text
M_a is injective
 iff Gram_a is positive definite
 iff det Gram_a>0.                                        (7)
```

Consequently, after the logarithmic regularity gate needed to place every screw null vector in the
factorized category,

```text
ker G_a={0} iff det Gram_a>0.                             (8)
```

The determinant has size `d_a`, but its entries contain the exact logarithmic Dirichlet inverse and
therefore retain the infinite Gamma boundary state.

`[PROVED SUBSEQUENT CLOSURE]` Every original screw null vector has the required global logarithmic
transformed trace, so the qualification before `(8)` has been discharged. The unconditional
equivalence, including the empty-characteristic branch, is proved in
`ccm-screw-null-global-log-regularity-law.md`.

## 1. Rational kernel

The inverse Fourier transform of `(1+xi^2)^(-L)` is the one-dimensional Bessel kernel

```text
k_L(t)=exp(-|t|)P_(L-1)(|t|),                             (9)
```

up to a nonzero constant, where `P_(L-1)` is a polynomial of degree `L-1`. This follows either by
residue calculus or by convolving the kernel `exp(-|t|)/2` of `(1+D^2)^(-1)` exactly `L` times.

Away from `t=0`, every derivative of `k_L` remains of the form

```text
exp(-|t|)Q(|t|),       degree Q<=L-1.                    (10)
```

The distribution kernel of `b_a(D)` is `p_a(D)k_L`. It may also contain a diagonal delta term
because `b_a(xi)->1`, but that term vanishes in every cross-boundary block.

## 2. Exterior contribution

For `x in I` and `y>a`, one has `|x-y|=y-x`. Equations `(9)`--`(10)` give

```text
(1_I b_a(D)1_(a,infinity)v_E)(x)
 =sum_(j=0)^(L_a-1) alpha_j(v_E)x^j exp(x).              (11)
```

The coefficients are exponentially weighted moments of the right exterior datum. Reflection gives

```text
(1_I b_a(D)1_(-infinity,-a)v_E)(x)
 =sum_(j=0)^(L_a-1) beta_j(v_E)x^j exp(-x).              (12)
```

The exponential decay makes these moments continuous on exterior `L2`. Hence the exterior
contribution lies in `R_(L_a)`.

## 3. Interior characteristic contribution

Extend `f in F_a` by zero outside `I`. Since `p_a(D)f=0` in the open interval and the extension
vanishes in the exterior, the distribution

```text
p_a(D)(1_I f)                                             (13)
```

is supported at the two endpoints `{-a,a}` and is a finite linear combination of delta derivatives
there. Using

```text
b_a(D)(1_I f)
 =(1+D^2)^(-L_a)p_a(D)(1_I f),                           (14)
```

and applying `(9)`--`(10)` to those endpoint distributions shows that its restriction to `I` also
lies in `R_(L_a)`. Adding the exterior contribution proves `(5)`.

## 4. Finite determinant

The Dirichlet reconstruction and the residual map are linear. The mean functional and the two
screw anchors are linear as well. Hence `(6)` is a linear map from a finite-dimensional space.
For any positive Hermitian structure on its target,

```text
<f,Gram_a f>=||M_a f||^2.                                (15)
```

This proves `(7)`. The characteristic reduction, exact exterior reconstruction, residual equation,
mean-zero condition, and two anchors give `(8)`. `QED`

## Positive CCM carrier law

The infinite-rank boundary theorem and the finite determinant theorem are compatible:

```text
infinite logarithmic Dirichlet reconstruction
  -> finitely many exact exponential boundary moments
  -> finite characteristic Gram determinant.             (16)
```

No fixed finite surrogate may replace the first arrow. The line-211 prime-log transport theorem
forces infinite renormalization rank before the moments are evaluated. Once that exact state is
constructed, rational Bessel propagation proves that only `d_a` residual coordinates reach the
interior characteristic packet.

The remaining RH-bearing theorem is now precise:

```text
det Gram_a>0 for every a>0.                               (17)
```

Its entries are source-defined through `C_(a,I)^(-1)`, the exact polar--Euler--Gamma symbol, and
the screw anchors; they may not be replaced by ordinate-only spectral data or a divisor-blind
finite model.

## Scope and classification

Bessel kernels, endpoint distributions, and finite-dimensional Gram criteria are standard. This
is a route reduction, not new scientific knowledge. The present Lean tree lacks the unbounded
logarithmic Dirichlet operator and Bessel-potential boundary calculus needed for a faithful
formalization, so no wrapper is added.

## Gates

- [x] exact rational Bessel kernel isolated
- [x] exterior cross block proved to have range in `R_(L_a)`
- [x] interior characteristic contribution reduced to endpoint distributions
- [x] complete reconstructed residual proved finite-dimensional
- [x] exact finite Gram determinant criterion constructed
- [x] prove the logarithmic regularity gate for every original screw null vector
- [ ] prove `det Gram_a>0` for every aperture
- [ ] RH
