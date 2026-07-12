# The completed local-ratio product carries a cofinal second-order covariance charge

- **ID:** `ccm-local-ratio-second-order-covariance-charge`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** the local-ratio multipliers and quantized differential of Connes--Consani,
  elementary finite-product differentiation, and Euler's reciprocal-prime divergence
- **Statement:** The canonical finite completed local-ratio multiplier differs from the sum of its
  one-place increments by a factorization-independent covariance anomaly. The anomaly has vanishing
  constant and linear diagonal jets, while its quadratic central jet is strictly negative and has
  cofinally divergent magnitude. Thus the additive local Weil trace and the multiplicative
  prime--Gamma covariance occupy different grades of one source object. Every successful CCM
  positivity construction must retain the quadratic grade in a relative/Schur carrier rather than
  discard it when taking the linear trace.

## 1. Critical-line local ratios

For a prime `p`, put `r_p=p^(-1/2)`, `L_p=log p`, and restrict the local ratio

```text
rho_p(s)=(1-p^(s-1))/(1-p^(-s))
```

to the critical line:

```text
u_p(t)=rho_p(1/2+it)
      =(1-r_p exp(iL_pt))/(1-r_p exp(-iL_pt)).              (1)
```

Then `|u_p(t)|=1`, `u_p(0)=1`, and direct differentiation gives

```text
u_p'(0)=-i b_p,
b_p=2 log(p)/(sqrt(p)-1)>0.                                 (2)
```

For the archimedean ratio

```text
rho_infinity(s)=gamma_infinity(s)/gamma_infinity(1-s),
gamma_infinity(s)=pi^(-s/2)Gamma(s/2),                       (3)
```

the critical restriction satisfies

```text
u_infinity(0)=1,
u_infinity'(0)=-i b_infinity,
b_infinity=log(pi)-psi(1/4)>0.                              (4)
```

The positivity in `(4)` follows, for example, from the classical value
`psi(1/4)=-gamma-pi/2-3log 2`.

## 2. Canonical covariance anomaly

For a finite prime set `F`, let

```text
u_F(t)=u_infinity(t) product_(p in F)u_p(t).                 (5)
```

Define the completed multiplicative covariance anomaly

```text
C_F(t)
 =u_F(t)-1-(u_infinity(t)-1)-sum_(p in F)(u_p(t)-1).         (6)
```

More generally, if the places are indexed by `V={infinity} union F`, the elementary subset
expansion gives

```text
C_F(t)=sum_(I subset V, |I|>=2) product_(v in I)(u_v(t)-1).  (7)
```

Thus `(6)` is independent of any Gauss splitting or pairing of archimedean components with primes.
It is the complete higher-than-linear part of the canonical local-ratio product.

Every factor in `(7)` vanishes at `t=0`, so

```text
C_F(0)=0,
C_F'(0)=0.                                                   (8)
```

Differentiating `(7)` twice leaves only the two-element subsets. Equations `(2)` and `(4)` give

```text
C_F''(0)
 =2 sum_(v<w)u_v'(0)u_w'(0)
 =-2 sum_(v<w)b_vb_w<0                                     (9)
```

whenever at least two places are present. Therefore the covariance anomaly has exact order two at
the central seam.

The prime-only part

```text
C_F^fin(t)
 =product_(p in F)u_p(t)-1-sum_(p in F)(u_p(t)-1)            (10)
```

has the exact curvature

```text
-(C_F^fin)''(0)
 =8 sum_({p,q} subset F)
    log(p)log(q)/((sqrt(p)-1)(sqrt(q)-1)).                   (11)
```

Every summand is strictly positive.

## 3. Cofinal divergence

For `x>1`, the elementary inequality `log x>=1-1/x` gives

```text
b_p
 =2log(p)/(sqrt(p)-1)
 >=2(p-1)/(p(sqrt(p)-1))
 =2(sqrt(p)+1)/p
 >=2/p.                                                      (12)
```

Hence

```text
-(C_F^fin)''(0)>=8 sum_({p,q} subset F)1/(pq).               (13)
```

Along a cofinal exhaustion of the primes,

```text
sum_(p<q, p,q in F)1/(pq)
 =1/2 ((sum_(p in F)1/p)^2-sum_(p in F)1/p^2)
 ->infinity,                                                 (14)
```

because `sum_p 1/p` diverges while `sum_p 1/p^2` converges. Thus the canonical second-order
covariance charge cannot remain bounded in the cofinal finite-place limit.

## 4. Quantized-differential kernel meaning

For critical-line boundary points `x,y`, set

```text
r_v(x,y)=conj(u_v(x))u_v(y).                                 (15)
```

The off-diagonal kernel multiplier in

```text
U_F^*[F_H,U_F]
```

is proportional to

```text
product_v r_v(x,y)-1.                                       (16)
```

The sum of the one-place quantized differentials has multiplier

```text
sum_v(r_v(x,y)-1).                                          (17)
```

Their exact difference is therefore

```text
kappa_F(x,y)
 =sum_(I subset V, |I|>=2)product_(v in I)(r_v(x,y)-1).      (18)
```

Each factor `r_v(x,y)-1` vanishes on the diagonal. Hence `kappa_F` has at least quadratic diagonal
vanishing. Multiplication by the Cauchy/Hilbert kernel, whose local singularity is first order,
leaves a kernel vanishing on the diagonal. This is the local analytic reason that the covariance
anomaly has zero ordinary diagonal trace while the first-order local terms yield the additive Weil
functional.

No global trace-class claim follows from local diagonal cancellation alone. The behavior at
infinity, prime cutoff, and Hardy/Sonin compression remains load-bearing.

## 5. Positive carrier law

The finite source therefore has an exact two-grade constraint:

```text
degree one:
  sum_v(r_v-1)
  -> additive local Weil trace;

degree at least two:
  kappa_F
  -> multiplicative prime--Gamma covariance with divergent central curvature. (19)
```

The second grade is not an arbitrary correction and cannot be consistently set to zero: `(9)`--
`(14)` fix a nonzero, cofinally growing source charge. Conversely it is trace-invisible at degree
one, so the scalar local trace cannot reconstruct it.

Every successful CCM construction must consequently carry `(19)` in a pointed relative object:

1. a Gauss-paired Hardy representative of the canonical covariance class;
2. a principal-relative or Schur block in which the signed covariance is retained before the final
   positive square;
3. a cofinal smoothing/renormalization controlling its divergent curvature; and
4. an index-faithful map from that pointed lift to the shifted-Xi Pick/Weil carrier.

The exact next theorem is a **Gauss-descent theorem**: prove that the analytically compact
Gauss-paired representatives descend, modulo trace-zero conjugation coboundaries, to the canonical
kernel `(18)`, and that the Sonin relative grade is a positive Schur lift of this class with a bound
uniform in the prime cutoff.

## 6. Scope and scientific classification

- `[SEARCH]` The local ratios, Hardy quantized differential, Gauss-paired quasi-inner
  factorization, and trace interpretation are Connes--Consani.
- `[PROVED]` The factorization-independent anomaly `(6)`--`(7)`, exact central curvature `(9)`--
  `(11)`, harmonic lower bound `(13)`, and cofinal divergence `(14)` follow as above.
- `[PROVED]` The kernel anomaly has quadratic diagonal vanishing and therefore contributes no local
  first-order diagonal trace.
- `[NOT PROVED]` No uniform global trace-ideal estimate, Sonin positivity, determinant convergence,
  or divisor-index transport is established.
- `[NOT PROVED]` This theorem does not prove RH.

The result is a route-specific assembly of elementary product calculus and standard local-ratio
formulas. It is useful because it identifies the exact canonical covariance carrier, but it does
not introduce a scientifically new parent mechanism. It is classified as a bridge rather than new
scientific knowledge.

## 7. Lean decision

The exact finite-product and second-jet identities are formalizable, but the present Lean tree has
no critical-line local-ratio multiplier or Hardy singular-kernel realization. Formalizing only the
commutative product identity would be a routine wrapper and would not certify the analytic
Gauss-descent or uniform Schur theorem. No Lean file is added for this bridge.
