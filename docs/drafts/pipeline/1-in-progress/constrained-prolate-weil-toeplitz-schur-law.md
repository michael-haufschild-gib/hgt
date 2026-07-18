# The constrained-prolate regular Weil form has a coercive Toeplitz limit

- **ID:** `constrained-prolate-weil-toeplitz-schur-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / REGULAR WEIL--PROLATE TRANSFER PIVOT
- **Scientific status:** `[PROVED FROM ACCEPTED PAPER INPUTS] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** Dunster fixed-mode exterior phase, the constrained-prolate leakage ladder,
  `ccm-countable-log-chirp-renormalization-law.md`, the exact radial off-diagonal bounds, and
  Suzuki's regular archimedean Weil multiplier.
- **Open consumers:** the intact polar--prime critical-Mellin graph defect in
  `constrained-prolate-exterior-weil-leading-law.md` and the source-specific aperture Gram in
  `ccm-weil-exterior-tail-quotient-gate.md`.

## Why this card exists

The direct scalar comparison between the constrained-prolate leakage form and the regular Weil
form is false beyond one mode.  The first surviving replacement is not a diagonal estimate but a
relative congruence law: after normalization by the fixed-mode exterior leakage scales, every
fixed finite pulled-back regular-Weil section converges to one explicit Toeplitz moment matrix.
Its first radial slice is exactly one half of the identity, so the limiting matrix has a uniform
spectral floor.

This is the current RH-facing pivot.  It supplies a canonical Schur correction to the raw CCM seed
and identifies the exact remaining theorem needed to transfer that correction to the full closed
Weil form.

## Fixed-mode radial cross measure

Let `e_(j,lambda)=h_(4j,lambda)` be the positive fixed prolate modes, let

```text
d_j(lambda)=1-chi_(4j)(lambda)^2,
```

and let `R_(j,lambda)` denote the complete integer radial sum of the exterior leakage of
`e_(j,lambda)`.  Dunster's fixed-mode phase has the form

```text
A_lambda(x)-(8j+1)theta(x)/2,
theta(x)=arccos(1/x).                                      (WT1)
```

Therefore the common fast phase cancels in the cross pairing of modes `j` and `ell`, leaving the
exact limiting radial cross density

```text
(1/pi) cos(4(j-ell)theta) dtheta.                          (WT2)
```

After summing the integer radial dilations, define

```text
D_r=(1/pi) sum_(k>=1) 1/k
      integral_(arccos(1/k))^(pi/2) cos(4r theta) dtheta

   =(1/pi) integral_0^(pi/2)
      H_(floor(sec theta)) cos(4r theta) dtheta.            (WT3)
```

The series is absolutely convergent for every fixed `r`.  In particular,

```text
D_0=(1/pi) sum_(k>=1) arcsin(1/k)/k,                        (WT4)

D_1=(1/pi) sum_(k>=2)
      (k^2-2)sqrt(k^2-1)/k^5.                              (WT5)
```

Every term in `(WT5)` is positive, and `0<D_1<D_0`.

## Toeplitz coercivity theorem `[PROVED FROM ACCEPTED PAPER INPUTS]`

For every finite coefficient vector `c=(c_0,...,c_N)`, let

```text
T_N=(D_|i-j|)_(0<=i,j<=N).
```

Then `(WT3)` gives

```text
c* T_N c
 =1/pi integral_0^(pi/2) H_(floor(sec theta))
      |sum_(j=0)^N c_j exp(4ij theta)|^2 dtheta.             (WT6)
```

Since `H_(floor(sec theta))>=1`, Parseval on the interval of one complete `4theta` turn yields

```text
c* T_N c >=(1/2) sum_(j=0)^N |c_j|^2.                       (WT7)
```

Thus every finite section is strictly positive definite with the depth-independent floor

```text
T_N >= (1/2) I.                                             (WT8)
```

The mechanism is exact: the `k=1` radial slice is `(1/2)I`, while every `k>=2` slice is positive
semidefinite.  This is stronger than merely proving that the Toeplitz moment matrix is positive.

## Regular Weil--prolate relative limit `[PROVED FROM ACCEPTED PAPER INPUTS]`

For the oriented fixed modes themselves, polarizing the countable logarithmic-chirp theorem and
using the radial cross law gives

```text
Q_regular(R_i,R_j)
 /(log(c) sqrt(d_i d_j)) -> s_i s_j D_|i-j|,                 (WT9)
```

where `s_j in {+1,-1}` records the harmless endpoint orientation.  Equivalently, after diagonal
orientation conjugacy,

```text
d^(-1/2) Q_regular d^(-1/2)/log(c) -> T_N.                   (WT10)
```

The proof first truncates the radial indices.  On compact exterior intervals the common Dunster
sum phase is nonstationary, while the difference phase tends to `4(i-j)theta`.  Endpoint and
far-tail removal follows by Cauchy--Schwarz from the proved individual tightness estimates.  The
uniform diagonal bound `||H_(j,k)||^2/d_j<=C_j/k^2` dominates the common-radial sum.  The
phase-preserving nuclear, first-row, and high-row estimates kill distinct radial dilations before
the countable sum is taken.  Thus no signed-measure tightness or unjustified interchange is used.

The finite-prime regular channel is one logarithmic order smaller.  Equations `(WT8)` and `(WT10)`
give a uniform positive comparison for every fixed finite pulled-back regular channel.  No
cofinal-in-depth interchange or uniform upper bound is claimed.

## Two-mode Schur correction

Let `g_0` be the normalized `h_0-h_4` zero-integral CCM contrast and `g_1` the next normalized
zero-integral contrast in `span{h_0,h_4,h_8}`, orthogonal to `g_0` in the source metric.  Their
exterior leakage scales obey

```text
eta_0~theta_0 d_1,   theta_0=8/11,
eta_1~theta_1 d_2,   theta_1=176/211.                         (WT11)
```

In the oriented source basis `(g_0,g_1)`, the leading pulled-back regular-Weil block is

```text
log(c) [ theta_0 D_0 d_1,
         s sqrt(theta_0 theta_1) D_1 sqrt(d_1 d_2);
         s sqrt(theta_0 theta_1) D_1 sqrt(d_1 d_2),
         theta_1 D_0 d_2 ].                                  (WT12)
```

Consequently the raw source seed has a nonzero adjacent numerator coupling of geometric-mean
size.  The direct diagonal transfer is false.  Eliminating the adjacent source channel gives the
canonical pulled-back correction

```text
t_lambda
 ~-s sqrt(211/242) (D_1/D_0) sqrt(d_1/d_2)
 =O(lambda^(-4)),                                            (WT13)
```

and the corrected leading Rayleigh coefficient is

```text
theta_0 d_1 log(c) (D_0-D_1^2/D_0).                          (WT14)
```

The Toeplitz floor implies the quantitative survivor

```text
D_0-D_1^2/D_0 > D_0-D_1 >=1/2.                              (WT15)
```

Thus the correction remains small in the source metric while its pulled-back regular-Weil energy
retains a universal positive fraction of the leakage scale.  This does not yet identify the true
restricted-Weil eigenvector: the exterior-tail identity preserves the Weil form, not the ambient
Hilbert norm.

In particular, the lower eigenvalue of the pulled-back two-rung numerator satisfies

```text
lambda_-/(d_1 log(c))
 ->(8/11)(D_0-D_1^2/D_0)>4/11.                              (WT15a)
```

The mixing coefficient is `O(lambda^(-4))` and its quadratic excess relative to the upper rung is
`O(lambda^(-8))`, stronger than the abstract projective-transfer rate inside this source-coordinate
model.

## Exact remaining true-operator cores

Two independent gates remain.

First, the actual CCM aperture vectors are `k_i=R_lambda E(g_i)`.  The true finite-dimensional
operator is the generalized eigenproblem

```text
Q_lambda c=epsilon G^E_lambda c,
G^E_(ij)=<R_lambda E(g_i),R_lambda E(g_j)>.                  (WT16)
```

The exterior map is ambiently unbounded and no aperture-Gram asymptotic is currently proved.
Promoting the source-metric Schur vector to a true restricted-Weil eigenvector or residual requires
a source-specific asymptotic for `G^E_lambda`.

Second, the regular theorem does not split the polar evaluation from the Poisson-resummed source.
To promote it to the full closed Weil numerator, one must prove, for every fixed pair `i,j`,

```text
Q_defect(b_i,b_j)
  =o(log(c) sqrt(eta_i eta_j)),                               (WT17)
```

where `Q_defect` is the intact polar--prime critical-Mellin graph defect.  No channelwise polar
evaluation is permitted.  The quadratic `i=j=0` case of `(WT17)` is exactly the open graph-domain
estimate already isolated in `constrained-prolate-exterior-weil-leading-law.md`; the relative
transfer needs its finite bilinear polarization.

Even both fixed-family gates would not control the orthogonal complement, so they would still not
prove a cofinal Weil floor or RH.

## No-go closure and positive survivor

- **Killed statement:** the normalized regular Weil form is asymptotically diagonal in the
  constrained-prolate basis.
- **Exact obstruction:** equal radial indices of different fixed modes share the same fast Dunster
  phase; their fixed phase difference survives as `cos(4r theta)`.
- **Positive survivor:** the complete cross-mode interaction is an explicit Toeplitz moment form
  with the uniform floor `(WT8)`.
- **Architectural consequence:** first construct the canonical Toeplitz/Schur correction in source
  coordinates; only then attack the aperture metric, intact graph defect, and full complement.

## Gates

- [x] direct diagonal transfer falsified at the first adjacent mode
- [x] exact cross moments `D_r` isolated
- [x] hostile audit of the fixed-mode cross-measure normalization
- [x] polarization and countable-sum interchange for `(WT9)`
- [x] finite-prime cross channel proved one logarithmic order lower
- [x] prove Toeplitz positivity and identify the `1/2` floor mechanism
- [ ] formalize the concrete adjacent coefficient and Schur survivor in Lean
- [ ] externally audit novelty and priority
- [ ] prove the aperture-Gram asymptotic `(WT16)`
- [ ] prove the intact bilinear graph-defect estimate `(WT17)`

## Log

- 2026-07-18 -- Pivoted from the false scalar/diagonal Weil--prolate comparison to the fixed-mode
  radial cross measure.  Isolated the Toeplitz moments `(WT3)`, the nonzero adjacent coefficient
  `(WT5)`, and the Schur correction `(WT13)`.
- 2026-07-18 -- Strengthened strict positivity to the depth-independent floor `(WT8)` by separating
  the exact `k=1` half-identity slice from the positive higher radial slices.
- 2026-07-18 -- Hostile audit closed the fixed-mode cross limit and corrected the operator claim:
  the Schur law is unconditional in the orthonormal source-coordinate metric, while a true aperture
  eigenvector requires the additional Gram gate `(WT16)`.
