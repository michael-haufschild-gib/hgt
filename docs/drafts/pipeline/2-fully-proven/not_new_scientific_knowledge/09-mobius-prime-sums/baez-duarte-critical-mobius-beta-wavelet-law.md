# Báez--Duarte coefficients are critical Möbius beta-wavelet values

- **ID:** `baez-duarte-critical-mobius-beta-wavelet-law`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), exact source-value bridge, top-down RH reduction
- **Status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `mobius-half-unit-exponential-moment-rh-law.md`,
  `mobius-schur-centered-boundary-limit-law.md`,
  `mobius-signed-channel-coisometry-incidence-law.md`, the classical sequential
  Báez--Duarte criterion, and `RHTower/SqrtCarrierCertificate.lean`
- **Statement:** Every sequential Báez--Duarte coefficient is exactly one zero-mean beta-wavelet
  coefficient of the critical logarithmic Möbius boundary vector.  The wavelet is centered at
  aperture `one half log(2k+1)`, and its weighted `L2` norm is an explicit beta integral.  Thus an
  `exp(alpha t)L2` Möbius moment gives the sharp scale law
  `c_k=O(k^(-(1+alpha)/2))`.  Letting `alpha` tend to `1/2` recovers exactly the
  RH-critical exponent `3/4`, while the unconditional `alpha=0` theorem gives the classical
  `k^(-1/2)` floor.  More weakly, RH is equivalent to cancellation against just this one canonical
  wavelet at each scale; the full weighted-domain tower is sufficient but not required as a proof
  input.
  In the fixed squarefree Gibbs channel this is equivalently a quantitative angle law: the
  canonical feature has unconditional norm of order `k^(-1/4)`, while RH asks its normalized
  overlap with the coherent signed-Moebius source line to be `O_epsilon(k^(-1/2+epsilon))`.

## 1. Euler-safe finite coefficients

For `k>=0`, define the Báez--Duarte coefficient

```text
c_k=sum_(j=0)^k (-1)^j binom(k,j)/zeta(2j+2).             (1)
```

Every zeta value in `(1)` lies in absolute Euler convergence.  Using

```text
1/zeta(2j+2)=sum_(n>=1) mu(n)n^(-2j-2)
```

and interchanging only a finite binomial sum with an absolutely convergent Dirichlet series gives

```text
c_k=sum_(n>=1) mu(n)n^(-2)(1-n^(-2))^k.                   (2)
```

This is also the binomial finite difference of the square-dilated Möbius carrier formalized in
`SqrtCarrierCertificate.lean`: the values sampled in `(1)` are the exact values
`zeta(2z)^(-1)` at the positive integers `z=j+1`.

## 2. Exact critical-boundary wavelet

Put

```text
m_0(t)=sum_(n<=exp(t)) mu(n)/n,        t>=0.               (3)
```

The critical Möbius boundary theorem proves unconditionally that `m_0` belongs to
`L2(0,infinity)` and tends to zero at infinity.  For `k>=1`, set

```text
w_k(t)=exp(-t)(1-exp(-2t))^k,

K_k(t)=-w_k'(t)
      =exp(-t)(1-exp(-2t))^(k-1)
         (1-(2k+1)exp(-2t)).                              (4)
```

Then

```text
c_k=integral_0^infinity m_0(t)K_k(t)dt.                   (5)
```

### Proof

The Stieltjes measure `d m_0` has a jump `mu(n)/n` at `t=log n`.  Therefore

```text
integral_[0,infinity) w_k(t)d m_0(t)
 =sum_(n>=1) mu(n)/n * n^(-1)(1-n^(-2))^k
 =c_k                                                     (6)
```

by `(2)`.  For `k>=1`, `w_k(0)=0`; also `w_k(t)` tends to zero and `m_0(t)` tends to zero at
infinity.  Stieltjes integration by parts therefore turns `(6)` into `(5)`.  Differentiating
`w_k` gives `(4)`.  `QED`

The kernel has zero mean because it is `-w_k'` with equal zero endpoint values.  It changes sign
exactly once, at

```text
t_k=one half log(2k+1).                                   (7)
```

Thus `(5)` is one signed cancellation measurement of the critical Möbius vector at each
logarithmic aperture, not a norm of the whole weighted tail.

## 2a. Fixed safe-temperature signed-channel form

The same coefficient already lives in one fixed absolutely convergent channel space.  Specialize
the squarefree Gibbs law of `mobius-signed-channel-coisometry-incidence-law.md` to

```text
omega=1/2,       sigma=1+2omega=2,
Z_*=sum_(n>=1)mu(n)^2/n^2=zeta(2)/zeta(4),
P_*(n)=mu(n)^2/(Z_* n^2).                                 (7a)
```

On the support of `P_*`, put

```text
epsilon(n)=mu(n),
X(n)=1-n^(-2),
(M_X f)(n)=X(n)f(n).                                      (7b)
```

Then `P_*` is a probability measure, `epsilon` has norm one, and `M_X` is one fixed positive
self-adjoint strict contraction on each coordinate.  Equation `(2)` becomes the exact matrix
coefficient

```text
c_k=Z_* <epsilon,M_X^k 1>_(L2(P_*)).                      (7c)
```

Equivalently, if `R_*` is the signed coisometry of the parent card and

```text
(Y_k)_n=sqrt(P_*(n))X(n)^k,
```

then

```text
c_k=Z_* R_*Y_k.                                           (7d)
```

Let

```text
Pi_*=R_*^*R_*,       w_*(n)=epsilon(n)sqrt(P_*(n)).       (7e)
```

The coisometry identities already proved in the parent card give

```text
Pi_*Y_k=(c_k/Z_*)w_*,
|c_k|=Z_*||Pi_*Y_k||.                                    (7f)
```

Thus the coefficient is exactly the length of the coherent signed-source component of `Y_k`,
not merely bounded by that component.

This is the fixed-source, constraint form of the route.  No parameter is transported through the
critical strip: all values are defined at the safe exponent `sigma=2`, and the RH datum is the
decay of one signed endpoint correlation as `k` grows.

The unsigned endpoint mass gives only the classical baseline.  Since

```text
sum_(n>=1) n^(-2)(1-n^(-2))^k=O(k^(-1/2)),                (7g)
```

absolute values in `(7c)` yield `c_k=O(k^(-1/2))`.  More precisely,

```text
||Y_k||^2
 =1/Z_* sum_(n>=1) mu(n)^2/n^2 (1-n^(-2))^(2k).          (7h)
```

The elementary squarefree counting law

```text
sum_(n<=x)mu(n)^2=x/zeta(2)+O(sqrt(x))                   (7i)
```

and Stieltjes partial summation imply

```text
||Y_k||^2
 =1/[2Z_*zeta(2)] B(1/2,2k+1)+O(k^(-3/4))
 ~ zeta(4)/zeta(2)^2 * sqrt(pi)/(2sqrt(2k)).              (7j)
```

Indeed, the main integral is

```text
integral_1^infinity x^(-2)(1-x^(-2))^(2k)dx
 =one half B(1/2,2k+1),                                  (7k)
```

and the `O(sqrt(x))` squarefree remainder contributes `O(k^(-3/4))` after the rescaling
`x=sqrt(k)y`.  Consequently `||Y_k||` is asymptotic to a positive constant times `k^(-1/4)`.
Define the normalized coherent-source overlap

```text
angle_k=||Pi_*Y_k||/||Y_k||.                             (7l)
```

Equations `(7f)` and `(7j)` show

```text
|c_k|=Z_*||Y_k|| angle_k,

RH iff for every epsilon>0,
       angle_k=O_epsilon(k^(-1/2+epsilon)).               (7m)
```

The equivalence in `(7m)` uses only the sequential endpoint `(15)` below.  The norm asymptotic is
unconditional and independent of zeta zero locations.  The RH exponent asks the Möbius character to
supply one additional quarter-power of cancellation near the spectral endpoint `X=1`.  Thus the
remaining datum is neither construction of a carrier nor continuation of that carrier; it is a
source-specific signed correlation law inside an already constructed probability space.

## 3. Exact weighted kernel norm

Fix `alpha>=0`.  With the beta function `B`, one has

```text
||exp(-alpha t)K_k(t)||_2^2
 =one half integral_0^1 y^alpha(1-y)^(2k-2)
       (1-(2k+1)y)^2 dy                                  (8)

 =one half [
      B(alpha+1,2k-1)
      -2(2k+1)B(alpha+2,2k-1)
      +(2k+1)^2 B(alpha+3,2k-1)].                         (9)
```

Indeed, substitute `y=exp(-2t)` in the squared norm.  The beta recurrence and the standard gamma
ratio asymptotic give

```text
||exp(-alpha t)K_k(t)||_2^2
 ~ Gamma(alpha+1)(alpha^2+alpha+1)
      /[2(2k)^(alpha+1)].                                 (10)
```

Consequently, whenever

```text
exp(alpha t)m_0(t) belongs to L2(0,infinity),              (11)
```

Cauchy--Schwarz in `(5)` proves

```text
c_k=O_alpha(k^(-(1+alpha)/2)).                             (12)
```

At `alpha=0`, the unconditional critical-boundary `L2` theorem recovers

```text
c_k=O(k^(-1/2)).                                          (13)
```

The missing half-unit of exponential moment contributes exactly the missing quarter-power:

```text
alpha increases from 0 to 1/2
  <-> wavelet exponent increases from 1/2 to 3/4.          (14)
```

## 3a. Exact zero-free-line beta integral

The same value relation has a purely spectral form.  Use the one-sided Fourier transform

```text
hat(f)(tau)=integral_0^infinity f(t)exp(-i tau t)dt.
```

The centered boundary theorem gives

```text
hat(m_0)(tau)=1/[i tau zeta(1+i tau)]                     (14a)
```

with the removable value at `tau=0`.  Since `K_k=-w_k'` and `w_k(0)=0`, a beta substitution
gives

```text
hat(K_k)(tau)
 =-i tau integral_0^infinity
      exp(-(1+i tau)t)(1-exp(-2t))^k dt
 =-i tau/2 B((1+i tau)/2,k+1).                            (14b)
```

Both functions are in `L2`, so Plancherel and `(5)` prove the absolutely convergent Euler-line
identity

```text
c_k=1/(4 pi) integral_R
      B((1-i tau)/2,k+1)/zeta(1+i tau) dtau.              (14c)
```

The apparent `tau^(-1)` singularity in `(14a)` has canceled exactly against the wavelet
derivative.  Thus the complete coefficient is a beta-smoothed value of reciprocal zeta on the
zero-free line `Re s=1`; no continuation value is inserted into its definition.

For integer `k`, the beta factor is the rational Pochhammer kernel

```text
B(a,k+1)=k!/[a(a+1)...(a+k)].                             (14d)
```

It has no nontrivial zeros capable of canceling a pole of `1/zeta`.  Formally moving the contour
from `tau in R` to `tau+i alpha`, `0<alpha<1/2`, replaces the reciprocal-zeta line by

```text
Re(1+i(tau+i alpha))=1-alpha                              (14e)
```

and changes the beta scale from `k^(-1/2)` to
`k^(-(1+alpha)/2)`.  Any crossed pole is exactly a zeta zero with real part greater than
`1-alpha`.  Hence the time-domain exponential weight, the quarter-power gain, and the
reciprocal-zeta contour displacement are three exact coordinates of the same seam:

```text
exp(alpha t) transport
  = beta contour shift by i alpha
  = coefficient gain k^(-alpha/2)
  = possible crossing of zeros in Re s>1-alpha.           (14f)
```

Equation `(14c)` leaves open a genuinely real-variable alternative: prove its oscillatory
cancellation on the original zero-free line without first justifying the meromorphic contour
shift.  By the endpoint below, such a proof would itself force the crossed divisor to be empty.

## 4. Top-down chain to RH

Báez--Duarte's sequential Riesz theorem states

```text
RH
 iff for every epsilon>0,
     c_k=O_epsilon(k^(-3/4+epsilon)).                      (15)
```

Combining `(5)` and `(15)` gives the source-only wavelet criterion

```text
RH
 iff for every epsilon>0,
     integral_0^infinity m_0(t)K_k(t)dt
       =O_epsilon(k^(-3/4+epsilon)).                       (16)
```

No Xi zero, limiting divisor measure, real-rooted approximant, anti-Herglotz sign, or Weil form
occurs in `(16)`.  It uses one explicit Möbius step function and one explicit elementary kernel.

The existing half-unit moment tower is a sufficient provider for `(16)`.  Given
`0<epsilon<1/4`, take `alpha=1/2-2epsilon` in `(12)`; this gives exactly
`k^(-3/4+epsilon)`.  For larger `epsilon`, the unconditional bound `(13)` is already stronger.
Hence

```text
exp(alpha t)m_0 in L2 for every alpha<1/2
  -> critical beta-wavelet cancellation (16)
  -> RH.                                                   (17)
```

The first premise in `(17)` is itself classically equivalent to RH, so `(17)` is not a proof.
The useful change is that the middle target is strictly less data than the full weighted-domain
tower: it asks for one signed wavelet coefficient at each scale, and allows cancellation between
the two sides of the sign change `(7)`.

Combining `(7c)` with the same endpoint also gives the entirely static chain

```text
<epsilon,M_X^k 1>=O_epsilon(k^(-3/4+epsilon))
  in the one fixed safe Gibbs space L2(P_*)
  -> sequential Báez--Duarte decay
  -> RH.                                                   (17a)
```

After normalizing by the unconditional carrier size `(7j)`, the same chain is

```text
angle_k=O_epsilon(k^(-1/2+epsilon))
  for the fixed signed source projection Pi_*
  -> sequential Báez--Duarte decay
  -> RH.                                                   (17b)
```

This discharges the abstract projection/angle construction at the fixed safe exponent.  What
remains open is its arithmetic decay, not the Hilbert-space incidence object.

## 5. Relation to the current formal corpus

The Lean tree already supplies the arithmetic side of `(1)`:

```text
MFreeLadder.lean
  -> the real Möbius coefficient sequence;

SqrtCarrierCertificate.lean
  -> zeta(2z)^(-1) as the square-dilated Möbius L-series;
  -> exact finite square-dilation;
  -> effective finite-cutoff approximation on Re z>1/2.
```

The paper pipeline supplies the analytic side:

```text
mobius-schur-centered-boundary-limit-law.md
  -> m_0 in L2 and its reciprocal-zeta Laplace value;

mobius-half-unit-exponential-moment-rh-law.md
  -> the complete weighted-domain tower and its half-unit seam.

mobius-signed-channel-coisometry-incidence-law.md
  -> the fixed squarefree Gibbs probability, signed source coisometry, and orthogonal projection.
```

What is not yet formalized is the bridge itself: the finite binomial transform `(1)--(2)`, the
Stieltjes pairing `(5)`, the beta norm `(8)--(10)`, the zero-free-line integral `(14c)`, and the
imported sequential criterion `(15)`.
Formalizing only the elementary shell before the analytic critical-boundary API exists would not
close a proof dependency, so no Lean file is added under the active no-computation/no-build
boundary.

## 6. Exact remaining research problem

The new independent source target is:

```text
Prove directly from the Möbius/Euler source that the zero-mean beta-wavelet values

  <m_0,K_k>

or, equivalently, the zero-free-line beta integrals

  1/(4 pi) integral_R B((1-i t)/2,k+1)/zeta(1+i t) dt

or the fixed safe-temperature correlations

  Z_* <epsilon,M_X^k 1>_(L2(P_*))

are O_epsilon(k^(-3/4+epsilon)) for every epsilon>0;

equivalently, prove that the normalized coherent-source angles

  ||Pi_*Y_k||/||Y_k||

are O_epsilon(k^(-1/2+epsilon)) for every epsilon>0,
without proving the full exp(alpha t)L2 tower and without using zeta zero locations,
an RH-equivalent Mertens estimate, or the Báez--Duarte explicit zero formula.       (18)
```

Generic `L2` theory stops sharply at `(13)`.  A successful argument must exploit arithmetic
cancellation across the single moving sign seam `(7)`.  This is distinct from the currently owned
theta-current/rectangular-Weil subpower lane: its source is the reciprocal-zeta Möbius boundary,
its scale is `one half log k`, and its terminal observable is a safe-value binomial finite
difference.

## Literature calibration

The coefficient definition `(1)`, the Möbius form `(2)`, the unconditional `k^(-1/2)` estimate,
and the equivalence `(15)` are classical results of L. Báez--Duarte,
[*A sequential Riesz-like criterion for the Riemann hypothesis*](https://doi.org/10.1155/IJMMS.2005.3527).
The Nyman--Beurling dilation background and the arithmetic Möbius approximants are developed in
Báez--Duarte,
[*A strengthening of the Nyman--Beurling criterion for the Riemann Hypothesis*](https://arxiv.org/abs/math/0202141),
and [*A general strong Nyman--Beurling Criterion for the Riemann Hypothesis*](https://arxiv.org/abs/math/0505453).
The beta-wavelet rewrite `(5)` and the exact weighted norm `(8)--(14)` are a project value
relation; no claim of external novelty is needed for its proof role.

## Gates

- [x] exact Euler-safe binomial coefficient identity
- [x] exact critical Möbius Stieltjes-wavelet identity
- [x] unique sign seam and logarithmic aperture identified
- [x] fixed safe-temperature signed-coisometry correlation identity
- [x] exact fixed-source projection identity and unconditional feature-norm asymptotic
- [x] RH-critical decay reformulated as a normalized `k^(-1/2+epsilon)` source-angle theorem
- [x] exact beta-function weighted `L2` norm
- [x] exact reciprocal-zeta Euler-line beta integral and contour-seam interpretation
- [x] half-unit exponential moment converted to the missing quarter exponent
- [x] sequential Báez--Duarte endpoint calibrated against primary literature
- [x] independent source-only cancellation target isolated
- [ ] formalize after the critical Möbius boundary/Stieltjes API enters Lean
- [ ] prove the critical beta-wavelet cancellation `(18)` unconditionally
- [ ] RH
