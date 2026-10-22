# Every fixed constrained-prolate contrast section is eventually Weil-positive

- **ID:** `constrained-prolate-fixed-depth-intact-weil-positivity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER PROOF CANDIDATE] [HOSTILE AUDIT OPEN]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `constrained-prolate-weil-toeplitz-schur-law.md`,
  `constrained-prolate-continuous-polar-charge-law.md`,
  `constrained-prolate-fixed-mode-spectral-ladder.md`, and the exact
  polar--prime/radical-quotient decomposition.
- **Statement:** At every fixed contrast depth, the complete prime-coupled Weil numerator,
  normalized by the individual exterior leakages and `log(2*pi*lambda^2)`, converges to the
  coercive Toeplitz matrix `(D_|i-j|)`; hence the fixed section is eventually positive definite.

## Goal

Close the bilinear fixed-depth graph-defect gate `(WT17)` without separating the Poisson center
from its critical-Mellin prime measure. This is a numerator theorem on one explicit prolate tower.
It does not identify the true restricted-Weil ground state, control depth growing with `lambda`,
or prove RH.

## Exact fixed-depth sources

Put

```text
e_(m,lambda)=h_(4m,lambda),
chi_m=chi_(4m)(lambda),
d_m=1-chi_m^2,
ell_m=integral_R e_(m,lambda)=chi_m e_(m,lambda)(0).       (FD1)
```

For `m>=1`, form the exact zero-integral raw contrast

```text
r_(m,lambda)=ell_0 e_(m,lambda)-ell_m e_(0,lambda),       (FD2)
```

and let `g_(k,lambda)` be the normalized `(k+1)`-st Gram--Schmidt output of
`r_1,...,r_(k+1)`. Thus `g_k` is supported on `e_0,...,e_(k+1)` and

```text
integral_R g_(k,lambda)=0.                                 (FD3)
```

The fixed-mode spectral-ladder theorem proves that its coefficient vector converges, up to sign,
to the normalization of

```text
w_k=(-a_0,...,-a_k,S_k/a_(k+1)),
S_k=sum_(m=0)^k a_m^2.                                    (FD4)
```

In particular, all coefficients are bounded at fixed `k`, and the last one converges to a nonzero
constant. If

```text
eta_k=lambda-dependent exterior leakage of g_(k,lambda),
```

then orthogonality of the prolate leakage channels and the Fuchs hierarchy give

```text
eta_k=sum_(m=0)^(k+1)|c_(k,m)|^2 d_m
     ~theta_k d_(k+1),
theta_k=Q_k/Q_(k+1)>0.                                    (FD5)
```

The exact integral cancellation also gives a stronger center estimate than source variation alone.
Indeed, using `(FD1)` and `(FD3)`,

```text
g_k(0)
 =sum_m c_(k,m)e_m(0)(1-chi_m)
 =O(d_(k+1))
 =O(eta_k),                                               (FD6)
```

because `1-chi_m=d_m/(1+chi_m)`, every fixed endpoint value is bounded, and
`d_m<=d_(k+1)` for `m<=k+1` once `lambda` is large.

## Fixed-degree weighted primitive

Write `c=2*pi*lambda^2`. For every fixed degree `n=4m`, let `q_(n,lambda)` be its exterior Fourier
tail and put

```text
U_(n,lambda)(x)=sqrt(lambda*x)q_(n,lambda)(lambda*x).
```

The endpoint/exterior proof of equations `(36)`--`(50)` in the continuous-polar card applies to
every fixed `n`, not only `n=0,4`:

```text
sup_(X>=1)
 |integral_1^X U_(n,lambda)(x)dx/sqrt(x)|
 <=C_n sqrt(d_n)/c.                                      (FD7)
```

The reason is parameter-specific and must not be blurred: Dunster's Bessel order is the angular
spheroidal order, which is zero for every `h_(4m,lambda)` here. The degree `4m` changes only the
fixed constants and phase offset. Hence the endpoint Bessel function remains `J_0`; the exterior
Liouville--Green phase remains nonstationary. The printed additive Bessel-envelope error and the
phase-preserving exterior error have the same fixed-degree bounds used in `(36)`--`(50)`.

Let `R_(k,lambda)` be the complete integer radial sum belonging to `g_(k,lambda)` and set

```text
F_k(t)=exp(t/2)R_k(t),
A_k(T)=integral_0^T F_k(t)dt.
```

Linearity, bounded fixed-depth coefficients, `(FD5)`, `(FD7)`, and the summable `j^(-2)` radial
majorant yield

```text
||A_k||_infinity<=C_k sqrt(eta_k)/c,
||R_k||_2<=C_k sqrt(eta_k).                                (FD8)
```

## Polarized continuous-polar bound

Polarize the abstract primitive identity from the continuous-polar card before taking the
infinite-radial limit. For fixed `i,j`, one orientation is bounded by

```text
||A_i||_infinity ||R_j||_2
 +||A_j||_infinity ||R_i||_2,
```

while the exponentially decreasing orientation is bounded directly by
`||R_i||_2||R_j||_2`. Passing from finite radial sums as in the quadratic proof gives

```text
PPol(R_i,R_j)=O(sqrt(eta_i eta_j)).                         (FD9)
```

This is an intact correlation estimate; it never assigns a standalone boundary value to a radial
summand.

## BV control of the clipped critical-Mellin center

The lower-tail representative is

```text
b_k(t)=R_k(t)-p_k exp(-t/2),
p_k=g_k(0)/(2sqrt(lambda))
   =O(eta_k/sqrt(lambda)).                                  (FD10)
```

For the exact critical-Mellin measure put

```text
J(t)=integral_0^t exp(h/2)dM(h)
    =exp(t)+t-1-Psi(exp(t)),
J_H(t)=J(min(H,t)),
kappa_H(t)=exp(-t)J_H(t).                                   (FD11)
```

Then

```text
kappa_H(t)
 =1+(t-1)exp(-t)-exp(-t)Psi(exp(t)),       0<=t<=H,
 =exp(H-t)kappa_H(H),                       t>H.              (FD12)
```

Chebyshev's elementary bound `Psi(x)<=C*x` and Abel summation imply

```text
Var_[0,infinity)(kappa_H)<=C(H+1).                           (FD13)
```

Here is the complete variation accounting. Between prime-power jumps,
`q(t)=exp(-t)Psi(exp(t))` has derivative `-q(t)`, so its continuous variation on `[0,H]` is at
most `C*H`. Its jumps have total size

```text
sum_(n<=exp(H)) Lambda(n)/n=O(H),
```

which follows from partial summation and `Psi(x)<=C*x`. The elementary term in `(FD12)` has
`O(1)` variation, and the frozen exponential tail has variation `|kappa_H(H)|=O(1)`.

Since `A_j(0)=0`, `A_j` is bounded by `(FD8)`, and `kappa_H(t)->0`, Stieltjes integration by parts
on finite intervals followed by the endpoint limit gives

```text
|integral_0^infinity F_j(t)kappa_H(t)dt|
 <=||A_j||_infinity Var(kappa_H)
 <=C_j sqrt(eta_j)(H+1)/c.                                  (FD14)
```

Finite-cutoff Fubini identifies the critical center term exactly as the left side of `(FD14)`.
At the matching aperture `H=2log(lambda)`, `(FD10)` and `(FD14)` therefore give

```text
|p_i| |integral F_j kappa_H|
 <=C eta_i sqrt(eta_j)(H+1)/(c sqrt(lambda))
 =o(sqrt(eta_i eta_j)).                                     (FD15)
```

The last step uses only `sqrt(eta_i)<=1`, `H=2log(lambda)`, and `c=2*pi*lambda^2`; it is uniform
over each fixed pair. The term with `i,j` reversed obeys the same estimate. The remaining
center--radial and center--center pieces satisfy

```text
p_i M_(R_j)=o(sqrt(eta_i eta_j)),
p_i p_j=o(sqrt(eta_i eta_j))                                (FD16)
```

by `(FD8)`, `(FD10)`, and the fixed-mode Fuchs fact that every `sqrt(eta_k)` beats every power of
`lambda`.

## Bilinear radial-prime and graph-defect theorem

For two fixed single modes `u,v`, write `G_lambda^(u,v)(r,s)` for the cross Gram of radial
components `r,s`, and

```text
a_lambda(k)=sum_(q|k; 2<=q<=lambda^2)Lambda(q)<=log(k).
```

The cross-degree phase estimates needed below are not an automatic polarization of the
same-degree estimates.  Put

```text
s_u=sigma_u(c)^2,  s_v=sigma_v(c)^2,
F_s(r,x)=r*sqrt((r^2*x^2-s)/(r^2*x^2-1)).
```

For fixed `u,v`, `s_u,s_v=O_(u,v)(c^(-1))`.  On `r>=2`, `x>=1`, and
`0<=s<=1/2`, direct differentiation gives

```text
partial_r F_s(r,x)>=c_0,
|partial_s F_s(r,x)|<=C/r.
```

Consequently, for distinct integers `r,s>=2`,

```text
|F_(s_u)(r,x)-F_(s_v)(s,x)|
 >=c_0*|r-s|-C_(u,v)/c
 >=c_1*|r-s|                                                (FD17p)
```

once `c` is large.  Thus the cross-degree difference phase has exactly the same
nonstationary divisor as the same-degree phase; the sum phase has derivative bounded below by
`c_1(r+s)`.

For the low first row the cross-degree difference phase has a unique stationary point.  If
`y=x^2`, its squared stationary equation is

```text
(y-s_u)(k^2*y-1)=k^2*(y-1)(k^2*y-s_v).                       (FD17q)
```

The left side minus the right side is a concave quadratic, is positive at `y=1`, and tends to
`-infinity`; hence it has exactly one root `y_(u,v,k)>1`.  The equation itself gives, uniformly
for `2<=k<=c/(2*pi)`,

```text
y_(u,v,k)-1 asymptotic to k^(-2),
|d^2/dx^2[xi_(s_u)(x)-xi_(s_v)(k*x)]|
  at x=sqrt(y_(u,v,k)) asymptotic to k^3.                    (FD17r)
```

Both Bessel arguments there therefore retain the sizes `c/k` and `c*k`.  The same stationary
phase partition gives the cross bound

```text
|G_lambda^(u,v)(1,k)|
 <=C_(u,v)*sqrt(d_u*d_v)
    [c^(-1/2)*k^(-2)+c^(-1)*k^(-1)].                        (FD17s)
```

For `k>lambda^2`, the high-factor exterior phase has derivative at least `c_0*c*k`.  The
fixed-degree pole factor obeys the weighted BV estimate

```text
Var[U_(u,1)(x)*a_(v,k)(x)/x]
 <=C_(u,v)*sqrt(d_u)*c.
```

After the exterior prefactor `sqrt(d_v)/k` is restored, integration by parts gives

```text
|G_lambda^(u,v)(1,k)|
 <=C_(u,v)*sqrt(d_u*d_v)/k^2.                               (FD17t)
```

On the radial diagonal, Cauchy--Schwarz is now used only after divisor reindexing:

```text
|G_lambda^(u,v)(k,k)|
 <=sqrt(G_lambda^(u,u)(k,k)G_lambda^(v,v)(k,k))
 <=C_(u,v)sqrt(d_u d_v)/k^2.
```

Consequently `sum_k a_lambda(k)|G_lambda^(u,v)(k,k)|` is
`O(sqrt(d_u d_v))`, because `sum_k log(k)/k^2<infinity`. For distinct radial indices, the proofs
of the exact exterior, finite first-row, and high first-row estimates are unchanged when the two
fixed prolate degrees differ: the common fast phase acquires only a fixed degree-dependent offset,
and every amplitude bound is normalized by `sqrt(d_u d_v)`. They give

```text
sum_(r,s>=2;r!=s) a_lambda(s)|G_lambda^(u,v)(r,s)|
 <=C_(u,v)sqrt(d_u d_v)/c,

finite first row
 <=C_(u,v)sqrt(d_u d_v)[c^(-1/2)+log(c)^2/c],

high first row=o(sqrt(d_u d_v)).                              (FD17a)
```

Here the first line follows from `(FD17p)`, the second from `(FD17q)`--`(FD17s)`, and the third
from `(FD17t)`.  These are the bilinear fixed-degree versions of equations `(7)`--`(8a)` in the
full radial-prime charge theorem, now with the cross-degree phase geometry exposed rather than
inferred by formal polarization. Summing the finitely many mode pairs in `g_i,g_j` and using
`(FD5)` proves

```text
QPrime(R_i,R_j)=O(sqrt(eta_i eta_j)).                         (FD17)
```

This is not the operator-norm estimate obtained by counting all available prime shifts. In the
notation of the exact autocorrelation carrier,

```text
Q_(polar-prime,H)(v,w)=2 Re integral_(0,H) C_(v,w)(h)dR(h),
dR(h)=2cosh(h/2)dh
      -sum_(n>=2)Lambda(n)n^(-1/2)delta_(log n)(h).             (FD17b)
```

Thus `(FD9)` is its continuous `2cosh(h/2)dh` part, `(FD17)` is its atomic
von-Mangoldt part, and `(FD15)`--`(FD16)` are exactly the terms created by replacing
`R_i,R_j` with the intact Poisson brackets `b_i,b_j`. Combining them once—not adding a second
copy of the prime form—proves

```text
Q_defect(b_i,b_j)=O(sqrt(eta_i eta_j))
                 =o(log(c)sqrt(eta_i eta_j)).                 (FD18)
```

For clarity, the exact bilinear center expansion behind that last sentence is as follows.  Set

```text
M_j=integral_0^infinity exp(-t/2)R_j(t)dt,
T_j(h)=integral_h^infinity exp(-t/2)R_j(t)dt.
```

For the oriented autocorrelation
`C_(v,w)(h)=integral_0^infinity v(t+h)w(t)dt`,

```text
C_(b_i,b_j)(h)
 =C_(R_i,R_j)(h)
  -p_i*exp(-h/2)M_j-p_j*exp(h/2)T_i(h)
  +p_i*p_j*exp(-h/2).                                      (FD17c)
```

The Hermitian bilinear carrier uses `(FD17c)` together with the reversed orientation
`(i,j)<->(j,i)`.  The `exp(h/2)T_j(h)` terms are exactly the finite-cutoff Fubini/Stieltjes
pairings in `(FD14)`--`(FD15)`.  For the decreasing orientation put

```text
B_H=integral_(0,H] exp(-h/2)dR(h)
   =H+1-exp(-H)-sum_(n<=exp(H))Lambda(n)/n.
```

Chebyshev plus partial summation gives the sufficient elementary bound
`|B_H|<=C(H+1)`.  Hence the remaining terms are bounded by

```text
|p_i*M_j*B_H|
 <=C*eta_i*sqrt(eta_j)*(H+1)/sqrt(lambda),

|p_i*p_j*B_H|
 <=C*eta_i*eta_j*(H+1)/lambda,                              (FD17d)
```

and are `o(sqrt(eta_i*eta_j))` at `H=2log(lambda)`.  This makes the finite-aperture
decomposition independent of any implicit Abel-limit interchange.

This is `(WT17)` at every fixed pair and is stronger by one logarithmic order. All limiting steps
are performed first for a finite radial sum and finite `H`, then passed by the existing `L2` and
summable-majorant theorems. No prime-number-theorem remainder and no separated critical boundary
evaluation is used.

## Fixed-depth intact Toeplitz limit

The leading archimedean/log-chirp theorem, together with the already controlled noncritical
lower-order terms, gives after harmless endpoint orientation

```text
Q_lead(b_i,b_j)
 /(log(c)sqrt(eta_i eta_j))
->D_|i-j|.                                                 (FD19)
```

To see that the source change does not alter the symbol, `(FD4)`--`(FD5)` and the Fuchs hierarchy
give

```text
c_(i,i+1)sqrt(d_(i+1))/sqrt(eta_i)->s_i in {+1,-1},
c_(i,m)sqrt(d_m)/sqrt(eta_i)->0,                 m<=i.        (FD19a)
```

Substituting the finite source changes on both sides of the fixed-mode limit `(WT9)` leaves only
the top-mode pair `(i+1,j+1)`, whose Toeplitz index is
`|(i+1)-(j+1)|=|i-j|`. This proves `(FD19)` rather than assuming it.

Here `Q_lead` does not contain another copy of the atomic term in `(FD17b)`. Equations `(FD18)`
and `(FD19)` prove the same limit for the complete Weil form. For fixed `N`,
entrywise convergence is operator-norm convergence, so

```text
Diag(eta)^(-1/2) QW_(lambda,N) Diag(eta)^(-1/2)/log(c)
 ->T_N=(D_|i-j|)_(0<=i,j<=N).                               (FD20)
```

The exact Toeplitz theorem gives `T_N>=(1/2)I`. Therefore for every fixed `N`, once `lambda` is
large enough,

```text
QW_(lambda,N)>=(1/4)log(c) Diag(eta_0,...,eta_N)>0.          (FD21)
```

The radical quotient identifies this matrix with the complete Weil numerator on the original
aperture-restricted sources. Thus every fixed contrast section is eventually strictly
Weil-positive.

The only legitimate localization corollary is internal to this tower:

```text
if a sequence of these prolate contrast sections has a negative eigenvalue
at cofinal apertures, then its depth is unbounded.             (FD22)
```

It is not proved that false RH supplies such a sequence, nor that these sections capture the true
restricted-Weil ground state.

## Hostile audit

1. **Not the Connes ground-state theorem.** Positive numerator matrices do not compare the CCM seed
   or its fixed companions with the true lowest Weil eigenvector. The aperture metric and
   reduced-resolvent incidence remain open.
2. **No cofinal-depth interchange.** Constants in `(FD7)`--`(FD18)` depend on `i,j,N`. Nothing here
   survives `N=N(lambda)->infinity`.
3. **No global witness localization.** `(FD22)` is about negative eigenvalues inside this explicit
   tower only. It is not a consequence about arbitrary Weil-negative tests.
4. **Prime cross term is structural.** Replacing `(FD17)` by the operator-norm bound for all prime
   shifts loses a factor of order `lambda`; the actual radial divisibility theorem is essential.
5. **Critical center is inseparable.** The BV weight controls the clipped prime and continuous
   parts together. Splitting either boundary evaluation revives the invalid graph-domain step.

## Novelty gate

### Internal residue

The regular Toeplitz limit `(FD19)` and its `1/2` floor already occur in
`constrained-prolate-weil-toeplitz-schur-law.md`. The two-mode quadratic primitive and center
estimate already occur in `constrained-prolate-continuous-polar-charge-law.md`. Candidate-new
content is precisely:

1. the all-fixed-degree primitive transfer `(FD7)`--`(FD8)`;
2. the bounded-variation clipped-weight argument `(FD11)`--`(FD15)`, which preserves the geometric
   mean across exponentially separated contrast levels;
3. bilinear closure `(FD18)` of `WT17`; and
4. complete fixed-section positivity `(FD21)`.

No equivalent result was located in the internal corpus.

### External collision audit through 2026-07-27

- Dunster's uniform PSWF asymptotics supply the Bessel and exterior components of `(FD7)`, but no
  prime-coupled Weil-form theorem.
- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*
  (arXiv:2006.13771), use Hermitian Toeplitz matrices for a local archimedean theorem with support
  in `(1/2,2)`. Their result has no growing prime aperture and is not `(FD18)`--`(FD21)`.
- Connes--Consani--Moscovici, *Zeta Spectral Triples* (arXiv:2511.22755), construct the full
  finite-prime Weil matrices but explicitly leave prolate-to-true-ground-state comparison and
  limiting convergence open.
- Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form* (arXiv:2607.02828), proves exact finite Galerkin and archimedean-tail results,
  not a fixed-prolate asymptotic or the clipped critical-Mellin estimate.

No statement matching `(FD18)` or `(FD21)` was found. This is evidence against immediate
rediscovery, not a priority certificate.

## Lean decision

Do not formalize an abstract “if every analytic estimate then positivity” wrapper. Existing Lean
already contains the concrete Toeplitz floor and fixed Hermite contrast algebra. Exact
formalization must next supply, unconditionally:

1. the concrete fixed-degree PSWF primitive `(FD7)`;
2. the actual radial/divisibility bilinear estimate `(FD17)`;
3. the explicit von-Mangoldt clipped-weight BV theorem `(FD13)` and Stieltjes pairing `(FD14)`;
4. the exact radical-quotient/Weil assembly `(FD18)`--`(FD21)`.

Until these are present, the theorem is paper-only and remains in Stage 1.

## Gates

- [x] 0 → 1: well-posed, source-pure, attack identified
- [x] exact fixed-depth source and leakage normalization
- [x] dependency-closed candidate proof of the all-degree primitive transfer
- [x] dependency-closed candidate proof of the clipped-weight center bound
- [x] candidate assembly of the bilinear graph defect and Toeplitz limit
- [ ] independent hostile audit of `(FD7)`, `(FD17)`, and exact defect decomposition
- [ ] external novelty/priority audit beyond targeted primary-source search
- [ ] 1 → 2: hostile audit accepted with no open dependency
- [ ] 2 → 3: complete unconditional Lean formalization
- [ ] true ground-state/reduced-resolvent incidence theorem
- [ ] cofinal-in-depth Weil floor

## Log

- 2026-07-27 — Created after closing the two-mode continuous-polar primitive and rejecting
  diagonal, moment-cluster, and fixed-width Calkin routes. Isolated the BV clipped-weight estimate
  that preserves geometric-mean scaling in the fixed-depth bilinear center term.
