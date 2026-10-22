# The true constrained-prolate secular eigenvector has negligible logarithmic leakage tail

- **ID:** `constrained-prolate-secular-log-weighted-tail-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / TRUE-EIGENVECTOR GRAPH-TAIL BRIDGE
- **Scientific status:** `[PAPER PROOF CANDIDATE] [HOSTILE AUDIT OPEN]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `constrained-prolate-fixed-mode-spectral-ladder.md`,
  `constrained-prolate-bessel-clock-universality-law.md`, and the classical angular
  prolate Sturm--Liouville form.
- **Statement:** At every fixed constrained spectral rung, the infinite tail of the exact
  constrained leakage eigenvector is negligible not only in source `L2`, but in the stronger
  leakage norm carrying the logarithmic modal weight required by the regular Weil multiplier.

## Why this card exists

The fixed-depth intact Toeplitz theorem is presently proved only for the exact finite
Gram--Schmidt contrasts.  The true constrained leakage eigenvector has coordinates

```text
v_m proportional to ell_m/(d_m-mu_k)
```

and therefore has an infinite prolate tail.  Source-`L2` convergence of that tail is insufficient:
the exterior/Weil graph is unbounded.  The correct intermediate question is whether the tail
remains small after multiplication by both its exterior leakage `d_m` and the logarithmic modal
frequency.

## Setup

Let `e_(m,lambda)=h_(4m,lambda)` be the positive-parity prolate tower,

```text
ell_m(lambda)=integral_R e_(m,lambda),
d_m(lambda)=1-chi_(4m)(lambda)^2,
gamma=2*pi*lambda^2.
```

Let `mu_k(lambda)` be the exact constrained leakage eigenvalue in
`(d_k,d_(k+1))`, and let `v_(k,lambda)` be its unit eigenvector.  Its secular coordinates are

```text
v_(k,lambda,m)
 =N_(k,lambda)^(-1)*ell_m/(d_m-mu_k).                         (LT1)
```

For fixed `k`, the spectral-ladder theorem proves

```text
mu_k/d_(k+1)->theta_k in (0,1),
d_(k+1)/d_(k+2)=O_k(lambda^(-8)),
||d_(k+1)*(ell_m/(d_m-mu_k))_m||_2 -> c_k>0.                 (LT2)
```

## A logarithmic moment law for the constraint coordinates

Rescale `x=lambda*z` and let `y_(n,gamma)` be the orthonormal angular prolate basis on
`[-1,1]`.  Then

```text
ell_m=sqrt(lambda)*inner(1,y_(4m,gamma)).
```

The angular prolate Sturm form is

```text
q_gamma(f)
 =integral_(-1)^1 [(1-z^2)|f'(z)|^2+gamma^2*z^2|f(z)|^2]dz.
```

Its eigenvalues `alpha_n(gamma)` satisfy

```text
alpha_n(gamma)>=n*(n+1),                                      (LT3)
```

by min--max from `q_gamma>=q_0`.  The constant function belongs to the form domain, so the
spectral theorem and `q_gamma(1)=2gamma^2/3` give

```text
sum_(m>=0) ell_m^2<=2lambda,

sum_(m>=0)(4m)(4m+1)ell_m^2
 <=lambda*q_gamma(1)
 =(2/3)lambda*gamma^2.                                      (LT4)
```

Only the `4m` parity subfamily is summed; dropping the other even parity preserves the
inequalities.

The constant also belongs to the operator domain.  Since

```text
L_gamma(1)=gamma^2*z^2,
```

the spectral theorem gives the second moment

```text
sum_(m>=0)alpha_(4m)^2*ell_m^2
 <=lambda*||L_gamma(1)||_2^2
 =(2/5)*lambda*gamma^4.                                    (LT4a)
```

This extra moment will pay for deliberately coarse polynomial one-mode graph bounds; no sharp
uniform plunge asymptotic is needed.

For `gamma>=2`,

```text
log(m+1)
 <=log(gamma)+(m+1)^2/gamma^2.                               (LT5)
```

Indeed the first term suffices when `m+1<=gamma`; otherwise use
`log((m+1)/gamma)<=((m+1)/gamma)^2`.  Equations `(LT4)`--`(LT5)` prove the concrete modal moment

```text
sum_(m>=0)
 [1+log(gamma)+log(m+1)]ell_m^2
 <=C*lambda*log(gamma).                                      (LT6)
```

This avoids any uniform asymptotic through the Slepian plunge.  The entire high-index sector is
paid for by one exact Sturm-form moment of the constant constraint vector.

## Logarithmically weighted secular-tail theorem

Define

```text
W_(lambda,m)=1+log(gamma)+log(m+1).
```

Because `mu_k<d_(k+1)` and the fixed-index Fuchs hierarchy eventually gives
`2d_(k+1)<=d_(k+2)`, monotonicity of `d_m` implies, for `m>=k+2`,

```text
d_m-mu_k>=d_m-d_(k+1)>=d_m/2.                                (LT7)
```

Apply `(LT7)` to the unnormalized vector

```text
u_m=d_(k+1)*ell_m/(d_m-mu_k).
```

Then `(LT6)` gives

```text
sum_(m>=k+2) W_(lambda,m)d_m|u_m|^2
 <=4*d_(k+1)^2/d_(k+2)
      *sum_(m>=k+2)W_(lambda,m)ell_m^2

 <=C_k*lambda*log(gamma)
      *d_(k+1)^2/d_(k+2).                                   (LT8)
```

The normalization in `(LT2)` is eventually bounded above and below.  Therefore the exact unit
eigenvector satisfies

```text
sum_(m>=k+2) W_(lambda,m)d_m|v_(k,lambda,m)|^2
   /(d_(k+1)log(gamma))

 <=C_k*lambda*d_(k+1)/d_(k+2)
 ->0.                                                        (LT9)
```

The final limit is exactly the fixed-rung `lambda^(-7)` aperture-weighted Fuchs tail law already
isolated abstractly by `ClockEnvelope.tail_tendsto_zero`.

Thus the infinite secular tail is negligible at the true regular-Weil leading scale in the
natural diagonal logarithmic leakage norm.

## Zero-integral compensation removes the dangerous center

The raw tail in `(LT9)` is not itself a legal CCM source: it has nonzero integral, and estimating
its Poisson center separately loses the leakage scale.  This is repaired exactly, not
asymptotically.  Write

```text
t_m=v_(k,lambda,m),                    m>=k+2,
L_tail=sum_(m>=k+2)ell_m*t_m,

r_(k,lambda)
 =sum_(m>=k+2)t_m e_m-(L_tail/ell_0)e_0.                    (LT10)
```

Then `integral r_(k,lambda)=0`.  The complementary head

```text
h_(k,lambda)=v_(k,lambda)-r_(k,lambda)                       (LT11)
```

lies in `span{e_0,...,e_(k+1)}` and also has zero integral.  It therefore belongs to the exact
fixed-dimensional constrained space covered by the intact Toeplitz theorem.

The quadratic Sturm moment is stronger than the logarithmic estimate needed here.  From `(LT4)`,
`(LT7)`, and the normalization in `(LT2)`,

```text
sum_(m>=k+2)(m+1)^2*d_m*|t_m|^2
 <=C_k*lambda*gamma^2*d_(k+1)^2/d_(k+2).                    (LT12)
```

Moreover

```text
|L_tail|
 <=C_k*lambda*d_(k+1)/d_(k+2).                              (LT13)
```

Since `ell_0^2` is bounded below by a positive constant times `lambda`, `d_0<=d_(k+2)`, and
`gamma>=1`, the compensating coefficient satisfies the sharper bound

```text
d_0*|L_tail/ell_0|^2
 <=C_k*lambda*d_0*d_(k+1)^2/d_(k+2)^2
 <=C_k*lambda*d_(k+1)^2/d_(k+2).                            (LT14)
```

Thus compensation preserves the same leakage-weighted Sturm budget.

It also creates the center cancellation which the raw tail lacks.  On the positive `4m` tower the
finite-Fourier eigenvalues are positive and

```text
ell_m=chi_m*e_m(0),       d_m=1-chi_m^2.
```

Consequently

```text
r_(k,lambda)(0)
 =sum_(m>=k+2)t_m*e_m(0)*(1-chi_m/chi_0),                    (LT15)

1-chi_m/chi_0
 =(d_m-d_0)/(chi_0*(chi_0+chi_m)).                           (LT16)
```

For `m>=k+2`, `(LT7)` makes `(d_m-d_0)/(d_m-mu_k)` uniformly bounded.  Therefore the apparent
`1/d_m` secular pole cancels from `(LT15)`.

The remaining positive finite-Fourier kernel diagonal is already controlled by the same Sturm
moment as `(LT4)`.  In the rescaled angular basis put

```text
Y_+(z)=sum_(m>=0)inner(1,y_(4m,gamma))*y_(4m,gamma)(z).
```

This is the orthogonal projection of the constant function onto the `4m` tower.  Spectral
orthogonality and positivity of the Sturm form give

```text
||Y_+||_2^2<=2,
q_gamma(Y_+)
 =sum_(m>=0)alpha_(4m)*|inner(1,y_(4m,gamma))|^2
 <=q_gamma(1)=2gamma^2/3.
```

On `[-1/2,1/2]`, `1-z^2>=3/4`; hence the ordinary local `H1` norm of `Y_+` is `O(gamma)`.
The one-dimensional interior Sobolev evaluation theorem gives

```text
0<=Y_+(0)
 =sum_(m>=0)chi_m*|y_(4m,gamma)(0)|^2
 <=C*(1+gamma).                                               (LT17)
```

After undoing the `x=lambda*z` normalization, this is more than the polynomial diagonal bound
needed for the positive finite-Fourier kernel.  Substitution in `(LT15)` yields

```text
|r_(k,lambda)(0)|<=C_k*(1+gamma)*d_(k+1).                    (LT18)
```

Thus the center estimate is dependency-closed on paper and uses no fixed-mode or plunge
asymptotic.

## One uniform diagonal graph estimate is sufficient

The earlier candidate `(LT10)` asked for an arbitrary-vector domination theorem.  That is
unnecessarily strong and potentially false in that generality because the CCM summation map is an
unbounded critical-line zeta multiplier.  Positivity of a shifted archimedean form reduces the
actual secular-tail problem to a one-mode estimate.

Let `R_(lambda,m)` be the complete radial sum of the exterior leakage of `e_m`, and choose `C_0`
so that

```text
B_lambda=A_arch+C_0*I>=I.
```

The exact remaining regular graph inputs can be deliberately coarse.  It is enough to prove the
degree-uniform diagonal estimates

```text
||R_(lambda,m)||_2^2
 <=C*d_m*(gamma+m+1),

B_lambda(R_(lambda,m),R_(lambda,m))
 <=C*d_m*(gamma+m+1)^2.                                     (LT19)
```

for every `m` and all sufficiently large `gamma`, with one absolute `C`.  These are strictly weaker
than sharp logarithmic asymptotics, weaker than a matrix domination, and are the only all-degree
radial-PSWF inputs required.

Indeed form Cauchy--Schwarz and `(LT19)` give

```text
B_lambda(R(r),R(r))^(1/2)
 <=sum_m |r_m|*B_lambda(R_(lambda,m),R_(lambda,m))^(1/2).
```

For the `L2` line use sequence weights

```text
p_m^(0)=(gamma+m+1)^2*[1+log(m+2)]^2,
```

and for the shifted graph line use

```text
p_m^(1)=(gamma+m+1)^3*[1+log(m+2)]^2.
```

The reciprocal sums forced by `(LT19)` are uniformly bounded:

```text
sum_m (gamma+m+1)/p_m^(0)<=C,
sum_m (gamma+m+1)^2/p_m^(1)<=C.
```

Splitting at `m=gamma`, using `alpha_(4m)>=4m(4m+1)`, and applying `(LT4)` and `(LT4a)` gives

```text
sum_m p_m^(0)*d_m*|r_m|^2
 <=C_k*lambda*gamma^2*log(gamma)^2
      *d_(k+1)^2/d_(k+2),

sum_m p_m^(1)*d_m*|r_m|^2
 <=C_k*lambda*gamma^3*log(gamma)^2
      *d_(k+1)^2/d_(k+2).                                   (LT20)
```

Consequently

```text
||R(r)||_2^2/d_(k+1)
 <=C_k*lambda*gamma^2*log(gamma)^2*d_(k+1)/d_(k+2)
 =O_k(lambda^(-3)*log(lambda)^2)->0,

B_lambda(R(r),R(r))/(d_(k+1)*log(gamma))
 <=C_k*lambda*gamma^3*log(gamma)*d_(k+1)/d_(k+2)
 =O_k(lambda^(-1)*log(lambda))->0.                           (LT21)
```

### The global all-degree estimate can be replaced by a two-sector proof

Dunster's primary theorem is uniform for prolate degrees below any fixed fraction of the Shannon
depth, not through the plunge.  The route does not require extending it through the plunge.

For `0<sigma<1`, define the exterior action

```text
J(sigma)
 =2*integral_sigma^1
    sqrt((t^2-sigma^2)/(1-t^2))dt.
```

This `J` is the exterior barrier action, not Dunster's Section 2 interior action, which equals
`integral_0^sigma sqrt((sigma^2-t^2)/(1-t^2))dt`.

It is continuous, `J(0)=2`, and `J(sigma)->0` as `sigma->1`.  Choose once and for all
`sigma_*<1` with

```text
J(sigma_*)<1.                                                (LT21a)
```

Let `M_gamma` be the largest positive-tower index whose spheroidal turning parameter is at most
`sigma_*`.  Dunster's uniform multi-parameter radial expansions apply on
`m<=M_gamma`; the existing interaction-picture, first-row, and countable-log-chirp arguments then
give the stronger deep-sector bounds

```text
||R_(lambda,m)||_2^2<=C_*d_m,
B_lambda(R_(lambda,m),R_(lambda,m))
 <=C_*d_m*log(gamma),              m<=M_gamma.               (LT21b)
```

All constants depend only on `sigma_*`, not on `m` or `gamma`.

The normalization in `(LT21b)` can be obtained from leakage itself and therefore does not depend
on `(LT21c)`.  For every order-zero degree with `sigma<=sigma_*`, Dunster's pole-uniform formula
has one absolute error constant because his theorem is uniform in the full range
`n<=(2/pi)gamma(1-delta)`.  After the analytic change `r=xi_sigma(x)`, the geometric weight on
`1<=x<=2` is bounded above and below by fixed positive multiples of `r`.  The exact identity

```text
integral_0^R J_0(gamma*r)^2*r dr
 =R^2/2*(J_0(gamma*R)^2+J_1(gamma*R)^2)
```

and the large-argument Bessel envelope give a lower bound `c_*/gamma`, uniformly for the possible
values of `R=xi_sigma(2)`.  The squared `O(gamma^(-1))*envJ_0` remainder is
`O(gamma^(-3))`, and the inequality `(u+v)^2>=u^2/2-v^2` makes the lower bound stable without a
pointwise relative-error claim at Bessel zeros.  Since the total exterior mass is exactly
`d_m/(1-d_m)` by `(LT21c.3)`, and Landau's pre-Shannon bound gives
`1-d_m>=0.4` throughout this sector, this gives the uniform endpoint trace

```text
|U_(lambda,m)(1)|^2<=C_*gamma*d_m.                            (LT21b.1)
```

Dividing the pole-uniform expansion by this endpoint value then gives, uniformly in the degree,
the Bessel-envelope primitive and diagonal estimates used in the fixed-mode cards.  On `x>=2`,
the Liouville phase satisfies

```text
xi_sigma'(x)>=1,
|(1/xi_sigma')'(x)|<=C_*x^(-2),
```

and the exact interaction-picture potential is uniformly short-range for
`0<=sigma<=sigma_*`.  Consequently the normalized amplitudes and their total variations are
bounded by one `C_*`.  Here this uniformity can be checked directly rather than imported from a
fixed-degree asymptotic.  For spheroidal order zero, Dunster `(2.11)` is

```text
psi_sigma(z)
 =-1/((z^2-1)(z^2-sigma^2))
  +(1-sigma^2)*(6z^4-(3+sigma^2)z^2-2sigma^2)
    /(4*(z^2-1)*(z^2-sigma^2)^3).
```

Thus, uniformly for `z>=2` and `0<=sigma<=sigma_*`,

```text
|psi_sigma(z)|<=C_*z^(-4),
|partial_z psi_sigma(z)|<=C_*z^(-5),
1<=xi_sigma'(z)<=C_*,
|(1/xi_sigma')'(z)|<=C_*z^(-3).                                (LT21b.2a)
```

Let `W` be Dunster's exact Liouville transform and let `a_+,a_-` be its exact interaction
amplitudes.  Their limits at infinity are the two coefficients of the real standing wave.
On `2<=z<=3`, the interaction transport differs from those limits by `O(gamma^(-1))`; averaging
the standing wave there therefore shows

```text
|a_+(infinity)|^2+|a_-(infinity)|^2
 <=C_* integral_2^3 |P_n(z)|^2 dz
 <=C_*d_m.                                                      (LT21b.2b)
```

The last inequality uses the exact exterior-mass identity and `1-d_m>=0.4`.  Gronwall applied
backwards from infinity to `(LT21b.2a)` now gives

```text
sup(|a_+|+|a_-|)<=C_*sqrt(d_m),
Var(a_+)+Var(a_-)<=C_*sqrt(d_m)/gamma.                           (LT21b.2c)
```

Restoring the radial prefactor introduces, after extracting the outside factor `1/j`,

```text
K_(sigma,j)(x)
 =j*sqrt(x)*[(j^2*x^2-1)(j^2*x^2-sigma^2)]^(-1/4).
```

For `j>=2`, direct logarithmic differentiation gives

```text
|K_(sigma,j)(x)|<=C_*x^(-1/2),
|K_(sigma,j)'(x)|<=C_*x^(-3/2),                                 (LT21b.2d)
```

uniformly in all three variables.  The derivative of an interaction amplitude after `z=jx`
is inserted is bounded by

```text
C_*sqrt(d_m)*j*|psi_sigma(jx)|/gamma
 <=C_*sqrt(d_m)/(gamma*j^3*x^4).
```

This closes the previously unexpanded differentiated-prefactor audit on `x>=2`.

For the first row, use the exact pole equation `(3.3)` rather than differentiating a printed
additive remainder.  Put

```text
A=z^2-1, delta=1-sigma^2.
```

Changing variables `r=sqrt(t^2-1)` in Dunster's pole action gives exactly

```text
xi=sqrt(A)*h(A,delta),
h(A,delta)=integral_0^1 sqrt((A*u^2+delta)/(A*u^2+1))du,
eta=A*h(A,delta)^2.                                             (LT21b.2e)
```

For `delta>=1-sigma_*^2`, `h` is analytic in `A` near zero with uniformly bounded derivatives and
`h(0,delta)=sqrt(delta)`.  For spheroidal order zero, the sum of the last two rational terms in
Dunster `(3.4)` is

```text
[-delta^2+A*delta^2+A^2*(6delta-4)]
 /(16*A*(A+delta)^3).
```

Its pole is `-1/(16*A*delta)`, while `1/(16*eta)` has pole
`+1/(16*A*delta)` by `(LT21b.2e)`.  Their sum and its first `eta`-derivative therefore extend
continuously with one uniform bound at `A=0`.  Away from zero the claim follows by compactness.
Thus the perturbing coefficient `hat(psi)_sigma(eta)` in the exact pole equation is uniformly
`C^1` on `1<=z<=2`.

The exact Bessel Volterra equation therefore gives, with the endpoint trace `(LT21b.1)`,

```text
|V_(m,j)(1)|+integral_1^infinity |V_(m,j)'(x)|dx
 <=C_*sqrt(d_m)*gamma,                  j>=2.                   (LT21b.2f)
```

The far part uses `(LT21b.2a)`--`(LT21b.2d)`.  The same integration-by-parts proof as in the
existing radial cards now gives

```text
||H_(lambda,m,j)||_2^2<=C_*d_m/j^2,

|inner(H_(lambda,m,i),H_(lambda,m,j))|
 <=C_*d_m/(gamma*i*j*|i-j|),       2<=i!=j,

|inner(H_(lambda,m,1),H_(lambda,m,j))|
 <=C_*d_m/j^2,                     j>=2,                       (LT21b.2)
```

and the weighted primitive is `O(sqrt(d_m)/gamma)`.  The already dependency-closed Hilbert-kernel
summation and countable-log-chirp argument applied with these uniform constants yield exactly
`(LT21b)`.  The uniformization is now dependency-closed on paper; independent hostile audit of
`(LT21b.2b)` and the exact Bessel-Volterra norm remains required before changing the card's stage.

At the cutoff, the same radial connection coefficient has exponential scale

```text
d_(M_gamma)>=gamma^(-C_*)*exp(-J(sigma_*)*gamma).             (LT21c)
```

This line must not be read directly from Dunster's `q_n^0(gamma)`.  At degree proportional to
`gamma`, that quantity contains a superexponential parabolic-cylinder normalization.  In
Dunster's notation, with spheroidal order zero, degree `n=4m`,

```text
a=gamma*alpha^2,
A(a,gamma)=(a/(2e))^(a/2)*(pi^2/(2gamma))^(1/2),

q_n^0(gamma)
 =A(a,gamma)*exp(-gamma*J(sigma)),

Psn_n^0(x,gamma^2)
 ={q_n^0(gamma)/((2n+1)*p_n^0(gamma))}^(1/2)
   *[(x^2-1)(x^2-sigma^2)]^(-1/4)
   *xi^(1/2)[J_0(gamma*xi)+O(gamma^(-1))*envJ_0].              (LT21c.1)
```

Thus the relevant connection amplitude is `q_n^0/p_n^0`, not `q_n^0`.  The normalizing integral
`p_n^0` in Dunster `(6.6)` carries the same large factor.  The exact remaining normalization
lemma is

```text
p_n^0(gamma)<=gamma^C*A(a,gamma)                              (LT21c.2)
```

uniformly when `sigma` lies in a fixed compact subinterval of `(0,1)`.  Its proof is local and
does not require a concentration-eigenvalue estimate or an integrated Olver envelope.

For `a>0`, put `Y_a(z)=U(-a/2,z)`.  Differentiating

```text
Y_a''+(a/2-z^2/4)Y_a=0
```

with respect to `a`, and integrating the resulting Wronskian identity on the positive half-line,
gives

```text
integral_0^infinity Y_a(z)^2 dz
 =2[Y_a partial_a(Y_a')-Y_a' partial_a(Y_a)]_(z=0).            (LT21c.2a)
```

The boundary term at infinity vanishes by the recessive asymptotic for `U`.  DLMF `12.2.6` and
`12.2.7`, followed by the gamma reflection formula, give, with

```text
r=(a+1)/4, theta=pi*r,

Y_a(0)=pi^(-1/2)2^((a-1)/4) Gamma(r) sin(theta),
Y_a'(0)=-pi^(-1/2)2^((a+1)/4) Gamma(r+1/2) cos(theta).
```

Differentiating these two expressions before estimating is essential: the common logarithmic
derivatives cancel.  The duplication formula yields the exact identity

```text
integral_0^infinity Y_a(z)^2 dz
 =Gamma((a+1)/2)/sqrt(2pi)
   *[pi-(digamma(r+1/2)-digamma(r))*sin(theta)*cos(theta)].     (LT21c.2b)
```

For `a` large, the bracket is uniformly bounded because the digamma difference is bounded.
Dunster's Liouville map satisfies

```text
(d zeta/dx)^2
 =(sigma^2-x^2)/((1-x^2)(alpha^2-zeta^2)).
```

Consequently the first integral in his definition `(6.6)` of `p_n^0` becomes

```text
integral_0^zeta(1-delta_0)
 |(alpha^2-zeta^2)/(sigma^2-x(zeta)^2)|
 U(-a/2,sqrt(2gamma)zeta)^2 d zeta.
```

The two action integrals have the uniform turning-point expansions

```text
integral_zeta^alpha sqrt(alpha^2-tau^2)d tau
 =(2/3)sqrt(2alpha)*(alpha-zeta)^(3/2)*(1+O(alpha-zeta)),

integral_x^sigma sqrt((sigma^2-t^2)/(1-t^2))dt
 =(2/3)sqrt(2sigma/(1-sigma^2))*(sigma-x)^(3/2)*(1+O(sigma-x)).
```

Hence the displayed Jacobian ratio extends continuously across the simple turning point, with

```text
lim_(x->sigma) |(alpha^2-zeta^2)/(sigma^2-x^2)|
 =alpha^(2/3)*sigma^(-2/3)*(1-sigma^2)^(-1/3).                 (LT21c.2c)
```

The action maps and this limit depend continuously on `(sigma,x)` on the relevant compact set, so
the ratio is uniformly bounded.  Equations `(LT21c.2a)`--`(LT21c.2b)` and Stirling therefore bound
the first part by

```text
C*gamma^(-1/2)*Gamma((a+1)/2)
 <=C*(a/(2e))^(a/2)*gamma^(-1/2)
 <=C*A(a,gamma).                                               (LT21c.2d)
```

On `1-delta_0<=x<1`, the second term in Dunster's definition of `p_n^0`
contains

```text
q_n^0(gamma)*I_0(gamma*|xi(x)|)^2.
```

Write

```text
S(sigma)=integral_sigma^1 sqrt((t^2-sigma^2)/(1-t^2))dt=J(sigma)/2.
```

Then

```text
|xi(x)|<=S(sigma)-integral_sigma^(1-delta_0)
 sqrt((t^2-sigma^2)/(1-t^2))dt.
```

The last integral has a positive uniform lower bound on the chosen compact `sigma`-interval.
The global elementary bound `I_0(y)<=C exp(y)/sqrt(1+y)`, together with the cancellation of the
endpoint singularity by the factor `|xi(x)|`, gives

```text
q_n^0(gamma)*integral_(1-delta_0)^1
 |xi(x)|*I_0(gamma|xi(x)|)^2
 /sqrt((1-x^2)(x^2-sigma^2)) dx
 <=C*A(a,gamma)*exp(-c*gamma)
 <=C*A(a,gamma).                                               (LT21c.2e)
```

Thus `(LT21c.2)` follows from exact half-line normalization, not an unrecorded Olver-envelope
constant.  The next paragraph audits separately whether Dunster's stated uniform remainder is
strong enough, with its displayed normalization, to convert the connection coefficient into the
claimed exterior-mass lower bound.

The conversion from `(LT21c.1)` to concentration leakage is exact.  If `P_n` has Dunster's
normalization

```text
integral_(-1)^1 P_n(x)^2 dx=2/(2n+1)
```

and `nu_n` is the eigenvalue of
`Q_gamma=(gamma/(2pi))*F_gamma^*F_gamma`, finite-Fourier continuation and Plancherel give

```text
d_n/(1-d_n)
 =(2n+1)/2*integral_(|x|>1)P_n(x)^2 dx,
d_n=1-nu_n.                                                    (LT21c.3)
```

On `2<=x<=3`, both `xi_sigma(x)` and `xi_sigma'(x)` are bounded above and away from zero uniformly
for `sigma` in the chosen compact interval.  The standard large-argument formulas give

```text
J_0(gamma*xi)
 =sqrt(2/(pi*gamma*xi))*(cos(gamma*xi-pi/4)+O(gamma^(-1))),

envJ_0(gamma*xi)
 <=C*(gamma*xi)^(-1/2).
```

After squaring, the `O(gamma^(-1))*envJ_0` remainder in Dunster `(6.5)` has
integral `O(gamma^(-3))`.  For the main term, `cos^2=(1+cos(2*)) / 2` and one
uniform nonstationary integration by parts give a positive `C*gamma^(-1)` lower
bound.  Thus Dunster's pointwise absolute remainder is sufficient; no pointwise relative
estimate at the Bessel zeros is being assumed.  Integrating the squared radial expansion gives

```text
integral_(2)^3 P_n(x)^2 dx
 >=C*gamma^(-1)*q_n^0(gamma)/((2n+1)*p_n^0(gamma)).            (LT21c.4)
```

Equations `(LT21c.1)`--`(LT21c.4)` give

```text
d_n>=C*gamma^(-1)*exp(-gamma*J(sigma_n)).                      (LT21c.5)
```

For the largest step-four index with `sigma_(4M_gamma)<=sigma_*`, Dunster's uniform
quantization law

```text
gamma*integral_0^sigma
 sqrt((sigma^2-t^2)/(1-t^2))dt
 =pi/2*(n+1/2)+O(gamma^(-1))
```

and monotonicity show

```text
sigma_(4M_gamma)=sigma_*+O(gamma^(-1)),
J(sigma_(4M_gamma))=J(sigma_*)+O(gamma^(-1)).                  (LT21c.6)
```

The step size is four and the derivative of the action coordinate is bounded away from zero near
the fixed positive `sigma_*`.  Substitution in `(LT21c.5)` is the claimed `(LT21c)`.

whereas every fixed-rung leakage has scale

```text
d_(k+1)<=gamma^(C_k)*exp(-2gamma).                            (LT21d)
```

Thus monotonicity gives, throughout `m>M_gamma`,

```text
d_(k+1)^2/d_m^2
 <=poly_k(gamma)*exp(-[4-2J(sigma_*)]gamma)
 =o(d_(k+1)*gamma^(-A))                                     (LT21e)
```

for every fixed `A`, precisely because `(LT21a)` holds.  On this upper sector no
leakage-preserving radial estimate is needed.

The required polynomial source-graph bound is elementary at finite aperture.  Min--max also gives

```text
alpha_n(gamma)<=n*(n+1)+gamma^2.
```

There are only `n<=lambda^2` physical samples in the aperture summation map.  The
one-turning-point/nodal partition bounds the variation of one degree-`n` source by a fixed
polynomial in `gamma+n`, and differentiating each of the finitely many sample branches preserves a
fixed polynomial bound.  Finally, for a compactly supported BV function `u`, Plancherel at low
frequency and `|Fourier(u)(xi)|<=Var(u)/|xi|` at high frequency give

```text
integral log(2+|xi|)*|Fourier(u)(xi)|^2 dxi
 <=C_H*(||u||_2^2+Var(u)^2).
```

The finite polar and prime blocks have polynomial operator norm as well.  Hence, for one fixed
polynomial `P`,

```text
||R_lambda E(e_m)||_2^2
 +|Q_(lambda,finite)(R_lambda E(e_m))|
 <=P(lambda,m).                                              (LT21f)
```

This can be summed against the constraint coefficients because, for every `r`,

```text
sum_m alpha_(4m)^(2r)*ell_m^2
 <=lambda*||L_gamma^r(1)||_2^2
 <=C_r*lambda*(1+gamma)^(4r).                               (LT21g)
```

Repeated application of the Sturm operator to `1` remains a polynomial.  Equations
`(LT21e)`--`(LT21g)` therefore make the entire upper sector exponentially negligible.

Therefore the true analytic core is weaker than global `(LT19)`: prove `(LT21b)` with the exact
uniform normalizations and prove the cutoff lower bound `(LT21c)`.  No estimate uniform through
the Slepian plunge is required.

The cross term with the fixed head is `o(d_(k+1)log(gamma))` by form
Cauchy--Schwarz.  This avoids any all-depth Toeplitz matrix bound.

## The intact polar--prime block has enough polynomial budget

At matching height `H=2log(lambda)`, the continuous polar convolution has `L2` operator norm
`O(lambda)`.  The finite-prime translation operator has the same bound:

```text
sum_(n<=lambda^2)Lambda(n)/sqrt(n)=O(lambda)                 (LT22)
```

by elementary Chebyshev control and partial summation.  Hence the noncentral intact
polar--prime block has norm `O(lambda)` on the finite aperture.  Equations `(LT20)`--`(LT21)` then
give

```text
|Q_defect(r,r)|/(d_(k+1)log(gamma))
 =O_k(lambda^(-2)*log(lambda))->0,

|Q_defect(h,r)|/(d_(k+1)log(gamma))
 =O_k(lambda^(-1/2))->0,                                    (LT23)
```

before center terms.  The compensated endpoint estimate `(LT18)` makes every center--center and
center--radial term exponentially smaller than the same scale after any fixed polynomial aperture
loss.  Thus `(LT19)` and the already paper-proved fixed-depth intact theorem would
transfer the intact Toeplitz law from `h` to the true constrained eigenvector `v=h+r`.

## Exact remaining graph bridge

Equation `(LT9)` is not yet a theorem about the Weil form.  The remaining source-specific
analytic core has now been reduced to:

```text
uniform deep-sector normalization and graph bounds (LT21b)
  + cutoff leakage lower bound (LT21c)
  + polynomial upper-sector source graph (proved).           (LT24)
```

No arbitrary-vector Weil domination, cofinal Toeplitz upper bound, or uniform plunge asymptotic is
required.  Global `(LT19)` remains a convenient sufficient theorem, but `(LT21a)`--`(LT21f)` show
it is not necessary.

The route separation is therefore:

```text
secular formula + Sturm moment + Fuchs hierarchy
  -> compensated zero-integral tail with quadratic leakage moment

positive spectral-kernel diagonal (proved) + two-sector radial graph (open)
  -> true constrained-eigenvector fixed-depth Toeplitz limit

growing-depth profile exhaustion + boundary sign (still RH-facing)
  -> possible full Weil positivity.
```

## Hostile audit

1. **No source-`L2` shortcut.**  `(LT9)`, not the previously known `O(lambda^(-15))` source tail,
   is the claimed bridge resource.
2. **No plunge asymptotic.**  `(LT6)` uses the exact Sturm form of the constant vector and does not
   assume uniform Fuchs/Dunster estimates for `m` growing with `lambda`.
3. **No unbounded-map shortcut.**  The arbitrary-vector form bound formerly proposed as `(LT10)`
   has been withdrawn.  Even global one-mode `(LT19)` is only sufficient: the exact open core is
   the two-sector package `(LT21b)`--`(LT21f)`.
4. **Fixed rung only.**  Constants may depend on `k`; no cofinal-depth interchange is claimed.
5. **Parity.**  The proof uses only that the selected tower is a subset of the even angular
   prolate basis.  It therefore has a parallel `4m+2` statement after replacing the fixed-rung
   Fuchs data.  This card writes the positive `4m` tower because that is the tower used by the
   current fixed-depth intact theorem.

## Novelty audit

Internal searches found the unweighted secular tail `(23)` and the abstract
`ClockEnvelope.tail_tendsto_zero`, but no logarithmically weighted tail or use of the constant
constraint's Sturm-form moment to cross the Slepian plunge.

Targeted primary-literature searches found uniform PSWF/eigenvalue estimates and transition-region
bounds, but no rank-one zero-integral constrained secular eigenvector estimate matching
`(LT6)`--`(LT9)`:

- A. Bonami and A. Karoui, *Uniform approximation and explicit estimates for the prolate
  spheroidal wave functions*, arXiv:1405.3676.
- S. Karnik, J. Romberg, and M. A. Davenport, *Improved bounds for the eigenvalues of prolate
  spheroidal wave functions and discrete prolate spheroidal sequences*, arXiv:2006.00427.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- Gradshteyn--Ryzhik `7.711.3` already contains an equivalent half-line integral for
  `D_nu^2`.  Thus `(LT21c.2b)` itself is classical; candidate-new content is its use to cancel
  Dunster's proportional-degree normalization in the constrained leakage cutoff.

Search absence establishes no priority.  Status remains `[NOVELTY UNVERIFIED]`.

## Lean plan

Do not formalize `(LT10)` as a hypothesis wrapper.  First formalize only the dependency-closed
positive theorem:

1. the abstract spectral-form moment bound `(LT3)`--`(LT6)`;
2. the secular-tail inequality `(LT8)`;
3. the fixed-rung limit `(LT9)` using the existing `ClockEnvelope` tail theorem.

The concrete angular PSWF Sturm operator is not presently realized deeply enough in the formal
tree to state `(LT4)` without new analytic infrastructure.  Paper audit precedes that build.

## Gates

- [x] internal corpus search
- [x] preliminary primary-literature search
- [x] dependency-closed candidate proof of the constraint logarithmic moment `(LT6)`
- [x] dependency-closed candidate proof of the secular tail `(LT9)`
- [x] isolate the exact zero-integral compensation and endpoint denominator cancellation
      `(LT10)`--`(LT18)`
- [x] reduce all cross-mode graph control to the single-mode diagonal estimate `(LT19)`
- [ ] independent hostile audit of normalization, parity restriction, and Sturm form-domain step
- [x] prove the positive finite-Fourier kernel diagonal bound `(LT17)` from projected-constant
      Sturm energy and local Sobolev evaluation
- [x] dependency-closed candidate proof of the uniform deep-sector graph bounds `(LT21b)` from
      Dunster's multi-parameter interaction-picture expansion
- [x] dependency-closed candidate proof of the cutoff leakage lower bound `(LT21c)` with exact
      concentration normalization
- [ ] independent hostile audit of `(LT21b.2b)`, the exact Bessel-Volterra norm, and the
      Gradshteyn--Ryzhik/Dunster parameter normalization
- [x] prove a polynomial finite-aperture source-graph bound for the upper sector from finite
      sampling, Sturm variation, and the BV logarithmic Fourier estimate
- [ ] audit the `O(lambda)` finite-aperture polar--prime operator norm and every center cross term
- [ ] transfer the fixed-depth Toeplitz law to true constrained leakage eigenvectors
- [ ] formalize `(LT6)`--`(LT9)` unconditionally in Lean

## Log

- 2026-07-27 — Isolated after rejecting the false inference from finite Gram--Schmidt contrasts
  to true constrained leakage eigenvectors.  The Slepian plunge is bypassed by one exact
  Sturm-form moment of the constant constraint vector.
- 2026-07-27 — Withdrew the overstrong arbitrary-vector graph domination target.  Exact
  zero-integral compensation cancels the secular endpoint denominator, and shifted-form
  Cauchy--Schwarz reduces the true tail transfer to one uniform single-mode graph estimate.
