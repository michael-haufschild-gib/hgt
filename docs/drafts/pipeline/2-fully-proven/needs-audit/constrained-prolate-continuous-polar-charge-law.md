# The constrained prolate exterior tail has bounded continuous polar charge

- **ID:** `constrained-prolate-continuous-polar-charge-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE ESTIMATE
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent results:** `constrained-prolate-full-radial-prime-charge-law.md`,
  `ccm-countable-log-chirp-renormalization-law.md`,
  `ccm-exact-radial-nonstationary-sector-bound.md`, Dunster's pole-uniform and exterior radial
  expansions, and the exact CCM polar multiplier
- **Statement:** If `R_lambda` is the exact radial sum of the constrained two-mode prolate source,
  then its aperture-truncated continuous polar charge is `O(d_1(lambda))`, uniformly at the
  matching aperture `a_lambda=log lambda`. Consequently the complete polar--prime exterior
  contribution is `O(d_1(lambda))`, and the exact exterior Weil seed has the positive leading law
  `D_arch*d_1(lambda)*log(2*pi*lambda^2)+O(d_1(lambda))`.

## Setup

Put

```text
c=2*pi*lambda^2,
d_lambda=1-chi_4(lambda)^2,

H_(lambda,k)(s)
 =sqrt(lambda*exp(s))*q_lambda(k*lambda*exp(s)),

R_lambda(s)=sum_(k>=1)H_(lambda,k)(s),             s>=0.       (1)
```

Let

```text
C_R,lambda(h)=integral_0^infinity
  R_lambda(s+h)R_lambda(s)ds,                    h>=0,          (2)
```

and let `a_lambda=log lambda`.  The continuous polar charge on the lower exterior tail is

```text
PPol_lambda(R_lambda)
 =4 Re integral_0^(2*a_lambda)
    cosh(h/2) C_R,lambda(h)dh.                                  (3)
```

The exact radial norm theorem gives

```text
||R_lambda||_2^2=O(d_lambda).                                  (4)
```

## Abstract primitive reduction

For a real `R in L2(0,infinity)`, define

```text
F(s)=exp(s/2)R(s),
G(s)=exp(-s/2)R(s),
A(t)=integral_0^t F(s)ds.                                      (5)
```

Assume `A` is bounded.  Since `G` belongs to `L1` by Cauchy--Schwarz,

```text
||G||_1<=||R||_2.                                              (6)
```

Fubini on finite rectangles, followed by the `L1` limit, gives for every `H>=0`

```text
integral_0^H exp(h/2)C_R(h)dh
 =integral_0^infinity
   G(s)[A(s+H)-A(s)]ds.                                        (7)
```

Hence

```text
|integral_0^H exp(h/2)C_R(h)dh|
 <=2||A||_infinity||R||_2.                                    (8)
```

The opposite branch needs no oscillatory estimate:

```text
|C_R(h)|<=||R||_2^2,

|integral_0^H exp(-h/2)C_R(h)dh|
 <=2||R||_2^2.                                                 (9)
```

Equations `(8)`--`(9)` prove

```text
|4 Re integral_0^H cosh(h/2)C_R(h)dh|
 <=4||A||_infinity||R||_2+4||R||_2^2.                          (10)
```

Thus the polar source estimate reduces to one weighted-primitive theorem.

## Exact radial primitive target

The required estimate is

```text
sup_(H>=0)
 |integral_0^H exp(s/2)R_lambda(s)ds|
 <=C*sqrt(d_lambda).                                           (11)
```

In fact Dunster's radial phases predict the stronger `O(sqrt(d_lambda)/c)` bound.

For one radial component, set `x=exp(s)`.  Then

```text
integral_0^H exp(s/2)H_(lambda,k)(s)ds
 =integral_1^(exp H) U_(lambda,k)(x)dx/sqrt(x),                 (12)

U_(lambda,k)(x)=sqrt(lambda*x)q_lambda(k*lambda*x).
```

For `k>=2`, the exact phase-preserving exterior expansion is

```text
U_(lambda,k)(x)
 =sqrt(d_lambda)/k sum_(epsilon=+-1)
   exp(i*epsilon*c*xi_c(k*x))a_(epsilon,c,k)(x),                (13)

|a_(epsilon,c,k)(x)|<=C*x^(-1/2),
|a_(epsilon,c,k)'(x)|<=C*x^(-3/2).                              (14)
```

Moreover

```text
|d/dx xi_c(k*x)|>=c_0*k.                                      (15)
```

One integration by parts in `(12)` therefore gives, uniformly in `H`,

```text
|integral_0^H exp(s/2)H_(lambda,k)(s)ds|
 <=C*sqrt(d_lambda)/(c*k^2),          k>=2.                    (16)
```

The series in `(16)` is summable.  For `k=1`, Dunster's pole-uniform Bessel representation in the
analytic endpoint coordinate gives the companion estimate

```text
|integral_0^H exp(s/2)H_(lambda,1)(s)ds|
 <=C*sqrt(d_lambda)/c,                                         (17)
```

again uniformly in `H`.  The endpoint interval has width `O(c^(-2))`; outside it, the Bessel
branches are nonstationary and one integration by parts supplies `(17)`.  Equations `(16)`--`(17)`
imply `(11)`.

Combining `(4)`, `(10)`, and `(11)` gives

```text
PPol_lambda(R_lambda)=O(d_lambda).                             (18)
```

### Passage from finite radial sums

Let `R_(lambda,N)=sum_(1<=k<=N)H_(lambda,k)`.  Equations `(16)`--`(17)` give the primitive bound
uniformly in both `N` and `H`.  The weighted projective Gram theorem implies
`R_(lambda,N)->R_lambda` in `L2(0,infinity)`.  For each fixed `H`, the functional

```text
f |-> integral_0^H exp(s/2)f(s)ds
```

is continuous on `L2(0,H)`.  Passing `N->infinity` first therefore retains the same bound for
each `H`; taking the supremum afterwards proves `(11)`.  No interchange of an infinite radial sum
with an improper primitive is used.

## Poisson--BV radial envelope

The far radial phase is not needed for the center audit. Put `a=lambda*exp(t)` and let
`g_lambda^+` be the positive-half compact source, extended by zero. The source is even and has
zero integral, so the exact one-sided Poisson--Muntz identity is

```text
sqrt(a)*sum_(k>=1)q_lambda(k*a)
 =1/sqrt(a)*sum_(n>=1)g_lambda(n/a)
  +g_lambda(0)/(2*sqrt(a)).                                    (19a)
```

The final term in `(19a)` is exactly the Poisson center. Hence

```text
b_lambda(t)=R_lambda(t)-C_lambda(t)
 =1/sqrt(a)*sum_(n>=1)g_lambda(n/a).                            (19b)
```

The sum in `(19b)` is finite because `g_lambda` is compactly supported. It is the square-root
normalization of a right-endpoint Riemann sum for the zero integral of `g_lambda^+`. The exact BV
quadrature theorem gives, without a Fourier-tail estimate,

```text
|b_lambda(t)|
 <=2*Var(g_lambda^+)/sqrt(lambda)*exp(-t/2),                    (19c)

|R_lambda(t)|
 <=[2*Var(g_lambda^+)+|g_lambda(0)|/2]
    /sqrt(lambda)*exp(-t/2).                                   (19d)
```

The formal theorem permits the support endpoint to fall between lattice points and includes the
last partial cell. Thus `(19c)` is not an asymptotic Euler--Maclaurin statement and does not
interchange the radial series with a limit.

For the fixed `m=0,4` constrained source, the strongest convenient source-side estimate is

```text
Var(g_lambda^+)=O(1).                                          (19e)
```

This does **not** require prolate-to-Hermite convergence in `W^(1,1)`. Put `z=x/lambda`. Each
angular prolate mode `y_n(z)=h_(n,lambda)(lambda*z)` satisfies

```text
((1-z^2)y_n')'=(gamma^2*z^2-alpha_n)y_n,   gamma=2*pi*lambda^2. (19f)
```

On `0<z<1`, the coefficient on the right has at most one zero. Remove that turning point and the
`n/2` positive nodal zeros of the even degree-`n` spheroidal function. On every remaining interval
both right-hand factors in `(19f)` have fixed nonzero sign, so `(1-z^2)y_n'` is strictly monotone
and `y_n'` has at most one zero. Nodal zeros are simple; the turning point and `z=0` add at most two
further critical points. Hence every fixed even mode has a number `M_n` of monotonicity intervals
bounded independently of `lambda`, and

```text
Var_(0,lambda)(h_(n,lambda))
 <=2*M_n*||h_(n,lambda)||_infinity.                            (19g)
```

CCM Lemma 7.2 gives uniform sup bounds for `n=0,4`. The coefficients of the unique
vanishing-integral combination are bounded because
`integral h_(n,lambda)=chi_n(lambda)h_(n,lambda)(0)` and these factors converge to nonzero Hermite
limits. Variation is subadditive, so `(19e)` follows; zero extension adds only the bounded endpoint
jump. This one-turning-point Sturm argument replaces the previously unproved `W^(1,1)` assertion.

The exact resource threshold is weaker but must be stated with the correct logarithm:
`(27)=o(d_lambda)` follows from
`Var(g_lambda^+)=o(lambda/log lambda)`, while preservation of the positive
`d_lambda*log lambda` leading term alone follows from `Var(g_lambda^+)=o(lambda)`. The formerly
stated condition `o(lambda*log lambda)` was insufficient. This replaces the former
leakage-normalized `z^(-2)` far-field gate by a compact-source regularity theorem.

## Poisson center: the critical Mellin coupling cannot be discarded

The exact lower tail is

```text
b_lambda(s)=R_lambda(s)-C_lambda(s),
C_lambda(s)=g_lambda(0)/(2*sqrt(lambda))*exp(-s/2),             (19)
```

with `g_lambda(0)=O(d_lambda)`.  The exterior representative is not supported in the finite
aperture.  Its global polar and prime center terms therefore cannot be bounded by finite-aperture
kernel masses separately.  They must be combined through the critical Mellin measure

```text
dM(h)=2*cosh(h/2)dh
  -sum_(n>=2)Lambda(n)n^(-1/2)delta_(log n)(h).                  (20)
```

Write

```text
p_lambda=g_lambda(0)/(2*sqrt(lambda)),
M_R=int_0^infinity exp(-s/2)R_lambda(s)ds,
T_R(h)=int_h^infinity exp(-s/2)R_lambda(s)ds.                   (21)
```

For `h>=0`, the exact cross and center autocorrelations are

```text
C_(R,C)(h)+C_(C,R)(h)
 =p_lambda[exp(h/2)T_R(h)+exp(-h/2)M_R],

C_C(h)=p_lambda^2 exp(-h/2).                                   (22)
```

The Abel boundary theorem for the critical Mellin channel proves

```text
Abel-int_0^infinity exp(-h/2)dM(h)=1+EulerGamma.                (23)
```

Hence the second cross term and the center--center term in `(22)` are respectively
`O(|p_lambda*M_R|)` and `O(p_lambda^2)`.  Since `|M_R|<=||R_lambda||_2`, they are
`o(d_lambda)`.

For the first cross term, finite-cutoff Fubini gives

```text
int_0^H exp(h/2)T_R(h)dM(h)
 =int_0^infinity exp(-t/2)R_lambda(t)J_H(t)dt,                  (24)
```

where `J_H(t)=J(min(H,t))` is the weighted cumulative defect clipped at the finite aperture and

```text
J(t)=int_0^t exp(h/2)dM(h)
 =exp(t)-1+t-Psi(exp(t))
 =t-1-E(exp(t)).                                                (25)
```

No prime-number-theorem remainder is needed. Chebyshev's elementary bound
`Psi(x)<=(log 4+4)x` gives

```text
exp(-t)|J(t)|<=log 4+7,                                        (26)

int_0^H exp(-t)|J_H(t)|dt
 <=(log 4+7)(H+1).                                             (26a)
```

The final `+1` in `(26a)` is the frozen tail
`exp(-H)|J(H)|`. Combining `(19d)` with `(24)`--`(26a)` gives directly

```text
|p_lambda|*
 |int_0^infinity exp(-t/2)R_lambda(t)J_H(t)dt|
 <=C*|g_lambda(0)|
   [Var(g_lambda^+)+|g_lambda(0)|]*(H+1)/lambda.                 (27)
```

At the matching height `H=2*log lambda`, `g_lambda(0)=O(d_lambda)` and the fixed-mode variation
law `(19e)` make `(27)` `O(d_lambda*log(lambda)/lambda)=o(d_lambda)`. More generally, the
sufficient rate budget delivered by the absolute estimate `(27)` is

```text
Var(g_lambda^+)=o(lambda/log lambda)  -> center error=o(d_lambda),
Var(g_lambda^+)=o(lambda)             -> center error=o(d_lambda*log lambda).
```

The second line is sufficient to preserve the positive leading coefficient; the first preserves
the stronger `O(d_lambda)` remainder asserted in `(32)`. These are not claimed to be necessary if
additional cancellation is found in the center pairing.

Equations `(22)`--`(27)` yield the genuine global statement

```text
Q_(polar-prime)(b_lambda,b_lambda)
 =Q_(polar-prime)(R_lambda,R_lambda)+o(d_lambda).               (29)
```

## Full exterior Weil consequence

The exact radial prime theorem, with the full divisor weight `log k`, gives

```text
QPrime_lambda(R_lambda,R_lambda)=O(d_lambda),                   (30)
```

with an explicit limiting coefficient, while the countable log-chirp theorem gives

```text
AArch(R_lambda,R_lambda)
 =D_arch*d_lambda*log(c)+O(d_lambda),

D_arch=8/(11*pi)sum_(k>=1)arcsin(1/k)/k>0.                     (31)
```

Equations `(18)` and `(23)`--`(31)` would prove the unconditional source estimate

```text
QW(a_lambda,a_lambda)
 =D_arch*d_lambda*log(2*pi*lambda^2)+O(d_lambda),               (32)
```

where `a_lambda` is the restricted CCM seed and the radical quotient identifies its Weil value
with that of `b_lambda`.  In particular the seed Rayleigh value is eventually positive and tends
to zero.

This closes the coupled polar--prime critical Mellin defect at the seed level.  It does not control
the true even spectral floor or the true gap, and therefore does not prove RH.

## Positive Connes obligation after the source estimate

If `(17)` and `(27)` are verified with the exact differentiated pole-uniform and summed radial
remainders, the first unresolved Connes theorem moves from source assembly to spectral selection:

```text
positive explicit seed law (32)
  + true even ground lower bound and gap comparison
  + locally uniform normalized determinant convergence to Xi
  -> RH.                                                        (33)
```

The source must therefore carry a reduced-resolvent incidence estimate strong enough to compare
the positive prolate seed with the true restricted-Weil ground state.  The exact sufficient rate
remains

```text
RayleighExcess_lambda/Gap_lambda=O(lambda^(-1)).                (34)
```

## Novelty and significance gate

The abstract primitive identity `(7)` is elementary.  The potentially new content is the
continuous polar-charge consequence `(18)` for the exact constrained radial prolate sum and its
closure of the coupled global source law `(32)`. The Poisson--BV envelope is a classical
quadrature bridge, but it removes the unnecessary far-field PSWF phase gate from the source
theorem. No parent statement of the continuous polar estimate was located in the CCM or
radial-PSWF literature. Significance is high if `(17)` and the fixed-mode variation input `(19e)`
survive formula-level audit because they remove the first analytic source gate in the determinant
route without assuming a Weil floor or an RH-equivalent bound.

## Lean plan

The formal tree already contains the exact finite-dimensional polar signature, the
autocorrelation/Stieltjes identity, and the abstract first-order interaction-picture transport.
The required new infrastructure is:

1. `[FORMALIZED]` the half-line autocorrelation/Fubini module `(7)`--`(10)`;
2. `[FORMALIZED]` the zero-mean BV square-root lattice envelope `(19c)`;
3. `[FORMALIZED]` the exact critical-Mellin cumulative `(25)` and its finite-aperture Chebyshev
   mass bound `(26a)`;
4. `[FORMALIZED]` the actual complex clipped center pairing and its linear-in-aperture norm bound
   under the half-density radial envelope;
5. `[FORMALIZED]` the exact normalized-budget transfer: sublinear variation preserves the
   `d_lambda*log(lambda)` leading scale, while the sharper logarithmically weighted budget makes
   the center error `o(d_lambda)`;
6. `[PHASE FORMALIZED; AMPLITUDE OPEN]` a concrete radial-PSWF endpoint/exterior interface proving
   the all-radial primitive `(11)`;
7. `[CANONICAL TWO-MODE SOURCE AND POISSON--MUNTZ LAW FORMALIZED; CLASSICAL IDENTIFICATION OPEN]`
   identify the classical real `h_0,h_4` modes in the actual operator spectrum and prove the
   concrete fixed-mode variation bound `(19e)`;
8. the constrained-source and critical-Mellin specialization `(18)`--`(32)`.

The universal variation endpoint of item 7 is now formalized in
`HTGeometry/FiniteMonotonicityVariation.lean`: one-sign Sturm cells contain at most one critical
point and an `n`-cell monotonicity partition has variation at most `2*n*||f||_infinity`.
`RHTower/ProlateOneTurningVariation.lean` proves the exact prolate flux equation and both sign-cell
critical-point specializations. The remaining Lean work is the classical spheroidal nodal-count
instance, ordered partition assembly, and concrete representative.

No abstract hypothesis wrapper is sufficient: the concrete prolate primitive, one-sided Poisson
specialization, and fixed-mode variation estimate must be theorems before `(32)` can be promoted
or used in a paper.

### Exact open core after the generic Abel theorem

The generic analytic identity is no longer open. The formal theorem now gives `(19a)` for every
integrable even compactly supported real source of zero mean at a symmetric Lebesgue point, and
proves that its physical lattice tail has literal finite support. The first route-specific missing
map is therefore

```text
constrained L2 prolate mode
  -> canonical real pointwise representative g_lambda
  -> even + compact support + L1 + integral zero
  -> symmetric Lebesgue point of its scaled periodization at 0
  -> Fourier(g_lambda)=q_lambda.                                (35)
```

`ConstrainedProlatePointwiseRepresentative.lean` now constructs the canonical half-endpoint source
for every nonzero eigenmode of the actual even time-band operator. It proves compact support,
integrability, exact evenness, equality with the original `L2` vector almost everywhere, exact
pointwise Fourier identification, the interior eigen-equation, and both half-endpoint equations.
`ConstrainedProlatePoissonMuntz.lean` now closes the rest of `(35)` generically for every pair of
nonzero eigenmodes: opposite-integral coefficients give exact zero mean, real extraction preserves
evenness/integrability/compact support, half endpoints make the scaled periodization continuous at
zero, continuity supplies the symmetric-Lebesgue condition, and the exact square-root-normalized
one-sided Poisson--Muntz physical-lattice law follows. The remaining part of `(35)` is therefore
only identification of the classical real `h_0,h_4` modes inside the actual operator spectrum.
After that identification, the fixed-mode
regularity law

```text
Var(g_lambda^+)=O(1),                                          (19e)
```

is paper-proved by the one-turning-point Sturm argument `(19f)`--`(19g)`, but its universal
variation lemma and concrete spheroidal instance still require Lean formalization. It is then
substituted into the already formalized BV envelope and clipped critical-Mellin pairing. This
separates the representative/regularity problem from the completed Abel machinery.

## Gates

- [x] exact polar charge reduced to one weighted primitive
- [x] `k>=2` exterior primitive estimate reduced to existing phase-preserving amplitudes
- [x] `k=1` primitive split into endpoint, Bessel, and exterior sectors with summable envelopes
- [x] pass finite radial primitives to the exact radial sum by projective `L2` convergence
- [x] center autocorrelations reduced exactly to the Abel boundary value and the PNT-weighted
  radial integral `(24)`
- [x] replace the global radial phase tail by the exact Poisson--BV lattice envelope
- [x] formalize the square-root BV lattice envelope, including a non-lattice support endpoint
- [x] formalize the growing critical-Mellin cumulative `(25)` and the clipped mass bound `(26a)`
- [x] formalize the actual complex finite-aperture center pairing and prove its improper tail is
  integrable under the half-density radial envelope
- [x] formalize the bilateral Poisson--Abel series, its exact Poisson-integral identity, and its
  boundary convergence at every symmetric Lebesgue point
- [x] formalize the exact exterior Liouville phase, dilation derivative, and derivative floor
- [x] compute and formalize the scaled compact-periodization Fourier coefficients for every L1
  source, with exact value `a * Fourier(f)(a*m)`
- [x] combine evenness, zero mean, compact support, and the Abel boundary theorem into the exact
  generic one-sided Poisson--Muntz specialization, including a finite physical-lattice cutoff
- [x] formalize the normalized center-budget transfer and the sublinear-variation sufficient law
  at the `d_lambda*log(lambda)` leading scale
- [x] construct the canonical compact half-endpoint representative of every nonzero actual
  even time-band eigenmode and identify its pointwise Fourier transform
- [ ] identify the classical real `h_0,h_4` pair in the actual spectrum; constrained contrast,
  real extraction, symmetric-Lebesgue regularity, and source-specific identity `(19a)` are already
  formalized for every nonzero eigenmode pair
- [x] prove the fixed-mode source variation bound `(19e)` on paper by one-turning-point Sturm
  oscillation; Lean specialization remains open
- [ ] promote `(18)` and `(32)` after the primitive and source-regularity audits
- [ ] formalize the concrete radial-PSWF primitive theorem and its polar consequence in Lean
- [ ] true even ground/gap comparison
- [ ] locally uniform determinant convergence to `Xi`

## Formula-level closure of the pole-uniform primitive

The remaining paper gap in `(17)` is closed by using Dunster's Bessel expansion only on a fixed
endpoint interval and the phase-preserving exterior expansion only where its potential is
short-range. This avoids factoring the additive pole-uniform error through an oscillatory
exponential.

Fix one of the two one-dimensional PSWF degrees `n=0,4`. These are both spheroidal-order-zero
solutions: Dunster's order parameter is `m=0`, while his degree parameter is `n=0,4`. Thus the
Bessel function in his formula `(3.5)` is `J_0` for both CCM modes. Write `q_(n,lambda)` for the
exterior Fourier transform, `d_n(lambda)=1-chi_n(lambda)^2`, and

```text
U_(n,lambda)(x)=sqrt(lambda*x)q_(n,lambda)(lambda*x).
```

The required single-mode estimate is

```text
sup_(X>=1)
 |integral_1^X U_(n,lambda)(x)dx/sqrt(x)|
 <=C_n*sqrt(d_n(lambda))/c.                                    (36)
```

### Endpoint interval

The endpoint-response identity and differentiated fixed-mode asymptotic in
`ccm-constrained-endpoint-euler-response-constant.md` give

```text
sqrt(lambda)*|q_(n,lambda)(lambda)|
 <=C_n*sqrt(c)*sqrt(d_n(lambda)).                               (37)
```

Dunster's pole-uniform formula `(3.5)`, divided by its nonzero endpoint value, gives uniformly
for `1<=x<=2`

```text
q_(n,lambda)(lambda*x)/q_(n,lambda)(lambda)
 =A_(sigma,c)(x)
   [J_0(c*xi_sigma(x))+c^(-1)E_(n,c)(x)],

|E_(n,c)(x)|<=C_n*envJ_0(c*xi_sigma(x)),                         (38)
```

where

```text
xi_sigma(x)
 =integral_1^x sqrt((t^2-sigma^2)/(t^2-1))dt,

A_(sigma,c)(x)
 =[xi_sigma(x)^2/((x^2-1)(x^2-sigma^2))]^(1/4),                 (39)
```

and `sigma^2=O_n(c^(-1))`. Put `r=xi_sigma(x)` and let `x=X_sigma(r)` be the inverse
coordinate. Dunster's endpoint coordinate `eta=xi_sigma^2` is analytic at `x=1`, with

```text
eta=2*(1-sigma^2)*(x-1)+O((x-1)^2).                             (40)
```

Consequently

```text
A_(sigma,c)(X_sigma(r))*X_sigma'(r)=r*B_(sigma,c)(r),            (41)
```

where, explicitly,

```text
B_(sigma,c)(r)
 =(X_sigma(r)^2-1)^(1/4)
  /(r^(1/2)*(X_sigma(r)^2-sigma^2)^(3/4)).                      (42)
```

The apparent singularity at `r=0` is removable by `(40)`. More explicitly,

```text
B_(sigma,c)(r)
 =[((X_sigma(r)^2-1)/eta)/
    (X_sigma(r)^2-sigma^2)^3]^(1/4),   eta=r^2.                 (42a)
```

The quotient `(x^2-1)/eta(x)` is positive analytic at `x=1`, and the analytic inverse is a
function of `eta=r^2`. Since fixed-mode `sigma^2=O(c^(-1))`, these functions and their first
derivatives are uniformly bounded on the compact parameter set
`1<=x<=2`, `0<=sigma^2<=1/2`. Hence

```text
||B_(sigma,c)||_(C^1[0,xi_sigma(2)])<=C_n.                      (43)
```

Use

```text
d/dr [r*J_1(c*r)]=c*r*J_0(c*r),
|J_1(u)|<=C*min(u,u^(-1/2)).                                   (44)
```

Integration by parts, first on `0<=r<=min(R,c^(-1))` and then on
`c^(-1)<=r<=R`, proves uniformly in every partial endpoint `R` that

```text
|integral_0^R r*B_(sigma,c)(r)J_0(c*r)dr|
 <=C_n*c^(-3/2).                                                (45)
```

The standard Bessel envelope bound gives

```text
integral_0^R r*|B_(sigma,c)(r)|envJ_0(c*r)dr
 <=C_n*integral_0^R r*(1+c*r)^(-1/2)dr
 <=C_n*c^(-1/2).                                                (46)
```

The extra `c^(-1)` in the error term of `(38)` makes its contribution
`O_n(c^(-3/2))` as well. Multiplying `(45)`--`(46)` by the endpoint
normalization `(37)` yields

```text
sup_(1<=X<=2)
 |integral_1^X U_(n,lambda)(x)dx/sqrt(x)|
 <=C_n*sqrt(d_n(lambda))/c.                                    (47)
```

This is the missing pole-uniform estimate. Only the printed additive Bessel-envelope error is
used; no derivative or phase factorization of that error is required.

### Exterior interval

On `x>=2`, Dunster's exterior Liouville--Green formulas `(2.19)`--`(2.21)` and the exact
interaction-picture transport theorem give

```text
U_(n,lambda)(x)
 =sqrt(d_n(lambda))*sum_(epsilon=+-1)
   exp(i*epsilon*c*xi_sigma(x))*a_(epsilon,n,c)(x),

|a_(epsilon,n,c)(x)|<=C_n*x^(-1/2),
|a_(epsilon,n,c)'(x)|<=C_n*x^(-3/2).                            (48)
```

The amplitudes in the integral are `a_(epsilon,n,c)(x)/sqrt(x)`, whose boundary value and
total variation on `[2,infinity)` are uniformly bounded. Moreover

```text
xi_sigma'(x)>=1,
|(1/xi_sigma')'(x)|<=C_n*x^(-2).                               (49)
```

One integration by parts in each branch of `(48)` therefore proves

```text
sup_(X>=2)
 |integral_2^X U_(n,lambda)(x)dx/sqrt(x)|
 <=C_n*sqrt(d_n(lambda))/c.                                    (50)
```

Equations `(47)` and `(50)` prove `(36)`.

### Constrained source and all radial channels

The opposite-integral coefficients of the normalized degree-`n=0,4` constrained source stay bounded,
while

```text
d_0(lambda)/d_1(lambda)=O(lambda^(-8)).
```

Thus `(36)` proves the `k=1` estimate `(17)` for the constrained source. For `k>=2`, the existing
exterior estimate `(16)` gives

```text
sup_(H>=0)
 |integral_0^H exp(s/2)H_(lambda,k)(s)ds|
 <=C*sqrt(d_1(lambda))/(c*k^2).
```

The `k`-majorant is summable. Passing first from finite radial sums to `R_lambda` in `L2(0,H)`
and then taking the supremum in `H` proves `(11)`. The abstract primitive identity `(10)` now
gives the unconditional paper theorem

```text
PPol_lambda(R_lambda)=O(d_1(lambda)).                            (51)
```

Together with the already proved radial-prime, log-chirp, Poisson-center, and critical-Mellin
estimates, this proves the seed law `(32)` on paper.

## Hostile post-closure audit

- The Poisson--BV estimate controls the center cross-terms but does not by itself control the
  `R_lambda`--`R_lambda` polar term. The Bessel/exterior proof above is essential.
- The theorem concerns one explicit source sequence and is not Weil-complete. It neither proves a
  true restricted-Weil floor nor implies RH.
- The tracked card before this proof ended at the former gate list; equations `(36)`--`(51)` are
  not a rediscovery from the shared worktree. Independent review initially mistook these uncommitted
  additions for prior corpus, then confirmed that the displayed endpoint/exterior assembly has the
  required bounds.
- Searches of Dunster, Slepian--Pollak, and the CCM papers found the component asymptotics but not
  the uniform weighted primitive `(36)` or its continuous-polar consequence `(51)`. This establishes
  no priority claim: the result remains `[NOVELTY UNVERIFIED]`.
- The next mathematical wall is the true cofinal Weil floor. By
  `ccm-rayleigh-transfer-collapses-to-spectral-floor.md`, any vanishing negative-floor allowance
  already proves RH; it is not preliminary spectral engineering.

## Updated gates

- [x] prove the exact `k=1` pole-uniform primitive `(17)` on paper
- [x] prove the all-radial primitive `(11)` on paper
- [x] prove the continuous polar charge `(18)` on paper
- [x] prove the exterior seed law `(32)` on paper
- [ ] formalize the concrete radial-PSWF/Bessel realization and `(51)` unconditionally in Lean
- [ ] prove the true cofinal Weil floor (RH-bearing)
