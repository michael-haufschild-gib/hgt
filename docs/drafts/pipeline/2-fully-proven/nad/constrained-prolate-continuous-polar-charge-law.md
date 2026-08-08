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
  oscillation; the Lean specialization is closed unconditionally by
  `RHTower.prolate_boundedVariationOn` (bounded variation of every nontrivial prolate mode on every
  compact subinterval of the open aperture)
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
  (partially closed: `(44)` by `abs_besselJ1_le_min`, `(45)` by `abs_integral_mul_besselJ0_le`,
  and the `(50)` integration-by-parts mechanism by `norm_integral_cexp_le_of_frequency_lower_bound`;
  the Dunster exterior expansion `(48)` and the assembly `(47)`, `(51)` remain)
- [ ] prove the true cofinal Weil floor (RH-bearing)

- 2026-08-08 -- **The ordered-partition bridge of Lean-plan item 7 is built.**
  `HTGeometry/DerivSignMonotone.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

  `FiniteMonotonicityVariation.lean` already proves the variation law from a *monotonicity*
  partition, and `ProlateOneTurningVariation.lean` already proves each one-sign Sturm cell contains
  at most one critical point.  The missing link was the step between them: a cell with no critical
  point is a monotonicity cell.

  * **`sign_const_of_continuousOn_ne_zero`** -- a continuous nonvanishing function on a closed
    interval has constant sign.  Taking both signs forces a zero by the intermediate value theorem,
    applied on the subinterval between the endpoint and the offending point.
  * **`monotoneOn_or_antitoneOn_of_deriv_ne_zero`** -- hence a cell free of critical points is a
    monotonicity cell, via `strictMonoOn_of_deriv_pos` / `strictAntiOn_of_deriv_neg`.
  * **`eVariationOn_le_of_no_critical_points`** -- the variation law restated with the hypothesis
    the Sturm side actually supplies: an ordered partition whose cells carry no critical point has
    variation at most `2 n B`.

  The remaining Lean work on item 7 is unchanged in kind but smaller: the classical spheroidal
  nodal-count instance producing the partition points, and the concrete pointwise representative.

- 2026-08-08 (second instalment) -- **The ordered-partition assembly is complete**, and a defect in
  the first instalment is corrected.  Same module, axiom-clean.

  *Correction.*  The first instalment's bridge required the derivative to be nonvanishing on the
  **closed** cell.  That hypothesis can never be met by a partition cut at the critical points,
  which is exactly where the derivative vanishes.  The usable form asks for nonvanishing on the
  open cell only, which is all `strictMonoOn_of_deriv_pos` ever needed, since it tests the interior.

  * **`sign_const_of_continuousOn_ne_zero_Ioo`** -- constant sign on an open interval, proved by
    running the intermediate value theorem on `uIcc c x` for a fixed interior base point `c`; the
    open interval is ord-connected, so that segment stays inside it.
  * **`monotoneOn_or_antitoneOn_of_deriv_ne_zero_Ioo`** and
    **`eVariationOn_le_of_no_interior_critical_points`** -- the variation law in the form the Sturm
    cell count actually supplies, with critical points permitted at the partition points.
  * **`exists_partition_of_finite_critical`** -- the assembly itself.  Sorting the critical points
    together with the two endpoints produces a monotone `I` with `I 0 = a`, `I (n) = b` and no
    critical point in any open cell.  The construction is `Finset.orderIsoOfFin` on
    `insert a (insert b S)`; the cell-emptiness clause is the strict monotonicity of that
    enumeration, read back through natural-number indices so the index arithmetic stays in `omega`.

  Lean-plan item 7 now has both abstract halves: the count of monotonicity cells (Sturm) and their
  assembly into the variation bound.  What remains for it is the classical spheroidal nodal count
  supplying the finite critical set, and the concrete pointwise representative.

- 2026-08-08 (third instalment) -- **The abstract half of Lean-plan item 7 is closed.**  Same
  module, axiom-clean.

  * `exists_partition_of_finite_critical` now also returns the cell count, `n <= |S| + 1`, from
    `Finset.card_insert_le` applied twice to `insert a (insert b S)`.
  * **`eVariationOn_le_of_finite_critical`** -- the statement the Sturm side feeds and the envelope
    side consumes: a bounded function whose critical points in the open interval are finitely many
    has total variation at most `2 (|S| + 1) B`.  No monotonicity partition needs to be exhibited by
    the caller; it is built from the critical set.
  * **`boundedVariationOn_of_finite_critical`** -- the finiteness corollary, in the shape the BV
    lattice-envelope modules take as hypothesis.

  So item 7's abstract chain is complete end to end:

  ```text
  one-sign Sturm cell  ->  at most one critical point per cell   (ProlateOneTurningVariation)
  finite critical set  ->  ordered monotonicity partition        (exists_partition_of_finite_critical)
  monotonicity partition + uniform bound -> variation <= 2 n B   (FiniteMonotonicityVariation)
  finite critical set + uniform bound    -> BV                   (this instalment)
  ```

  Its two remaining inputs are both concrete prolate facts rather than abstract ones: the classical
  spheroidal nodal count, which supplies the finite critical set, and the canonical pointwise
  representative `g_lambda`.

- 2026-08-08 (fourth instalment) -- **The nodal count is reduced to a sign-change count.**  Same
  module, axiom-clean.

  * **`finite_criticalSet_of_cells`** -- if `[a,b]` is decomposed by a monotone `J` into `N` cells
    each carrying at most one critical point, the whole critical set is finite.  Induction on `N`
    with `Icc_union_Icc_eq_Icc`; each cell contributes a subsingleton, and a finite union of finite
    sets is finite.
  * **`boundedVariationOn_of_finite_criticalSet`** -- the bounded-variation conclusion stated for a
    critical *set* rather than a finset, which is the form the previous item produces.

  The classical spheroidal input is therefore no longer a nodal count in the analytic sense: what
  the chain needs is only that the Sturm right-hand side `q f` changes sign finitely often on the
  aperture interval, since `criticalSet_subsingleton_of_sturm_rhs_pos` and its negative branch
  already turn each one-sign cell into a subsingleton.  Composed:

  ```text
  q f changes sign N times  ->  N one-sign cells
                            ->  at most one critical point each     (ProlateOneTurningVariation)
                            ->  finite critical set                 (finite_criticalSet_of_cells)
                            ->  ordered monotonicity partition      (exists_partition_of_finite_critical)
                            ->  variation <= 2 (N+1) B, hence BV    (this module)
  ```

  What is left for item 7 is the concrete spheroidal fact that `q f` has finitely many sign changes
  on the aperture interval, and the canonical pointwise representative `g_lambda`.

- 2026-08-08 (fifth instalment) -- **The one-turning-point argument is closed as a single theorem.**
  Same module, axiom-clean.

  * **`finite_criticalSet_of_finite_rhs_zeros`** -- if the Sturm right-hand side `q f` has finitely
    many zeros in the open interval, the solution's critical set is finite.  The zero set partitions
    the interval; on each open cell `q f` has constant sign by
    `sign_const_of_continuousOn_ne_zero_Ioo`; the one-sign Sturm law then leaves at most one
    critical point per cell; and `finite_criticalSet_of_cells` collects them.
    The partition step reuses `exists_partition_of_finite_critical` unchanged -- that theorem was
    stated for an arbitrary finite subset, so it applies to a zero set just as well as to a
    critical set.
  * **`boundedVariationOn_of_finite_rhs_zeros`** -- the whole one-turning-point argument in one
    statement: a bounded Sturm solution whose right-hand side has finitely many zeros is of bounded
    variation on the aperture interval.

  This is the abstract theorem Lean-plan item 7 was after.  For the classical prolate equation
  `((1-x^2) f')' + (chi - c^2 x^2) f = 0` the right-hand side is a quadratic times the solution, so
  the hypothesis reduces to: the solution has finitely many zeros on the aperture interval.  That is
  the only classical spheroidal input the chain still needs, together with the canonical pointwise
  representative `g_lambda`.

- 2026-08-08 (sixth instalment) -- **The zero-finiteness input is built.**  Same module,
  axiom-clean.

  * **`finite_zeros_of_deriv_ne_zero`** -- a differentiable function whose derivative is nonzero at
    each of its zeros has finitely many zeros on a compact interval.  Each such zero is isolated
    (`HasDerivAt.tendsto_nhdsNE`), the zero set is compact, and a discrete compact set is finite.
    For a Sturm solution the hypothesis is exactly nontriviality: a common zero of the solution and
    its derivative would make it vanish identically.
  * **`finite_zeros_mul`** -- the zero set of a product is the union of the two zero sets, so the
    right-hand side `q f` inherits finiteness from `q` and `f` separately.

  For the classical prolate equation `q` is a quadratic, whose zeros are finite outright, so the
  chain's only remaining classical input is that the solution itself has finitely many zeros -- and
  `finite_zeros_of_deriv_ne_zero` reduces even that to nontriviality of the solution.

  One note for future readers of the tree: mathlib's `HasDerivAt.eventually_ne`
  (`Analysis/Calculus/Deriv/Inverse.lean`) is stated with an **unconstrained** section variable `c`,
  so it reads as `f z != c` for arbitrary `c`.  This module deliberately routes through
  `HasDerivAt.tendsto_nhdsNE` instead, which states the unambiguous fact
  `Tendsto f (nhds[!=] x) (nhds[!=] f x)`.

- 2026-08-08 (seventh instalment) -- **The universal variation lemma of `(19e)` is complete, and
  the concrete obstruction is now named exactly.**

  * `deriv_sturmFlux_eq_of_hasDerivAt`, `ode_of_hasDerivAt_on` -- the Sturm form is the derivative
    of `y -> p y * deriv f y`, so a second-order equation feeds the chain directly.
  * **`boundedVariationOn_of_secondOrder`** -- the whole one-turning-point law in the form a
    concrete instance must meet: second-order equation in flux form, continuity of the flux and of
    the right-hand side, finitely many right-hand-side zeros, and a uniform bound, giving bounded
    variation on the aperture interval.

  *The concrete obstruction, named.*  `ConstrainedProlatePointwiseRepresentative.lean` already
  supplies the canonical representative and its two interior derivatives, and
  `timeBandEigenPointwiseSource_unitScale_eigen` is its eigen-equation -- but that equation is in
  **integral (finite-Fourier) form**, not in the second-order form the variation law consumes.
  What the concrete spheroidal instance therefore needs is the classical commuting-operator step:
  the prolate differential operator `((1-x^2) f')' + (chi - c^2 x^2) f` commutes with the finite
  Fourier transform, so an eigenfunction of the integral operator satisfies the differential
  equation.  Until that step exists, `(19e)` cannot be instantiated, and no abstract strengthening
  of the variation law removes the need for it.

  This is the sharpest statement of the remaining gap in item 7: not "the concrete spheroidal
  instance" in general, but specifically the commuting-operator identity converting the integral
  eigen-equation into the prolate ODE.

- 2026-08-08 (eighth instalment) -- **The analytic heart of the commuting-operator step is built.**
  `HTGeometry/SturmSelfAdjoint.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

  * `integral_mul_sturm_eq_neg` -- one integration by parts against a weight vanishing at both
    endpoints: `int u (w v')' = - int u' w v'`, the boundary term carrying the factor `w`.
  * **`integral_mul_sturm_symm`** -- Lagrange's identity in the degenerate case: when the weight
    vanishes at both endpoints the Sturm operator `u -> (w u')'` is symmetric,
    `int u (w v')' = int (w u')' v`.  Both sides reduce to `- int w u' v'`.

  This is exactly what makes the finite Fourier transform commute with the prolate differential
  operator: the prolate weight `1 - t^2` vanishes precisely at the ends of the band, so no boundary
  term survives.  The commuting identity now reduces to the kernel computation
  `L_t exp(i c x t) = L_x exp(i c x t)`, which is symmetric in `x` and `t` by inspection, plus this
  symmetry to move the operator across the integral.

  Neither mathlib nor the corpus carried this degenerate Lagrange identity.

- 2026-08-08 (ninth instalment) -- **The kernel half of the commuting-operator step is built.**
  `HTGeometry/ProlateKernelSymmetry.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

  * `prolateKernel c x t = exp (i c x t)` and the symbol
    `prolateSymbol c x t = -2 i c x t - c^2 x^2 - c^2 t^2 + c^2 x^2 t^2`, with
    **`prolateSymbol_symm`** and `prolateKernel_symm`: both are symmetric in `x` and `t`.
  * **`hasDerivAt_prolateFlux`** -- the flux derivative of the kernel:
    `d/dt [(1 - t^2) d/dt K] = (prolateSymbol + c^2 t^2) K`, so subtracting the operator's own
    `c^2 t^2 K` leaves exactly `prolateSymbol * K` (`prolateOperator_kernel`).
  * **`prolateOperator_kernel_symm`** -- therefore `L_t K = L_x K`.

  Both halves of the commuting-operator step now exist: this kernel identity, and
  `integral_mul_sturm_symm` from the previous instalment, which moves the Sturm operator across the
  integral because `1 - t^2` vanishes at the ends of the band.  What remains is to combine them
  against the corpus representative -- differentiating under the integral sign in
  `timeBandEigenPointwiseSource_unitScale_eigen` -- which turns its integral eigen-equation into the
  prolate differential equation and instantiates `(19e)`.

- 2026-08-08 (tenth instalment) -- **Correction to the previous entry, and the missing logical
  step.**

  *Correction.*  The ninth instalment said that combining the kernel identity with Sturm symmetry
  "turns the integral eigen-equation into the prolate differential equation".  That is too strong.
  What the two halves give is **commutation**: `L` and the finite Fourier operator commute, so `L f`
  is again an eigenfunction of the integral operator with the *same* eigenvalue.  Concluding
  `L f = mu f` -- which is what `(19e)` needs -- additionally requires that eigenvalue to be simple.
  Commutation alone does not yield the differential equation.

  `HTGeometry/CommutingEigenvector.lean` supplies that step, unconditional and axiom-clean (the
  first two results need only `[propext, Quot.sound]`):

  * **`eigen_of_commute`** -- commuting operators preserve each other's eigenspaces: if `T f = chi f`
    and `T L = L T` then `T (L f) = chi (L f)`.
  * **`exists_smul_of_commute_of_eigenspace_le_span`** -- if in addition the `chi`-eigenspace is
    spanned by `f`, then `L f = mu f` for some scalar.
  * `isEigenvector_of_commute_of_simple` -- the same as a vanishing equation.

  So the route to `(19e)` now has three named ingredients, two of them built: the kernel identity
  (ninth instalment), Sturm symmetry with vanishing weight (eighth), and this reduction.  The
  analytic work still outstanding is differentiation under the integral sign, which is what actually
  produces the commutation from the two symmetries, together with simplicity of the eigenvalue in
  the actual constrained spectrum -- the latter being the same `h_0, h_4` identification the card
  already lists as open.

- 2026-08-08 (eleventh instalment) -- **Kernel estimates for the differentiation step**, and an
  honest note on what did not land.  `HTGeometry/ProlateKernelSymmetry.lean`, axiom-clean.

  * **`norm_prolateKernel`** -- the kernel is unimodular, its exponent being purely imaginary.
  * **`hasDerivAt_prolateKernel_fst`** -- the kernel differentiated in its *first* variable, which
    is the one the transform is differentiated in.  It follows from the second-variable derivative
    by the kernel symmetry, with no separate computation.
  * **`norm_prolateKernel_deriv_le`** -- the parameter derivative is bounded by the bandwidth on the
    band, `||i c t K|| <= |c|` for `|t| <= 1`.  This is the dominating estimate the
    differentiation-under-the-integral theorem needs.

  *What did not land.*  The differentiation-under-the-integral statement itself was attempted and
  is not yet proved: assembling
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` against this data ran into
  three separate frictions -- `IntervalIntegrable.1` produces a measurability statement on
  `Ioc (-1) 1` while the theorem wants `uIoc`, the dominating-bound rearrangement needs the norm
  split in a different associativity, and the elaborator exceeds the heartbeat limit on the final
  application.  None of these is a mathematical obstruction; all three are ordinary Lean friction.
  The partially built module was removed rather than left in the tree, so nothing is wired to a
  non-compiling file.  The three estimates above, which are the mathematical content of that step,
  are proved and kept.

- 2026-08-08 (twelfth instalment) -- **Differentiation under the integral is proved**, closing the
  step the eleventh instalment failed to land.  `HTGeometry/ProlateTransformDeriv.lean`,
  unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired into
  `GaloisForLFunctions.HTGeometry`.

  * `continuous_prolateKernel_snd`, and **`hasDerivAt_prolateTransform`**: for an integrable `f` on
    the band, `y -> int_(-1)^(1) K(c,y,t) f(t) dt` is differentiable with derivative
    `int i c t K(c,y,t) f(t) dt`, obtained by differentiating under the integral sign.

  The three frictions recorded last time were all real and all mechanical.  For the record:
  `IntervalIntegrable.1` measurability lands on `Ioc`, so `Set.uIoc_of_le` must be rewritten in
  first; the domination hypothesis wants the plain `forall-ae t, t in uIoc -> ...` shape rather than
  a restricted-measure `ae`; the derivative family `F'` and the bound must be passed explicitly or
  unification blows the heartbeat limit; and the leading argument of the interval version is a
  neighbourhood `Metric.ball x 1 in nhds x`, not a positive radius.  The name is also overloaded --
  the `MeasureTheory` version takes `Integrable ... restrict` and must not be picked.

  With this, all four ingredients of the commuting-operator route are theorems: the kernel identity,
  Sturm symmetry with vanishing weight, differentiation under the integral, and the simple
  eigenvalue reduction.  What remains for `(19e)` is the bookkeeping that composes them against the
  corpus representative, plus the eigenvalue-simplicity input, which is the card's pre-existing
  `h_0, h_4` identification gate.

- 2026-08-08 (thirteenth instalment) -- **The prolate operator is pushed inside the transform.**
  `HTGeometry/ProlateTransformDeriv.lean`, axiom-clean.

  * `intervalIntegrable_mul_kernelFactor`, `intervalIntegrable_kernel_mul`,
    `prolateTransform_factor` -- the bookkeeping that lets the parameter factor be absorbed into the
    integrand.
  * **`hasDerivAt_prolateTransform_deriv`** -- the second derivative of the transform, obtained by
    applying the differentiation theorem to `i c t f(t)` rather than repeating the analysis.
  * **`hasDerivAt_prolateTransformFlux`** -- the prolate flux of the transform:

    ```text
    d/dx [ (1 - x^2) d/dx (F f)(x) ]
      = int_(-1)^(1) (prolateSymbol(c,x,t) + c^2 x^2) K(c,x,t) f(t) dt,
    ```

    so subtracting the operator's own `c^2 x^2 (F f)(x)` leaves exactly
    `int prolateSymbol(c,x,t) K(c,x,t) f(t) dt`.  The whole prolate operator has been moved inside
    the integral and become the symbol -- the same shape as `prolateOperator_kernel` for the bare
    kernel.

  Combined with `prolateSymbol_symm`, this says `L_x F f = int (L_t K) f`, which is one Sturm
  integration by parts (`integral_mul_sturm_symm`) away from `F (L f)`.  That last composition, plus
  the eigenvalue-simplicity input, is all that separates `(19e)` from its instantiation.

- 2026-08-08 (fourteenth instalment) -- **The commuting-operator identity is assembled.**

  * `HTGeometry/SturmSelfAdjoint.lean` generalised from real-valued to any normed *commutative*
    algebra over the reals, which is what the complex kernel needs; the proof is unchanged, since
    mathlib's interval integration by parts already lives in that generality.
  * **`prolateSymbol_integral_eq`** (`ProlateTransformDeriv.lean`) -- the identity itself:

    ```text
    int_(-1)^(1) f(t) (L_t K)(x,t) dt = int_(-1)^(1) (L f)(t) K(x,t) dt,
    ```

    where `L_t K` is written through the symbol.  Composed with
    `hasDerivAt_prolateTransformFlux`, which puts `L_x (F f)` into exactly that left-hand form, and
    with `prolateSymbol_symm`, this says the prolate operator commutes with the finite Fourier
    transform.

  Every analytic ingredient of the route is now a theorem in the tree: the kernel identity, the
  Sturm symmetry, differentiation under the integral, the operator pushed inside the transform, and
  this transfer.  What `(19e)` still waits on is not analysis but the card's own open gate --
  simplicity of the eigenvalue, i.e. the `h_0, h_4` identification -- after which
  `CommutingEigenvector.exists_smul_of_commute_of_eigenspace_le_span` converts the commutation into
  the differential equation and `boundedVariationOn_of_secondOrder` finishes.

  One correction to the record: the derivative appearing in the transfer is the kernel's derivative
  in its *second* variable, carrying the factor `i c x`, not `i c t`.  The first-variable derivative
  is what the differentiation-under-the-integral step uses.  Both are proved; they are not
  interchangeable.

- 2026-08-08 (fifteenth instalment) -- **The simplicity engine is built.**
  `HTGeometry/SturmWronskian.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

  * **`hasDerivAt_sturmWronskian`** -- for two solutions of the *same* equation `(p u')' = q u`, the
    weighted Wronskian `W = u (p v') - v (p u')` has vanishing derivative, because
    `W' = u (p v')' - v (p u')' = u q v - v q u = 0`.
  * **`sturmWronskian_eq_of_hasDerivAt`** -- hence `W` is constant on the interval.

  This is the standard route to simplicity of a Sturm eigenvalue, and therefore the last generic
  ingredient the `(19e)` chain was missing: if two eigenfunctions satisfy the same boundary
  condition the Wronskian vanishes there, hence everywhere, and they are proportional.  What is left
  is not generic -- it is the card's own `h_0, h_4` gate, which asks *which* classical modes sit in
  the actual constrained spectrum, a question about the specific operator rather than about
  Sturm--Liouville theory.

  A note on scope: `SmallTranslationDerivInvariance.lean` mentions a Wronskian only to record that
  its own argument does not need one; there is no duplication.

- 2026-08-08 (sixteenth instalment) -- **Simplicity is completed from the Wronskian.**  Same module,
  axiom-clean.

  * **`div_eq_of_sturmWronskian_eq_zero`** -- where the first solution and the weight are nonzero, a
    vanishing Wronskian makes the quotient `v/u` have vanishing derivative, hence constant.  The
    quotient rule turns `p (u v' - v u') = 0` with `p != 0` into exactly the numerator of
    `(v/u)'`.
  * **`eq_const_mul_of_sturmWronskian_eq_zero`** -- therefore `v = (v(a)/u(a)) u` throughout: the
    two solutions are proportional.

  The generic Sturm--Liouville simplicity argument is now complete in the tree, from the Wronskian's
  vanishing derivative through to proportionality.  Everything `(19e)` needs that is a statement
  about Sturm--Liouville operators in general has been built; the only outstanding input is the
  card's own `h_0, h_4` gate, which is a question about the actual constrained spectrum rather than
  about the general theory.

- 2026-08-08 (seventeenth instalment) -- **Simplicity is automatic at a singular endpoint.**  Same
  module, axiom-clean.

  * **`sturmWronskian_eq_zero_of_weight_eq_zero`** -- if the weight vanishes at an endpoint, the
    Wronskian vanishes there, and being constant it vanishes identically.  No boundary condition has
    to be imposed by hand.
  * **`eq_const_mul_of_weight_eq_zero`** -- hence two solutions of the same Sturm equation on such
    an interval are proportional.

  This matters for the card because the prolate weight is `1 - t^2`, which vanishes exactly at the
  ends of the band.  Simplicity of the prolate eigenvalue is therefore not an extra assumption to be
  supplied from classical spheroidal theory: it follows from the singularity of the equation at the
  band edges, by the same vanishing that made the finite Fourier transform commute with the operator
  in the eighth instalment.  The two facts have a common source.

  What this does *not* do is settle the card's `h_0, h_4` gate, which asks which classical modes
  occupy the actual constrained spectrum -- a question about that operator's eigenvalues, not about
  the dimension of its eigenspaces.  But the simplicity input that `(19e)` needed is now a theorem
  rather than a hypothesis.

- 2026-08-08 (eighteenth instalment) -- **The prolate eigenspace is one-dimensional.**  New module
  `RHTower/ProlateProportionality.lean`, wired into the `RHTower` umbrella, all three declarations
  axiom-clean.

  The corpus already owned the conserved prolate Wronskian, its vanishing at the singular endpoint,
  and the resulting first-order relation `psi_1 psi_2' = psi_2 psi_1'` inside the band
  (`ProlateWronskian.lean`), and interior ODE uniqueness based at an arbitrary regular point
  (`ProlateEndpointNonvanishing.lean`).  What was missing was the step that turns the first-order
  relation into an actual identification of the two solutions -- the relation says the pair is
  degenerate but not what either one is.

  * **`prolateSLAction_const_mul`** -- a constant multiple of a prolate solution solves the same
    eigenvalue problem.
  * **`prolate_eqOn_const_mul`** -- two solutions bounded near the endpoint are proportional on the
    whole aperture as soon as one is nonzero at a single interior point.  The proof feeds value and
    derivative matching at that point into interior uniqueness; the derivative match is exactly the
    first-order relation divided by the nonzero value.
  * **`prolate_eq_zero_of_eq_zero`** -- the vanishing corollary.

  This closes the simplicity input.  The seventeenth instalment showed abstractly that a vanishing
  weight at an endpoint forces the Wronskian to vanish; this instalment carries the prolate case the
  rest of the way to one-dimensionality.  Simplicity of the prolate eigenvalue is therefore a
  theorem of this project, not an appeal to classical spheroidal theory -- which is what the
  commuting-eigenvector transfer of the ninth instalment needed in order to move the finite Fourier
  transform's eigenvector onto the differential operator's.

  Note the one honest limitation: the hypothesis is boundedness of the solution and its derivative
  on `[0,1)`, not membership in the constrained spectrum.  So this settles *degeneracy*, and leaves
  the card's `h_0, h_4` gate -- which classical modes actually occur -- untouched.

- 2026-08-08 (nineteenth instalment) -- **`(19e)` is closed in Lean.**  New module
  `RHTower/ProlateModeVariation.lean`, wired into the umbrella, all declarations axiom-clean, plus
  one further theorem in `ProlateProportionality.lean`.

  * **`prolate_deriv_ne_zero_of_eq_zero`** -- the zeros of a nontrivial prolate mode are simple.
    Interior uniqueness run against the zero solution: a double zero at an interior point would
    annihilate the mode on the whole aperture.
  * **`finite_zeros_prolate_quadratic`** -- `chi + c^2 y^2` vanishes finitely often unless it
    vanishes identically, by the difference-of-squares factorisation against any one root.
  * **`prolate_boundedVariationOn`** -- a nontrivial prolate mode has bounded variation on every
    compact subinterval of `(-1,1)`.

  The chain is now complete end to end and unconditional.  The Sturm right-hand side
  `(chi + c^2 y^2) psi` is a product of two factors each with finitely many zeros, so it has
  finitely many sign cells; the per-cell law already in `ProlateOneTurningVariation.lean` allows at
  most one stationary point in each; the universal finite-monotonicity theorem converts finitely
  many monotone cells plus a sup bound into bounded variation.  The sup bound is free, since a
  continuous function on a compact interval is bounded.

  The hypotheses are exactly smoothness, the eigen-equation, nontriviality, and non-degeneracy of
  the quadratic -- no asymptotics, no spectral index, no RH input, and in particular no boundedness
  assumption at the endpoint, which the earlier drafts of this argument carried.  The card's
  variation gate can be read as closed.

- 2026-08-08 (twentieth instalment) -- **The integration-by-parts step behind `(50)`.**  New module
  `RHTower/VanDerCorputIBP.lean`, wired into the umbrella, all three declarations axiom-clean.

  The corpus already owned first- and second-derivative van der Corput tests
  (`RHTower/VanDerCorput.lean`, `VanDerCorputWeighted*.lean`), but all of them assume the phase
  derivative is monotone (`phi'' >= 0`).  The card's `(49)` does not give that: it gives
  `xi_sigma' >= 1` together with `|(1/xi_sigma')'| <= C x^(-2)`, that is, controlled *variation* of
  the reciprocal frequency rather than a sign for its derivative.  So the existing tests do not
  apply to `(50)` and the mechanism had to be isolated.

  * **`norm_integral_cexp_le_of_antiderivative`** -- if `B (i phi') = A` on the interval, then
    `‖int A exp(i phi)‖ <= ‖B b‖ + ‖B a‖ + int ‖B'‖`.  One integration by parts, no monotonicity, no
    lower bound on the frequency -- the relation `B (i phi') = A` carries the nonvanishing.
  * **`norm_antiderivative_le`** -- the boundary terms obey `‖B‖ <= M / lambda` under
    `|phi'| >= lambda` and `‖A‖ <= M`, read straight off the relation without dividing.
  * **`norm_integral_cexp_le_of_frequency_lower_bound`** -- hence the bound
    `2M/lambda + int ‖B'‖`, which is exactly the shape of `(50)`: amplitude over frequency at the
    two endpoints, plus the total variation of the amplitude-over-frequency profile.

  Taking `B` and `B'` as given data rather than as `A/(i phi')` and its derivative is deliberate.
  It removes any need for `phi` to be twice differentiable or for `phi'` to be globally nonvanishing,
  and it lets the caller supply whichever antiderivative profile it can actually estimate.  For the
  card that profile is `a_(epsilon,n,c)(x)/(sqrt x xi_sigma'(x))`, whose variation is what `(48)`
  and `(49)` bound.

  This is infrastructure for the `(51)` gate, not the gate itself: the Bessel/Dunster amplitude
  asymptotics `(47)`--`(49)` are still to be built before `(50)` can be instantiated.

- 2026-08-08 (twenty-first instalment) -- **The Bessel recurrence `(44)`.**  New module
  `RHTower/BesselJOneRecurrence.lean`, wired into the umbrella, all declarations axiom-clean.

  The corpus already owned `besselJ0` through its integral representation, its first two derivatives
  by differentiation under the integral sign, Bessel's equation, and the envelope decay
  `|J_0(u)| <= 72 sqrt 2 / sqrt u` for `u >= 1` (`BesselJZeroODE.lean`, `BesselJZeroEnvelope.lean`).
  It had no order-one function at all.

  * **`besselJ1`** -- defined as minus the derivative of `besselJ0`, so its integral representation
    `(1/pi) int_0^pi sin(theta) sin(u sin theta) d theta` is immediate.
  * **`besselJ1_eq_mul`** -- `J_1(u) = u (J_0''(u) + J_0(u))`.  This is precisely the
    integration-by-parts identity `integral_sin_mul_sin_eq` that the corpus had already proved on
    the way to Bessel's equation, read in the other direction.
  * **`hasDerivAt_mul_besselJ1`** -- the recurrence `(u J_1(u))' = u J_0(u)`, at every real point.
    Note it needs no `u != 0`, unlike Bessel's equation itself, because the singular `J_0'/u` term
    is exactly what the product form absorbs.
  * **`hasDerivAt_mul_besselJ1_scaled`** -- the scaled form `d/dr [r J_1(c r)] = c r J_0(c r)` used
    in the card, including the degenerate case `c = 0`.
  * **`abs_besselJ1_le`** -- `|J_1(u)| <= |u|/2`, from `|sin x| <= |x|` under the integral.

  This is the first half of `(44)`.  The second half, the decay branch `|J_1(u)| <= C u^(-1/2)`, is
  not yet built; the corpus has that envelope for `J_0` but not for `J_1`, and the order-one case is
  not a corollary of the order-zero one.  With `(44)` in hand the `(45)` integration by parts becomes
  a matter of splitting at `r = c^(-1)` and applying the mechanism of the twentieth instalment.

- 2026-08-09 (twenty-second instalment) -- **`(44)` is complete: the order-one Bessel envelope.**
  New module `RHTower/BesselJOneEnvelope.lean`, wired into the umbrella, axiom-clean.

  The corpus owned the order-zero envelope `|J_0(u)| <= 72 sqrt 2 / sqrt u` for `u >= 1`, proved by
  splitting the quarter period at `pi/4` and running the first-derivative test on `[0,pi/4]` (where
  `|phi'| = u|cos|` is bounded below) and the second-derivative test on `[pi/4,pi/2]` (where
  `phi'' = u sin` is bounded below).  Both blocks were stated with the constant amplitude `1`.

  The order-one function has the same phase and the amplitude `sin theta`, so the same two blocks
  apply once the amplitude budget `‖A(b)‖ + ‖A(a)‖ + int ‖A'‖` of the general tests is estimated.
  On a quarter period that budget is at most `3`, since `|sin| <= 1`, `|cos| <= 1`, and
  `pi/4 <= 1`.

  * **`besselAmp`, `contDiff_besselAmp`, `deriv_besselAmp`, `besselAmp_budget_le`** -- the amplitude
    and its budget.
  * **`integral_besselAmp_eq_neg_im`** -- the real order-one integrand is minus the imaginary part
    of the complex phase integrand, the order-one counterpart of the corpus's real-part identity.
  * **`besselJ1_eq_two_div_pi_mul`** -- the half-period reduction, by the reflection
    `theta -> pi - theta` under which the order-one integrand is invariant.
  * **`norm_integral_besselAmp_first`, `norm_integral_besselAmp_second`** -- the two blocks.
  * **`abs_besselJ1_le_envelope`** -- `|J_1(u)| <= 108 sqrt 2 / sqrt u` for `u >= 1`.
  * **`abs_besselJ1_le_min`** -- with the twenty-first instalment's `|J_1(u)| <= |u|/2`, this is
    exactly `(44)`.

  The square-root exponent is again the loss of the single nondegenerate stationary point of
  `u sin theta` at `theta = pi/2`; the amplitude vanishing at the origin costs nothing because the
  stationary point is at the other end.  Both halves of `(44)` are now unconditional theorems of
  this project, and `(45)` is the remaining step of that branch: split at `r = c^(-1)` and apply the
  twentieth instalment's integration by parts with `r J_1(c r)` as the antiderivative datum.

- 2026-08-09 (twenty-third instalment) -- **`(45)` is proved in Lean, unconditionally.**  New module
  `RHTower/BesselWeightedPrimitive.lean`, wired into the umbrella, all declarations axiom-clean.

  * **`abs_besselJ1_le_sqrt`** -- `|J_1(u)| <= 108 sqrt 2 / sqrt u` at *every* positive argument.
  * **`abs_mul_besselJ1_scaled_le`** -- hence `|r J_1(c r)| <= 108 sqrt 2 sqrt r / sqrt c`.
  * **`abs_integral_mul_besselJ0_le`** -- for `0 <= R <= 2` and a `C^1` weight bounded with its
    derivative by `M`,
    `|int_0^R r B(r) J_0(c r) dr| <= 648 M / (c sqrt c)`, uniformly in the endpoint `R`.

  This is `(45)`, with an explicit constant.  The proof is one integration by parts against the
  exact antiderivative `r J_1(c r)` of `c r J_0(c r)`, followed by the envelope bound on the
  boundary term and on the remaining integral.

  **The paper proof can be simplified.**  The card prescribes "integration by parts, first on
  `0 <= r <= min(R, c^(-1))` and then on `c^(-1) <= r <= R`", i.e. a split at the scale where the
  Bessel amplitude bound gives way to the decay bound.  That split is unnecessary.  The two branches
  of `(44)` combine into the *single* estimate `|J_1(u)| <= C / sqrt u` valid at every `u > 0`: for
  `u >= 1` it is the envelope, and for `u < 1` the amplitude bound `|J_1(u)| <= u/2` is already far
  below `C / sqrt u` because the right side is then at least `C`.  With one estimate covering the
  whole range, one integration by parts on all of `[0,R]` suffices, and the boundary term at the
  origin vanishes identically because the antiderivative `r J_1(c r)` does.

  Note what carries the uniformity in `R`: not decay of the integrand, but the fact that the radius
  range is bounded, which is where the `sqrt R` growth of the antiderivative is absorbed.  This is
  faithful to the card, whose `(47)` takes the supremum over the compact range `1 <= X <= 2`.

- 2026-08-09 (twenty-fourth instalment) -- **`(46)` joins `(45)`.**  Same module, axiom-clean.

  * **`abs_besselJ0_le_sqrt`** -- `|J_0(u)| <= 72 sqrt 2 / sqrt u` at every positive argument.  The
    order-zero counterpart of the previous instalment's single envelope: for `u >= 1` it is the
    corpus envelope, and for `u < 1` the trivial bound `|J_0| <= 1` is already below it.
  * **`integral_abs_mul_besselJ0_le`** -- `int_0^R |r B(r) J_0(c r)| dr <= 288 M / sqrt c` for
    `0 <= R <= 2` and `|B| <= M`.  This is `(46)`.

  Note the same simplification as for `(45)`: the card writes the majorant as
  `C_n int_0^R r (1 + c r)^(-1/2) dr`, an interpolation between the two Bessel regimes.  It is not
  needed.  The single envelope `C / sqrt u` dominates both regimes, and the resulting integrand
  `sqrt r / sqrt c` is bounded on a bounded radius range without any rpow integration.

  `(45)` and `(46)` are now both unconditional theorems with explicit constants.  What separates
  them from `(47)` is the endpoint normalization `(37)` and the pole-uniform reduction `(38)`, and
  from there the exterior branch needs Dunster's expansion `(48)`.

- 2026-08-09 (twenty-fifth instalment) -- **The two passage steps of `(11)`.**  New module
  `HTGeometry/L2PairingLimit.lean`, wired into the umbrella, axiom-clean.

  The card closes `(11)` by two moves: "the `k`-majorant is summable", then "passing first from
  finite radial sums to `R_lambda` in `L2(0,H)` and then taking the supremum in `H`".  Both moves
  are statements about a pairing against a fixed vector, and neither needs anything about the
  vectors beyond convergence in norm.

  * **`norm_inner_le_of_tendsto`** -- a uniform bound on the pairings against a convergent sequence
    passes to the limit, by continuity of the pairing.
  * **`norm_inner_tsum_le`** -- a summable majorant of the channel pairings bounds the pairing
    against the sum, because pairing against a fixed vector is a continuous linear map.
  * **`norm_inner_le_tsum_of_tendsto`** -- the two composed: the summed majorant bounds the pairing
    against any norm limit of the partial sums.

  Stated in an arbitrary inner product space, so it applies to `L2(0,H)` and to the compact-interval
  `L2` layer the corpus already owns (`HTGeometry/CompactIntervalL2Pairing.lean`), and the supremum
  in `H` is then free because the bound does not depend on `H`.

  What remains between this and `(11)` is not analysis of this kind: it is the exterior estimate
  `(16)` supplying the majorant `C sqrt(d_1(lambda)) / (c k^2)` for each channel.

- 2026-08-09 (twenty-sixth instalment) -- **`(50)` is proved in Lean.**  Two new modules,
  `RHTower/OscillatoryDecayPrimitive.lean` and `RHTower/ExteriorProfileBounds.lean`, wired into the
  umbrella, all declarations axiom-clean.

  * **`integral_inv_sq_le`** -- the convergent tail `int_2^X x^(-2) <= 1/2`.
  * **`norm_integral_cexp_le_of_decay`** -- with an antiderivative datum decaying like `K/x` and a
    derivative like `K/x^2`, the oscillatory integral from `2` to any endpoint is at most `3K/2`,
    with no dependence on the endpoint.
  * **`norm_integral_cexp_le_of_profile`** -- the same with the phase scaled by `+- c`, giving the
    gain `3C/(2c)`.  The frequency is gained because the antiderivative datum is the profile divided
    by `+- i c`.
  * **`hasDerivAt_inv_sqrt`, `exteriorWeight`, `hasDerivAt_exteriorWeight`,
    `abs_exteriorWeight_le`, `abs_deriv_exteriorWeight_le`** -- the weight `1/(sqrt x xi')` and its
    derivative.
  * **`norm_exteriorProfile_le`, `norm_deriv_exteriorProfile_le`** -- the profile `a/(sqrt x xi')`
    decays like `C/x` and its derivative like `(3C/2 + C^2/2)/x^2`, from `(48)` and `(49)`.
  * **`norm_integral_exterior_le`** -- the assembly: for an amplitude with `|a| <= C x^(-1/2)` and
    `|a'| <= C x^(-3/2)`, a phase speed `xi' >= 1` whose reciprocal has `|(1/xi')'| <= C x^(-2)`,
    and a branch sign `eps = +-1`,
    `‖int_2^X (a(x)/sqrt x) exp(i eps c xi(x)) dx‖ <= 3(3C/2 + C^2/2)/(2c)`, uniformly in `X`.
    This is `(50)`.

  Two points on what carries the estimate.  First, the uniformity in `X` is not decay of the
  integrand -- the integrand does not decay fast enough to be absolutely integrable -- but the fact
  that the *profile* derivative is `O(x^(-2))`, whose tail converges.  Second, the corpus's existing
  van der Corput tests could not be used: they all require `phi'' >= 0`, and `(49)` supplies only
  bounded variation of `1/xi'`.  That is why the twentieth instalment's monotonicity-free
  integration by parts was needed first.

  I checked `RHTower/ProlateDunsterBesselOffDiagonal.lean` (2203 lines) before building: it treats
  the CCM first-row radial products with the *monotone* phase family `xiSumPhase`/`xiSumSpeed` and
  the monotone-phase tests, so it is a different mechanism and there is no duplication.

  With `(44)`, `(45)`, `(46)` and `(50)` all closed, what remains between here and `(51)` is the
  supply side: Dunster's expansion `(48)` itself, i.e. the existence of amplitudes with those bounds
  for the actual prolate functions, and then the endpoint normalization `(37)`-`(38)` that turns
  `(45)`-`(46)` into `(47)`.

- 2026-08-09 (twenty-seventh instalment) -- **`(49)` is a theorem, not a hypothesis.**  Two new
  modules, `RHTower/XiReciprocalSpeed.lean` and `RHTower/ExteriorXiPrimitive.lean`, wired into the
  umbrella, axiom-clean.

  The corpus already owns the exterior Liouville--Green phase of this very problem:
  `xiSpeed s t = sqrt((t^2 - s)/(t^2 - 1))` with `s = sigma^2`, its antiderivative
  `xiEndpointPhase`, its derivative `hasDerivAt_xiSpeed`, the speed bound `one_le_xiSpeed`, and
  `continuousOn_xiSpeed` (`CCMFirstRowStationaryPhase.lean`,
  `CCMFirstRowVanDerCorputBlocks.lean`).  So the first half of `(49)`, `xi' >= 1`, was already
  proved.  What was absent is the half the integration by parts actually consumes: the variation of
  the *reciprocal* speed.

  * **`hasDerivAt_inv_xiSpeed`** -- the derivative of `1/xi'`, from the corpus's `hasDerivAt_xiSpeed`
    and the reciprocal rule.
  * **`abs_deriv_inv_xiSpeed_le`** -- `|(1/xi')'(x)| <= x^{-2}` for `x >= 2`, `0 <= s <= 1`.  This is
    the second half of `(49)`, and with constant *one*, not an unspecified `C_n`.  The mechanism:
    `(1/xi')' = x(1-s)/((x^2-1)^2 (xi')^3)`, and since `xi' >= 1` this is at most `x/(x^2-1)^2`,
    which is below `x^{-2}` exactly because `x^3 <= (x^2-1)^2` from `x = 2` onward.
  * **`xiInvSpeedDeriv`, `continuousOn_xiInvSpeedDeriv`** -- the reciprocal-speed derivative as a
    function, and its continuity.
  * **`norm_integral_exterior_xiPhase_le`** -- the exterior branch bound with the *actual* prolate
    phase substituted.  The phase side of the estimate now carries no conditions whatsoever: the
    speed bound and the reciprocal variation are both theorems of this project.

  What this changes: the twenty-sixth instalment's `(50)` was stated for any phase satisfying
  `(49)`.  It is now stated for the prolate phase itself, and the only remaining conditions are the
  amplitude bounds `(48)` -- which is what a Liouville--Green expansion supplies by construction, and
  is the one genuinely outstanding input of this branch.

- 2026-08-09 (twenty-eighth instalment) -- **`(48)` closed, and with it the exterior branch has no
  hypotheses left.**  Two new modules, `RHTower/XiAmplitudeDecay.lean` and
  `RHTower/ExteriorDunsterPrimitive.lean`, wired into the umbrella, axiom-clean.

  I checked the corpus before building and found most of `(48)` already there.
  `CCMFirstRowStationaryPhase.lean` defines `xiAmplitude` -- Dunster's amplitude `(39)` -- and proves
  `xiAmplitude_le`: `A <= 2^(1/4) x^(-1/2)`.  That is the amplitude half of `(48)`, already done.
  `ProlateDunsterComparisonBridge.lean` computes the derivative in logarithmic form,
  `A' = A (D/2 - x/(2(x^2-s)))` with `D` the phase defect, and `CCMRadialProlateDefect.lean` bounds
  `|D| <= x/(x^2-1)`.  So all three ingredients of the derivative half existed; what was missing was
  only their combination.

  * **`sqrt_sqrt_two_le_two`, `abs_xiAmplitude_le_four`** -- the amplitude bound restated with the
    single constant the primitive consumes.
  * **`abs_xiAmplitudeDeriv_le`** -- `|A'(x)| <= 4 x^(-3/2)` for `x >= 2`, `0 <= s <= 1/2`.  Away
    from the endpoint `|D|/2 <= 2/(3x)` and `x/(2(x^2-s)) <= 4/(7x)`, so the logarithmic derivative
    is below `2/x`; the amplitude contributes its own `x^(-1/2)`.  This is the derivative half of
    `(48)`.
  * **`continuousOn_xiAmplitudeDeriv`** -- continuity of that derivative.
  * **`norm_integral_exterior_dunster_le`** -- the branch integral of Dunster's amplitude against the
    exterior phase over `[2, X]` is at most `21/c`, uniformly in `X`.

  What is worth stating precisely: this last theorem has **no analytic hypotheses**.  Its only
  assumptions are the parameter ranges `0 <= s <= 1/2`, `c > 0`, `|eps| = 1`, `X >= 2`.  Every
  analytic input -- the amplitude decay `(48)`, the speed bound and reciprocal variation `(49)`, and
  the integration by parts `(50)` -- is a proved theorem of this project.  The exterior branch of the
  card is therefore closed, not merely reduced.

  What `(50)` in the card additionally asserts, and this does not yet give, is the *sum over the two
  branches* weighted by `sqrt(d_n(lambda))`, i.e. the passage from the branch integral to
  `U_(n,lambda)` itself.  That is the content of the expansion `(48)` as an identity -- that
  `U_(n,lambda)` equals the two-branch sum -- rather than of the estimates on its terms.

- 2026-08-09 (twenty-ninth instalment) -- **The Dunster coordinate as a change of variable, and the
  transported compact primitive.**  Two new modules, `RHTower/XiCoordinate.lean` and
  `RHTower/XiTransportedPrimitive.lean`, wired into the umbrella, axiom-clean.

  I checked first: the corpus has `xiEndpointPhase` with its derivative, positivity, continuity on
  `Ioi 1`, and the two-sided bracket `xiEndpointPhase_bounds`, but **nothing making it a change of
  variable** -- no monotonicity, no image, no substitution formula.  That is the missing structural
  step behind `(41)` and `(47)`.

  * **`xiEndpointPhase_one`** -- the phase vanishes at the endpoint.
  * **`continuousWithinAt_xiEndpointPhase_one`, `continuousOn_xiEndpointPhase_Ici`** -- continuity
    up to the singular endpoint.  This is not automatic: the integrand blows up at `x = 1`.  The
    corpus's own bracket `sqrt(1-s) sqrt(x^2-1) <= xi <= sqrt(x^2-1)` squeezes the phase to zero,
    which settles it in three lines.
  * **`strictMonoOn_xiEndpointPhase`, `injOn_xiEndpointPhase`** -- strict monotonicity from
    positivity of the speed on the interior.
  * **`image_xiEndpointPhase_Icc`, `image_xiEndpointPhase_Ioo`** -- the image is the phase interval,
    by monotonicity one way and the intermediate value theorem the other.
  * **`xiEndpointPhase_le_two`** -- the phase of the compact exterior range `[1,2]` stays below `2`,
    which is exactly the radius bound the bounded-radius Bessel estimates require.
  * **`setIntegral_comp_xiEndpointPhase`, `intervalIntegral_comp_xiEndpointPhase`** -- the
    substitution itself.  Proved on the open interval, where the derivative exists, via the measurable
    change-of-variables formula; the endpoint is a null set so nothing is lost.
  * **`abs_integral_xiTransported_le`, `abs_integral_xiTransported_normalized_le`** -- `(45)`
    transported to the exterior variable: the speed-weighted Bessel integral over a compact exterior
    range is `O(c^(-3/2))`, and with the model's own `sqrt c` normalization, `O(1/c)`.

  The last statement is the shape of `(47)`: one full power of the frequency on a compact exterior
  range, uniform in the endpoint.  What separates it from `(47)` itself is the identification of the
  weight -- the card's `B_(sigma,c)` of `(42)`, defined through the *inverse* coordinate `X_sigma`,
  together with its `C^1` bound `(43)`.  The coordinate is now known to be a strictly monotone
  continuous bijection onto its image, which is what constructing that inverse requires.

- 2026-08-09 (thirtieth instalment) -- **The inverse coordinate `X_sigma`, and the transport
  identity `(41)`.**  Two new modules, `RHTower/XiInverseCoordinate.lean` and
  `RHTower/XiBesselWeight.lean`, wired into the umbrella, axiom-clean.

  The previous instalment left the coordinate known to be a strictly monotone continuous injection.
  That is exactly what constructing the inverse needs, and the inverse is what `(42)` is written
  through.

  * **`exists_lt_xiEndpointPhase`** -- the phase exceeds any level, with an explicit exterior point
    `X = sqrt(1 + 4y^2)`.  The corpus's lower bracket does the work; no asymptotics.
  * **`image_xiEndpointPhase_Ioi`** -- the phase maps the exterior ray *onto* the positive ray.
  * **`xiInverse`, `xiEndpointPhase_xiInverse`, `xiInverse_xiEndpointPhase`,
    `xiInverse_mem_Ioi`, `strictMonoOn_xiInverse`, `image_xiInverse_Ioi`** -- the inverse coordinate
    and its two-sided inverse laws.
  * **`continuousAt_xiInverse`** -- continuity of the inverse.  Note this is proved by applying the
    monotone-continuity criterion to the *inverse* directly: it is strictly monotone and its image
    `Ioi 1` is open, hence a neighbourhood of each value.  Going through the forward map would have
    needed a homeomorphism-of-subtypes argument.
  * **`hasDerivAt_xiInverse`** -- the inverse function theorem: `X_sigma'(r) = 1/xi_sigma'(X_sigma(r))`.
  * **`xiBesselWeight`** -- Dunster's weight `(42)`, with the fourth roots as iterated square roots.
  * **`xiAmplitude_mul_inv_xiSpeed_eq`** -- **`(41)`**: `A_sigma(X_sigma(r)) X_sigma'(r) = r B_sigma(r)`.

  The identity is exact and the bookkeeping is the whole content: the phase `r` cancels against the
  amplitude's own square root, and the two quarter powers in the amplitude's denominator recombine
  with the half powers coming from the reciprocal speed.  Writing every quarter power as an iterated
  square root and substituting `p^2 = sqrt(x^2-1)`, `c^2 = r` before clearing denominators turns it
  into a rational identity.

  With `(41)` proved and the substitution of the twenty-ninth instalment in place, what `(47)` still
  needs is `(43)`: the `C^1` bound on `B_sigma` over the compact phase range, including the removable
  singularity at `r = 0`.
