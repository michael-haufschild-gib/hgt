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
6. `[FORMALIZED]` a concrete radial-PSWF
   endpoint/exterior interface proving the all-radial primitive `(11)`.  Unconditional Lean
   theorems: `(43)`, `(47)`, `(50)`; the exact two-branch representation of the mode itself
   (`RHTower.sqrt_mul_radialProlate_dilate_eq_branches`, an identity, no error term); `(16)` for
   every `k >= 1` over the full range `[L, X]` for the **exact** mode
   (`RHTower.norm_integral_radialProlate_dilate_left_le`,
   `<= 4500 M/(sqrt c (c k^2) L)` with `M` free of `k` and of the endpoint); `(17)`
   (`RHTower.abs_integral_sqrt_mul_radialProlate_full_le`); and the assembled
   **`(11)`** itself (`RHTower.tsum_norm_integral_radialProlate_all_channels_le`), uniform in the
   endpoint of integration;
7. `[(19e) FORMALIZED FOR ANY NONTRIVIAL MODE; SPECTRAL IDENTIFICATION OPEN]`
   identify the classical real `h_0,h_4` modes in the actual operator spectrum and prove the
   concrete fixed-mode variation bound `(19e)`.  The variation bound itself is now an
   unconditional theorem for *every* nontrivial solution of the prolate eigen-equation
   (`RHTower.prolate_boundedVariationOn_of_nontrivial`); what is open is only the identification of
   `h_0, h_4` in the spectrum;
8. the constrained-source and critical-Mellin specialization `(18)`--`(32)`.

Item 7's variation content is complete.  `HTGeometry/FiniteMonotonicityVariation.lean` gives the
`n`-cell law, `RHTower/ProlateOneTurningVariation.lean` the prolate flux equation and the sign-cell
critical-point laws, `HTGeometry/DarbouxMonotoneCell.lean` the ordered partition assembly and the
Darboux monotonicity step, `HTGeometry/GronwallUniqueness.lean` the uniqueness that makes zeros
simple, `HTGeometry/IsolatedZeroFinite.lean` the isolation-to-finiteness step, and
`RHTower/ProlateSturmVariation.lean` the assembled bound
`RHTower.prolate_boundedVariationOn_of_nontrivial`.

The classical spheroidal nodal count is **not** needed: Gronwall uniqueness supplies the finiteness
of the zero set directly, without any spheroidal asymptotics.  What remains of item 7 is the
spectral identification of `h_0, h_4` and the concrete representative.

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

The *mechanism* of that identification is now formalized.
`RHTower.prolateAction_bandTransform_commutes` proves that the finite Fourier transform commutes
with the prolate differential operator on the band, from the kernel identity, the two
differentiations under the integral, and the symmetry of the operator where `1 - t^2` vanishes at
both endpoints.  An eigenfunction of the band transform therefore satisfies the prolate
eigen-equation up to regularity, and `RHTower.prolate_boundedVariationOn_of_nontrivial` then
applies.  What is left is the regularity of the specific representative, not the mechanism.
After that identification, the fixed-mode
regularity law

```text
Var(g_lambda^+)=O(1),                                          (19e)
```

is **formalized**, for every nontrivial solution of the prolate eigen-equation and not only for the
classical modes: `RHTower.prolate_boundedVariationOn_of_nontrivial`.  The one-turning-point Sturm
argument `(19f)`--`(19g)` is in Lean, and the spheroidal nodal count it was thought to need is not
needed at all -- Gronwall uniqueness gives the finiteness of the zero set directly.  The bound is
then substituted into the already formalized BV envelope and clipped critical-Mellin pairing.  This
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
- [x] identify a live pair in the actual spectrum and inhabit the two-mode constrained source:
  `RHTower.eventually_exists_twoModeConstrainedRealSource` builds it from the first two signed
  modes, which are simultaneously live at every large aperture
  (`eventually_evenProlateSignedValue_ne_zero_pair`), and
  `eventually_exists_tendsto_poissonMuntzAbelSum_radialFullLogSource` runs the Abel boundary law on
  it.  The two *degree-labelled* asymptotic inputs -- `d_0/d_1 = O(lambda^-8)` and the Hermite
  limits of `chi_n` -- are classical PSWF asymptotics and stay cited; nothing in the construction,
  the envelope, `(4)`, `(19a)`--`(19d)` or `(19e)` uses them.  Constrained contrast,
  real extraction, symmetric-Lebesgue regularity, and source-specific identity `(19a)` are already
  formalized for every nonzero eigenmode pair.  The *mechanism* is now closed:
  `RHTower.prolateAction_bandTransform_commutes` (the transform commutes with the prolate operator
  on the band), `RHTower.hasDerivAt_bandEigen` (a band eigenfunction is automatically twice
  differentiable), and `RHTower.prolate_eq_const_mul_of_same_eigenvalue` (prolate eigenvalues are
  simple, by the vanishing Wronskian and Gronwall).  What is left is exhibiting the two classical
  modes, not proving that they are determined
- [x] prove the fixed-mode source variation bound `(19e)` on paper by one-turning-point Sturm
  oscillation; the Lean specialization is closed unconditionally by
  `RHTower.prolate_boundedVariationOn` (bounded variation of every nontrivial prolate mode on every
  compact subinterval of the open aperture)
- [ ] promote `(18)` and `(32)` after the primitive and source-regularity audits
- [x] formalize the concrete radial-PSWF primitive theorem and its polar consequence in Lean:
  `RHTower.norm_integral_radialProlate_dilate_left_le` is `(16)` for the exact mode over the full
  channel range, `RHTower.tsum_norm_integral_radialProlate_all_channels_le` is `(11)`, and
  `RHTower.abs_polarCharge_radialLimit_le` is the polar consequence, uniform in the endpoint
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

- [x] prove the exact `k=1` pole-uniform primitive `(17)` on paper; **`(17)` is now closed in Lean
  unconditionally for the exact radial mode** by
  `RHTower.abs_integral_sqrt_mul_radialProlate_full_le` (endpoint interval by an energy/Gronwall
  bound, exterior by the Dunster transfer against `(47)`)
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

- 2026-08-09 (thirty-first instalment) -- **The removable singularity of `(42)` is removable
  quantitatively, and Dunster's expansion `(40)` is not needed for it.**  New module
  `RHTower/XiBesselWeightBounds.lean`, wired into the umbrella, axiom-clean.

  * **`xiBesselWeight_le_two`** -- `B_sigma(r) <= 2` for every `r > 0`, with no upper restriction on
    the range.
  * **`inv_le_xiBesselWeight`, `inv_le_xiBesselWeight_of_le`** -- `B_sigma(r) >= 1/(2 sqrt 2)` on the
    compact phase range `r <= xi_sigma(2)`.

  Both bounds hold right up to the endpoint, which is the point.  The weight
  `B = (x^2-1)^(1/4) / (r^(1/2) (x^2-s)^(3/4))` looks singular at `r = 0`: numerator and `r` vanish
  together.  The card removes the singularity through `(40)`, the analytic expansion of the endpoint
  coordinate `eta = 2(1-sigma^2)(x-1) + O((x-1)^2)`.

  **That expansion is not needed.**  The corpus's own two-sided bracket
  `sqrt(1-s) sqrt(x^2-1) <= xi_s(x) <= sqrt(x^2-1)` already pins the phase to the square root of
  `x^2-1` within a bounded factor, and taking a further square root pins `r^(1/2)` to
  `(x^2-1)^(1/4)` within a bounded factor.  So the numerator's quarter root cancels against
  `r^(1/2)` exactly, in both directions: the lower half of the bracket gives the upper bound on `B`
  and the upper half gives the lower bound.  No expansion, no analyticity, absolute constants.

  This is the `C^0` half of `(43)`.  What remains of `(43)` is the derivative bound, which needs the
  derivative of `B` through the inverse coordinate -- available now that
  `hasDerivAt_xiInverse` is proved, but requiring a second-order control of the phase near the
  endpoint that the bracket alone does not supply.

- 2026-08-09 (thirty-second instalment) -- **The endpoint atom, and a precise statement of what the
  derivative half of `(43)` needs.**  New module
  `HTGeometry/InverseSqrtEndpointIntegral.lean`, wired into the umbrella, axiom-clean.

  * **`rpow_neg_half_eq_inv_sqrt`, `hasDerivAt_two_mul_sqrt_sub_one`,
    `integral_rpow_neg_half_sub_one`** -- `int_1^x (t-1)^(-1/2) dt = 2 sqrt(x-1)`.  The corpus had
    integrability of this weight (`intervalIntegrable_rpow_sub_one`) but not its value.  The
    fundamental theorem is applied in the form needing the derivative only on the open interval,
    since at the endpoint there is none.

  **Why this is the next atom, and what is still missing.**  Writing
  `xi_s(x) = int_1^x g(t) (t-1)^(-1/2) dt` with `g(t) = sqrt(t^2-s)/sqrt(t+1)` smooth and
  `g(1) = sqrt(1-s)/sqrt 2`, this integral gives the leading term `2 g(1) sqrt(x-1)`.

  The derivative half of `(43)` needs exactly that refinement, and here is why the `C^0` argument of
  the thirty-first instalment does not extend.  The logarithmic derivative is

  `B'/B = x/(2 sqrt(u) sqrt(v)) - 1/(2r) - 3 x sqrt(u)/(2 v sqrt(v))`,   `u = x^2-1`, `v = x^2-s`.

  The third term is harmless.  The first two each blow up like `C/sqrt(u)` as `r -> 0`, and their
  difference is bounded *only because their leading constants agree exactly*: the bracket gives
  `r` between `sqrt(1-s) sqrt(u)` and `sqrt(u)`, which is a bounded factor and therefore enough for
  a bound on `B` itself, but not enough for a bound on a difference of two divergent terms.  What is
  needed is the next order, `xi_s(x) = sqrt(1-s) sqrt(x^2-1) (1 + O(x-1))` -- equivalently `(40)`.

  So the thirty-first instalment's finding is sharp: the bracket suffices for `C^0` and provably
  cannot suffice for `C^1`.  The endpoint atom built here is the first step of the `C^1` route, and
  the remaining step is the Lipschitz correction `|xi_s(x) - 2 g(1) sqrt(x-1)| <= C (x-1)^(3/2)`.

- 2026-08-09 (thirty-third instalment) -- **`(40)` is proved: the second-order endpoint expansion of
  the phase.**  New module `RHTower/XiEndpointExpansion.lean`, wired into the umbrella, axiom-clean.

  * **`xiEndpointFactor`, `xiSpeed_eq_factor_div`** -- the exact factorisation
    `xi_s'(t) = g_s(t) (t-1)^(-1/2)` with `g_s(t) = sqrt(t^2-s)/sqrt(t+1)` smooth at the endpoint.
  * **`abs_xiEndpointFactor_sub_le`** -- `|g_s(t) - g_s(1)| <= 3(t-1)`, for every `t >= 1`.  The
    mechanism is that the *square* of `g_s` is a rational function vanishing to first order at the
    endpoint, `g_s(t)^2 - g_s(1)^2 = (t-1)(2t+1+s)/(2(t+1))`, and `g_s` is bounded below by `1/2`
    there, so the difference of squares converts to a difference with an absolute constant.  No
    derivative of `g_s` is ever computed.
  * **`integral_inv_sqrt_sub_one`, `intervalIntegrable_inv_sqrt_sub_one`, `integral_sqrt_sub_one`**
    -- the two endpoint weights in square-root form, `int_1^x (t-1)^(-1/2) = 2 sqrt(x-1)` and
    `int_1^x (t-1)^(1/2) = (2/3)(x-1)^(3/2)`.
  * **`abs_xiEndpointPhase_sub_leading_le`** -- **the expansion**:

    `|xi_s(x) - 2 g_s(1) sqrt(x-1)| <= 2 (x-1)^(3/2)`   for `0 <= s <= 1/2`, `x >= 1`.

  This is `(40)` in the form the card needs, with an explicit constant and no appeal to analyticity
  of the endpoint coordinate.  The proof is one line of algebra once the pieces are in place: the
  phase minus its leading term is the integral of `(g_s(t) - g_s(1)) (t-1)^(-1/2)`, whose modulus is
  at most `3 (t-1)^(1/2)`, and that integrates to `2(x-1)^(3/2)`.

  The thirty-second instalment identified this as exactly the missing input for the derivative half
  of `(43)`.  It is now available.

- 2026-08-09 (thirty-fourth instalment) -- **The endpoint cancellation, quantitatively.**  New module
  `RHTower/XiEndpointCancellation.lean`, wired into the umbrella, axiom-clean.

  * **`two_xiEndpointFactor_one_eq`** -- `2 g_s(1) = sqrt(2(1-s))`, unconditionally in `s`.
  * **`abs_sqrt_prod_sub_le`** -- `|sqrt((x+1)(x^2-s)) - sqrt(2(1-s))| <= 10(x-1)` on `[1,2]`, again
    by the difference of squares: the polynomial `(x+1)(x^2-s) - 2(1-s)` factors as
    `(x-1)(x^2+2x+2-s)`, and the sum of the roots is at least `1`.
  * **`abs_mul_xiEndpointPhase_sub_sqrt_le`** -- the cancellation numerator:
    `|x xi_s(x) - sqrt(x^2-1) sqrt(x^2-s)| <= 16 (x-1)^(3/2)`.
  * **`abs_endpoint_logDeriv_diff_le`** -- **the payoff**:

    `| x/(2 sqrt(x^2-1) sqrt(x^2-s)) - 1/(2 xi_s(x)) | <= 8 sqrt(x-1)`  on `(1,2]`.

  The two terms on the left each blow up like `(x-1)^(-1/2)`.  Their difference is not merely
  bounded -- it *vanishes* at the endpoint, at rate `(x-1)^(1/2)`.  That is one full power better
  than either term, and it is what the thirty-second instalment identified as the missing ingredient.

  The mechanism, stated plainly: over a common denominator the difference is
  `(x xi_s - sqrt(x^2-1) sqrt(x^2-s)) / (2 xi_s sqrt(x^2-1) sqrt(x^2-s))`.  The expansion `(40)`
  makes the numerator `O((x-1)^(3/2))` while the bracket makes the denominator at least `2(x-1)`.
  Neither bound alone suffices; it is their combination that produces the extra half power.

  This closes the analytic obstruction to the derivative half of `(43)`.  What is left there is
  mechanical: differentiate `B_sigma` through `hasDerivAt_xiInverse` and the quotient rule, and read
  off the bound from this estimate together with the already-proved boundedness of the third term.

- 2026-08-09 (thirty-fifth instalment) -- **The weight is differentiable, and its logarithmic
  derivative is bounded.**  New module `RHTower/XiBesselWeightDeriv.lean` plus two theorems in
  `XiEndpointCancellation.lean`; wired, axiom-clean.

  * **`hasDerivAt_xiAmplitude_comp`, `hasDerivAt_xiSpeed_comp`** -- the amplitude and the speed at
    the inverse coordinate, differentiated by the chain rule against `hasDerivAt_xiInverse`.
  * **`xiBesselWeight_eq_quotient`** -- the weight in the quotient form
    `B_s(r) = A_s(X_s(r)) / (xi_s'(X_s(r)) r)`, which is the transport identity `(41)` rearranged.
  * **`hasDerivAt_xiBesselWeight`** -- **the weight is differentiable on the positive ray**, with an
    explicit derivative.  The quotient form is what makes this reachable: in its original fourth-root
    form the weight's derivative is not accessible, but as a quotient of three functions with known
    derivatives it is just the quotient rule.
  * **`abs_endpoint_logDeriv_regular_le`** -- the regular term `3x sqrt(u)/(2 v sqrt(v))` is at most
    `24` on the compact range.
  * **`abs_besselWeight_logDeriv_le`** -- **the logarithmic derivative of the weight is bounded by
    `32`** on `(1,2]`.

  A correction worth recording, because it cost a false start.  Expanding `B'/B` through the
  quotient form gives
  `A'/(A xi') - xi''/xi'^2 - 1/r`, and the term `xi''/xi'^2 = x(s-1)/(sqrt(u) v^(3/2))` *looks*
  divergent, which suggested the quotient route could not work.  It is not divergent in combination:
  multiplying the discrepancy by `sqrt(u) v^(3/2)/x` gives `-v + u + (1-s) = 0` identically, so the
  quotient form and the direct form
  `B'/B = x/(2 sqrt(u) sqrt(v)) - 1/(2 xi) - 3x sqrt(u)/(2 v sqrt(v))`
  agree exactly.  The apparent extra singularity is an artefact of splitting the logarithmic
  derivative at the wrong place; `-log xi'` carries a `+x/(2u)` that flips the sign of the term the
  cancellation acts on.

  What remains for the derivative half of `(43)` is now a single identity: that the explicit
  derivative produced by `hasDerivAt_xiBesselWeight` equals `B_s(r)` times the bracket bounded here.
  Both sides are known; the step is algebraic, not analytic.

- 2026-08-09 (thirty-sixth instalment) -- **`(43)` is complete.**  Two theorems added to
  `RHTower/XiBesselWeightDeriv.lean`; wired, axiom-clean.

  * **`xiBesselWeightDeriv_eq_mul`** -- the identity: the explicit derivative produced by
    `hasDerivAt_xiBesselWeight` equals `B_sigma(r)` times the bracket
    `x/(2 sqrt(u) sqrt(v)) - 1/(2r) - 3x sqrt(u)/(2 v sqrt(v))`.  After substituting
    `a = sqrt(x^2-1)`, `b = sqrt(x^2-s)` the whole thing is rational, and the single relation it
    needs is `a^2 - b^2 = s - 1`.
  * **`abs_xiBesselWeightDeriv_le`** -- `|B_sigma'(r)| <= 64` on the compact phase range.

  So `(43)` now holds in both halves, with absolute constants:
  `1/(2 sqrt 2) <= B_sigma <= 2` and `|B_sigma'| <= 64`.

  **The remaining obstruction to `(47)` is structural, not analytic, and is worth naming precisely.**
  The transported primitive `abs_integral_xiTransported_le` inherits from `(45)` the requirement that
  the weight be differentiable on the *closed* phase interval `[0, xi_sigma(X)]`, because mathlib's
  integration by parts is stated with derivatives on the closed interval.  But `B_sigma` is
  differentiable only on the open ray: at `r = 0` the inverse coordinate `X_sigma` is outside its
  domain and `xiBesselWeight` takes a junk value there.

  Two routes, both real work and neither an analytic gap:
  (i) restate `(45)` with the derivative on the open interval only, via the same
  `integral_eq_sub_of_hasDeriv_right_of_le` pattern already used three times on this card, which
  needs the product `B(r) r J_1(cr)` to be continuous up to `r = 0` -- true on the nose, since
  `r J_1(cr) -> 0` and `B` is bounded;
  (ii) prove the bound on `[delta, xi_sigma(X)]` uniformly in `delta` and pass to the limit.

  Route (i) is the better one: the boundary term at the endpoint vanishes identically because
  `r J_1(c r)` does, so no limit argument is needed at all.

- 2026-08-09 (thirty-seventh instalment) -- **Route (i) is built: integration by parts with interior
  derivatives.**  New module `HTGeometry/InteriorIntegrationByParts.lean`, wired into the umbrella,
  axiom-clean.

  * **`intervalIntegrable_of_continuousOn_Ioo_of_bounded`** -- continuous and bounded on the *open*
    interval is enough for interval integrability; the endpoints carry no measure.
  * **`integral_mul_deriv_eq_deriv_mul_interior`** -- integration by parts requiring derivatives only
    on the interior, and continuity only of the *product* up to the endpoints.  The fundamental
    theorem in its one-sided form already covers this; mathlib's integration by parts happens to be
    stated with derivatives on the closed interval, which is what blocked `(47)`.
  * **`continuousWithinAt_mul_of_bounded_of_tendsto_zero`** -- the degenerate-endpoint continuity: a
    bounded factor against a factor vanishing at the endpoint is continuous there, whatever value the
    bounded factor takes -- indeed whether or not it has one.

  That last lemma is the point of the whole detour.  The weight `B_sigma` has no meaningful value at
  `r = 0`: the inverse coordinate `X_sigma` is undefined there, so `xiBesselWeight` returns a junk
  value.  But the product being differentiated in `(45)` is `B_sigma(r) r J_1(c r)`, and
  `r J_1(c r)` vanishes at `r = 0`, so the product is continuous at the endpoint regardless.  The
  junk value never enters, and no limit argument is needed.

  This is general infrastructure, stated for arbitrary functions, and it is the exact shape the
  thirty-sixth instalment identified as needed.  What remains is to re-derive `(45)` against it and
  substitute `B_sigma`.

- 2026-08-09 (thirty-eighth instalment) -- **`(45)` re-derived for a weight degenerate at the
  origin.**  New module `RHTower/BesselWeightedPrimitiveInterior.lean`, wired, axiom-clean.

  * **`abs_integral_mul_besselJ0_le_interior`** -- the same bound `648 M / (c sqrt c)`, with the same
    constant, but requiring the weight to be differentiable only on the *open* radius interval and
    bounded on the half-open one.  Nothing is assumed at the origin: not a derivative, not
    continuity, not even a value.

  This is exactly the shape `B_sigma` satisfies.  The boundary term at the origin is identically
  zero -- `r J_1(c r)` vanishes there -- so the weight's junk value at `r = 0` is multiplied by zero
  and never enters.  The continuity needed for the fundamental theorem is continuity of the
  *product*, which the thirty-seventh instalment's endpoint lemma supplies from boundedness alone.

  One hypothesis had to be placed carefully: the derivative bound is required on `Ioc 0 R` rather
  than `Ioo 0 R`, because the integral-norm estimate runs over `Ioc`.  That costs nothing for the
  application -- `B_sigma'` is defined and bounded at `r = R > 0` -- but it is a real requirement,
  not a cosmetic one, and stating it on the open interval leaves the right endpoint uncontrolled.

  With this, every ingredient of `(47)` is now a theorem: the transport identity `(41)`, the
  substitution, the two-sided weight bound and the derivative bound `(43)`, and a primitive estimate
  whose hypotheses the weight actually satisfies.

- 2026-08-09 (thirty-ninth instalment) -- **`(47)` is closed in Lean.**  New module
  `RHTower/XiCompactPrimitive.lean` plus the derivative's continuity in `XiBesselWeightDeriv.lean`;
  wired, axiom-clean.

  * **`xiBesselWeightDeriv`, `continuousOn_xiBesselWeightDeriv`** -- the weight's derivative as a
    function, and its continuity on the positive ray, by composing the corpus's continuity of the
    amplitude derivative, the speed and the speed derivative with continuity of the inverse
    coordinate.
  * **`xiInverse_le_two`** -- the inverse coordinate stays below `2` on the compact phase range.
  * **`abs_integral_xiBesselWeight_le`** -- the primitive in the phase variable,
    `<= 648 * 64 / (c sqrt c)`.
  * **`integral_xiAmplitude_besselJ0_eq`** -- the substitution together with `(41)`: the transported
    integrand *is* the Liouville--Green amplitude.  The endpoint case is degenerate on both sides --
    `xiSpeed s 1` and `xiAmplitude s 1` are both zero -- so it needs no special argument.
  * **`abs_integral_radialProlateBesselProfile_le`** -- **`(47)`**:

    `| int_1^X radialProlateBesselProfile s c x dx | <= 648 * 64 / c`   for `1 < X <= 2`,
    `0 <= s <= 1/2`, `c > 0`.

  The statement is in the corpus's own vocabulary: `radialProlateBesselProfile` is the regular
  Dunster/Bessel profile `sqrt c * A_sigma(x) * J_0(c xi_sigma(x))` that
  `ProlateDunsterBesselOffDiagonal.lean` already defines.  One full power of the frequency, uniform
  in the endpoint, no hypotheses beyond the parameter ranges.

  This closes the compact branch.  Together with the exterior branch closed in the twenty-eighth
  instalment, both halves of the pole-uniform primitive are now unconditional Lean theorems about
  the actual prolate objects.

- 2026-08-09 (fortieth instalment) -- **The integrated profile transfer.**  New module
  `RHTower/ProlateProfileTransferIntegral.lean`, wired, axiom-clean.

  I checked the corpus first and found the supply side of `(38)` already there, which changes the
  picture for `(48)`.  `ProlateDunsterUniformTransfer.lean` proves
  `abs_radialProlate_sub_regularModel_le`: an unconditional uniform `O(c^-1)` approximation of the
  *actual* radial prolate profile by the regular Bessel model beyond an explicit matching point,
  with one constant independent of `s`, `c`, the solution and the endpoint.
  `ProlateDunsterDensityTransfer.lean` restates it as
  `abs_radialProlate_sub_besselProfile_le`, pointwise against `A_sigma(x) J_0(c xi_sigma(x))` --
  which is exactly the integrand of `(47)` up to the `sqrt c` normalization.  So the expansion `(38)`
  is not an outstanding input at all; only its integrated form was missing.

  * **`abs_integral_radialProlate_sub_besselProfile_le`** -- the integrated form:

    `| int_a^b (R(x) - A_sigma(x) J_0(c xi_sigma(x))) dx |
       <= (4 K C / c) (b - a)`   for `dunsterEndpointCrossing c <= a <= b`.

  Beyond the matching point the Bessel envelope is at most one -- because `c xi_sigma` is at least
  one there and the phase is increasing -- and the amplitude is at most four, so the pointwise
  transfer becomes a constant multiple of `c^-1` and integrating costs only the length.

  Composing this with the thirty-ninth instalment's `(47)` bounds the primitive of the *exact*
  profile, not merely of the model: the model's primitive is `O(c^-1)` by `(47)` and the difference
  of primitives is `O(c^-1)` by the transfer.  What is still needed to write that composition down
  as one statement is a bound on the matching point itself, `dunsterEndpointCrossing c <= 2`, so that
  the two ranges overlap.

- 2026-08-09 (forty-first instalment) -- **Keeping the envelope's decay, and why it matters.**  New
  module `RHTower/ProlateEnvelopeIntegral.lean` plus a quarter-power atom in
  `HTGeometry/InverseSqrtEndpointIntegral.lean`; wired, axiom-clean.

  A rate correction to the fortieth instalment, found by checking the arithmetic rather than
  assuming it.  That instalment bounded the Bessel envelope by one, giving a transfer error of
  `O(c^-1)` times the length.  After the model's own `sqrt c` normalization that is `O(c^(-1/2))`,
  which is *weaker* than the `O(c^-1)` of `(47)` and would have dominated it.  The card's own
  accounting does not lose this: it applies the crude envelope bound `(46)`, worth a further
  `c^(-1/2)`, to the error term, so the error contributes `O(c^(-3/2))` and the rate survives.

  * **`sqrt_sub_one_le_xiEndpointPhase`** -- `sqrt(x-1) <= xi_sigma(x)`.  A clean consequence of the
    corpus bracket in which the two constants cancel exactly: `sqrt(1-s) >= sqrt(1/2)` and
    `sqrt(x+1) >= sqrt 2`, and `sqrt(1/2) sqrt 2 = 1`.
  * **`hasDerivAt_rpow_three_quarters_sub_one`, `integral_rpow_neg_quarter_sub_one`** -- the
    quarter-power endpoint integral `int_1^x (t-1)^(-1/4) dt = (4/3)(x-1)^(3/4)`.
  * **`integral_rpow_neg_quarter_le`** -- hence that weight has integral at most `4/3` on the
    compact exterior range.

  Together these say the envelope is integrable against the endpoint singularity: the envelope is
  `(c xi_sigma(x))^(-1/2)`, the phase is at least `sqrt(x-1)`, so the envelope is at most
  `c^(-1/2) (x-1)^(-1/4)`, whose integral is bounded.  That is the missing `c^(-1/2)`, and with it
  the transfer error integrates to `O(c^(-3/2))` -- the same rate as the model's own primitive after
  normalization.

  The lesson is worth keeping: bounding an envelope by its supremum is not free here.  The half power
  it discards is exactly the half power that separates the error from the main term.

- 2026-08-09 (forty-second instalment) -- **The sharp integrated transfer: the rate is preserved.**
  Two theorems added to `RHTower/ProlateEnvelopeIntegral.lean` plus a quarter-root identity in
  `HTGeometry/InverseSqrtEndpointIntegral.lean`; wired, axiom-clean.

  * **`rpow_neg_quarter_eq_inv_sqrt_sqrt`** -- `t^(-1/4) = (sqrt (sqrt t))^(-1)`.
  * **`envelope_le_quarter_weight`** -- the Bessel envelope is dominated by the quarter-power
    endpoint weight with the frequency's half power extracted:
    `C / sqrt(c xi_sigma(x)) <= (C / sqrt c) (x-1)^(-1/4)`.
  * **`abs_integral_radialProlate_sub_besselProfile_sharp_le`** -- **the sharp transfer**:

    `| int_a^b (R(x) - A_sigma(x) J_0(c xi_sigma(x))) dx |
       <= 8 K C / (3 c sqrt c)`   for `dunsterEndpointCrossing c <= a <= b <= 2`.

  This is `O(c^(-3/2))`, one half power better than the fortieth instalment's crude bound, and it is
  the rate the composition needs: after the model's own `sqrt c` normalization it becomes `O(c^-1)`,
  matching `(47)` instead of dominating it.

  The three inputs are the pointwise transfer already in the corpus, the phase lower bound
  `xi_sigma(x) >= sqrt(x-1)`, and the integrability of `(x-1)^(-1/4)`.  Nothing about the envelope is
  discarded: it is integrated, not bounded by its supremum.

- 2026-08-09 (forty-third instalment) -- **The primitive of the *exact* prolate profile.**  New
  module `RHTower/ProlateExactPrimitive.lean`, wired, axiom-clean.

  * **`intervalIntegrable_radialProlateBesselProfile`** -- the regular Bessel profile is interval
    integrable up to the endpoint.  It has no value there -- the amplitude is a `0/0` -- but it is
    bounded and continuous on the open interval, which is all the thirty-seventh instalment's
    integrability lemma needs.
  * **`abs_integral_sqrt_mul_radialProlate_le`** -- **the exact-profile primitive**:

    `| int_A^X sqrt c R(x) dx | <= (8 K C / 3 + 2 (648 * 64)) / c`,
    `A = dunsterEndpointCrossing c <= X <= 2`.

  This is `(47)` for the actual radial prolate mode rather than for the model, and the rate is the
  full `O(c^-1)`.  The decomposition is exactly the card's: exact profile = model + transfer error.
  The model's primitive is `O(c^-1)` by the thirty-ninth instalment, applied twice because the range
  starts at the matching point rather than at the endpoint; the transfer error is `O(c^(-3/2))` by
  the forty-second, and the `sqrt c` normalization brings it to `O(c^-1)`.  Neither piece would have
  sufficed with the crude envelope bound.

  The matching point is below `2` for `c >= 5` (`dunsterEndpointCrossing_le_eleven_tenths`, already
  in the corpus), so the two ranges overlap and the composition is legitimate -- the missing overlap
  fact named in the fortieth instalment.

- 2026-08-09 (forty-fourth instalment) -- **Status audit of `(17)` and `(11)`; no new Lean.**

  Item 6 of the infrastructure list said `[PHASE FORMALIZED; AMPLITUDE OPEN]`.  That is now stale:
  the amplitude side is closed.  `(48)`'s amplitude bounds, `(43)` in both halves, `(47)` for the
  model and for the exact mode, and the exterior branch `(50)` are all unconditional Lean theorems.
  The item's status line is corrected above.

  Two pieces of `(17)`/`(11)` remain, and it is worth naming them exactly rather than leaving them
  inside a general "amplitude open".

  **(a) The endpoint interval.**  `abs_integral_sqrt_mul_radialProlate_le` covers
  `[dunsterEndpointCrossing c, X]`.  The card's own remark -- "the endpoint interval has width
  `O(c^-2)`; outside it, the Bessel branches are nonstationary" -- matches exactly, since
  `dunsterEndpointCrossing c - 1 = 9/(8 c^2)`.  What is missing is the contribution of `[1, crossing]`
  itself.  A sup bound `|R| <= C` there would give `sqrt c * C * 9/(8 c^2) = O(c^(-3/2))`, better
  than needed.  I checked whether the corpus's density bound supplies it: it does not.
  `radialProlateDensity_le_profileWeight` bounds `c R(x)^2` by `profileWeight s x`, and
  `profileWeight s x = 1/(pi sqrt((x^2-1)(x^2-s)))` *diverges* as `x -> 1`.  So that route degenerates
  precisely on the interval in question, and the endpoint bound has to come from the initial
  condition `R 1 = 1` and the ODE -- a Gronwall estimate on a `O(c^-2)`-wide interval -- not from the
  density envelope.

  **(b) The `k >= 2` channels `(16)`.**  The radial channels `H_(lambda,k)` have no counterpart in the
  corpus at all; nothing named for them exists.  The summation machinery on top of them is however
  already built and needs nothing further: `HTGeometry/L2PairingLimit.lean` gives
  `norm_inner_le_tsum_of_tendsto`, which takes a summable channel majorant and a norm limit of
  partial sums and returns the summed bound.  So `(16)` is the whole of the remaining work for
  `(11)`, and it is a construction, not an assembly.

- 2026-08-09 (forty-fifth instalment) -- **Piece (a) closed: the mode is bounded on the endpoint
  interval.**  New module `RHTower/ProlateEndpointEnergy.lean`, wired, axiom-clean.

  The forty-fourth instalment showed the density envelope cannot do this -- `profileWeight` diverges
  at the endpoint -- and that the bound must come from the equation and the initial condition.  It
  does, by an energy argument.

  * **`prolateEndpointEnergy`** -- the Sturm energy `E = (t^2-1)(R')^2 + c^2(t^2-s)R^2` of
    `((t^2-1)R')' + c^2(t^2-s)R = 0`.
  * **`hasDerivAt_prolateEndpointEnergy`** -- `E' = 2t(c^2 R^2 - (R')^2)`.  Not sign-definite, which
    is why the naive monotone-energy argument fails.
  * **`sq_le_two_mul_prolateEndpointEnergy`** -- but `c^2 R^2 <= 2E`, because `t^2 - s >= 1/2`.  The
    endpoint degeneracy sits entirely in the `(t^2-1)` term, which is nonnegative and simply
    discarded.
  * **`prolateEndpointEnergy_le_exp`** -- hence `E' <= 5E` on `[1, 11/10]`, and Grönwall gives
    `E(t) <= E(1) exp(5(t-1))`.
  * **`abs_radialProlate_le_two_endpoint`** -- **`|R(t)| <= 2` on `[1, dunsterEndpointCrossing c]`**
    for `c >= 5`.

  The numbers work out with room to spare: the interval has width `9/(8c^2) <= 9/200`, so the
  exponential factor is at most `exp(1/4) < 2`, and `E(1) = c^2(1-s)` exactly because `R 1 = 1`.
  Combining, `c^2 R^2 <= 4c^2`.

  This closes piece (a).  The contribution of the endpoint interval to `(17)` is therefore
  `sqrt c * 2 * 9/(8c^2) = O(c^(-3/2))`, comfortably inside the target rate, and `(16)` for the
  `k >= 2` channels is now the only remaining input for `(11)`.

- 2026-08-09 (forty-sixth instalment) -- **`(17)` is closed in Lean for the exact radial mode.**
  New module `RHTower/ProlateFullPrimitive.lean`, wired, axiom-clean.

  * **`abs_integral_endpoint_interval_le`** -- the endpoint interval contributes at most
    `2 sqrt c (b-1)`.
  * **`abs_integral_sqrt_mul_radialProlate_full_le`** -- **`(17)`**:

    `| int_1^X sqrt c R(x) dx | <= (9/4 + 8KC/3 + 2*648*64) / c`   for `1 <= X <= 2`, `c >= 5`,
    `0 <= s <= 1/2`, `R 1 = 1`, `R` solving the radial equation.

  The split is at the matching point.  Beyond it the forty-third instalment's exterior primitive
  applies; on `[1, crossing]` the forty-fifth instalment's sup bound `|R| <= 2` applies, and since
  that interval is only `9/(8c^2)` wide its contribution is `9/(4 c sqrt c)`, i.e. `O(c^(-3/2))` --
  strictly smaller than the exterior contribution rather than merely comparable.  The two cases
  `X <= crossing` and `X > crossing` are handled separately; in the first the exterior term is simply
  absent.

  The gate line for `(17)` is corrected above: it previously recorded only the model form `(47)`.

  With `(17)` closed, `(16)` for the `k >= 2` channels is the sole remaining input to `(11)`, and
  from `(11)` the card's `(18)` follows by `(4)` and `(10)`, both already formalized.

- 2026-08-09 (forty-seventh instalment) -- **The `k`-channel exterior estimate: `(15)` and the
  mechanism of `(16)`.**  New module `RHTower/ProlateDilatedChannel.lean`, wired, axiom-clean.

  Reading `(13)`--`(15)` closely, the `k`-th channel differs from the first only by the dilation of
  the phase, `xi_s(k x)` in place of `xi_s(x)`, and by the explicit prefactor `1/k` in `(13)`.  The
  amplitude bounds `(14)` are *identical* to `(48)`'s.  So no new estimate is needed for `(16)` --
  only the observation that the dilated phase satisfies the same hypotheses with frequency `c k`.

  * **`dilatedPhase`, `hasDerivAt_dilatedPhase`** -- the normalized dilated phase `xi_s(k x)/k`, whose
    derivative is `xi_s'(k x)`, again at least one.  This is `(15)`: the phase speed of the `k`-th
    channel is `k` times larger, and normalizing moves that factor into the frequency.
  * **`hasDerivAt_inv_dilatedSpeed`, `abs_dilated_inv_speed_deriv_le`** -- the reciprocal speed's
    variation is *improved* by the dilation.  The chain rule contributes a factor `k`, the argument
    `k x` contributes `k^(-2)`, and the net `k^(-1)` is discarded: the bound `|(1/xi')'| <= x^(-2)`
    holds for every `k >= 1` with the same constant.
  * **`norm_integral_exterior_dilated_le`** -- hence the `k`-th channel's exterior primitive is
    `O(1/(c k))`, one full factor `k` better than the first channel.

  Together with the `1/k` prefactor of `(13)` this is the `1/(c k^2)` of `(16)`: one factor of `k`
  from the expansion, one from the phase speed.  What is still not formalized is the expansion `(13)`
  itself -- that `U_(lambda,k)` *equals* that two-branch sum -- exactly as `(48)` was for the first
  channel before the corpus's Dunster transfer was found to supply it.

- 2026-08-09 (forty-eighth instalment) -- **The two-branch expansion is closer than recorded: the
  corpus owns the Bessel-to-cosine bridge.**  New module `RHTower/AmpFourthDecay.lean`, wired,
  axiom-clean.

  I said last instalment that `(13)`/`(48)` as *identities* were open, and flagged that it was worth
  checking whether the corpus supplies them rather than assuming.  It largely does.
  `ProlateDunsterBesselOffDiagonal.abs_radialProlateBesselProfile_sub_leading_le` proves

  `| radialProlateBesselProfile s c x - sqrt(2/pi) ampFourth s x cos(c xi_s(x) - pi/4) |
     <= compactBesselProfileError s c a`

  for `1 < a <= x` with `1 <= c xi_s(a)`.  That *is* the two-branch form: the cosine is
  `(e^{i theta} + e^{-i theta})/2`, so the leading term is exactly the `sum over eps = +-1` of
  `(13)`/`(48)` with amplitudes `sqrt(2/pi) ampFourth s x e^{∓ i pi/4}/2`.

  What was missing is the amplitude bound in the normalization the exterior estimate expects.

  * **`ampFourth_le_two_div`** -- `ampFourth s x = ((x^2-1)(x^2-s))^(-1/4) <= 2/x` for `x >= 2`.
  * **`sqrt_mul_ampFourth_le`** -- hence in the normalization `a(x)/sqrt x` used by
    `norm_integral_exterior_le`, the amplitude is `a(x) = sqrt x * ampFourth s x <= 2/sqrt x`, which
    is exactly the first half of `(14)`/`(48)`.

  So the correction to record is that `(13)`/`(48)` are not open constructions.  What remains of them
  is the derivative half of `(14)` for this amplitude -- `|a'| <= C x^(-3/2)`, i.e. a bound on
  `ampFourth'` -- and the bookkeeping that turns the cosine into two exponentials under the integral.
  Both are mechanical against what is now built.

- 2026-08-09 (forty-ninth instalment) -- **`(14)` is complete for the leading amplitude.**  Three
  theorems added to `RHTower/AmpFourthDecay.lean`; wired, axiom-clean.

  * **`quarter_root_deriv_identity`** -- the algebraic identity behind differentiating a quarter
    root, stated with the square relation `p * p = P` abstracted into a hypothesis.  Abstracting it
    is not cosmetic: rewriting `(x^2-1)(x^2-s)` into `sqrt(...) * sqrt(...)` in place loops through
    the radicands, and `field_simp` on the concrete form leaves an unusable residual.
  * **`hasDerivAt_ampFourth`** -- the leading amplitude is differentiable, with
    `ampFourth' = -(P'/(4P)) ampFourth`, `P = (x^2-1)(x^2-s)`.
  * **`abs_deriv_ampFourth_le`** -- `|ampFourth'(x)| <= 32/x^2` for `x >= 2`.

  With the forty-eighth instalment's `ampFourth <= 2/x`, the normalized amplitude
  `a(x) = sqrt x * ampFourth s x` satisfies both halves of `(14)`: `|a| <= 2 x^(-1/2)` and, since
  `a' = ampFourth/(2 sqrt x) + sqrt x * ampFourth'`, also `|a'| = O(x^(-3/2))`.

  So the amplitude side of the two-branch expansion `(13)`/`(48)` is now fully formalized for the
  leading form, for every channel: the dilation of the forty-seventh instalment does not touch the
  amplitude, only the phase.  What remains is the bookkeeping that rewrites the cosine as two
  exponentials under the integral sign and feeds the result to
  `norm_integral_exterior_dilated_le`.

- 2026-08-09 (fiftieth instalment) -- **The cosine bridge, and where the `1/k^2` is currently lost.**
  New module `HTGeometry/CosineToExponential.lean` plus two theorems in
  `RHTower/ProlateDilatedChannel.lean`; wired, axiom-clean.

  * **`mul_cos_sub_eq_re`, `abs_integral_mul_cos_sub_le`** -- a shifted cosine integral is dominated
    by its complex exponential integral, with no loss: it is the real part of that integral times a
    unimodular rotation.  This is the bookkeeping the forty-eighth instalment named, stated for
    arbitrary amplitude and phase.
  * **`ampFourth_dilate_le`** -- `ampFourth s (k x) <= 2/(k x)`: the dilated amplitude carries the
    channel's `1/k` automatically, which is `(13)`'s prefactor appearing without being put in by
    hand.
  * **`abs_deriv_ampFourth_dilate_le`** -- its derivative carries the same `1/k` on top of the
    `x^(-2)` decay.

  **An obstruction found by trying the composition rather than assuming it.**  Feeding these into
  `norm_integral_exterior_dilated_le` does *not* yield `(16)`'s `1/(c k^2)`.  That theorem, inherited
  from `norm_integral_exterior_le`, uses a *single* constant `C` for both the amplitude bounds and
  the reciprocal-speed variation `|(1/xi')'| <= C x^(-2)`, and the latter forces `C >= 1` through the
  `max C 1`.  So an amplitude constant of size `C_0/k` is silently rounded back up to `1` and the
  gain is discarded.

  The fix is a genuine refinement, not a rearrangement: `norm_integral_exterior_le` should carry two
  constants, `C_a` for the amplitude and `C_rho` for the speed variation.  Its proof already supports
  this -- the profile obeys `|P| <= C_a/x` and `|P'| <= (3 C_a/2 + C_a C_rho/2) x^(-2)`, both linear
  in `C_a` -- so the conclusion is linear in `C_a` and the `1/k` survives.  Both factors of `k` are
  then present: one from the amplitude here, one from the phase speed in the forty-seventh
  instalment.

- 2026-08-09 (fifty-first instalment) -- **The two-constant refinement: the `1/k` is no longer
  discarded.**  Two theorems added to `RHTower/ExteriorProfileBounds.lean`; wired, axiom-clean.

  The fiftieth instalment found that the exterior bound's single constant silently rounds a small
  amplitude constant back up to `1`, because the same constant also carries the reciprocal-speed
  variation, which cannot be taken below one.  Separating them fixes it.

  * **`norm_deriv_exteriorProfile_two_const_le`** -- the profile derivative obeys
    `|P'| <= (3 C_a/2 + C_a C_r/2) x^(-2)`, **linear** in the amplitude constant `C_a`, with the
    speed-variation constant `C_r` entering only as a multiplier.
  * **`norm_integral_exterior_two_const_le`** -- hence the exterior primitive is at most
    `3 C_a (3/2 + C_r/2) / (2 c)`, again linear in `C_a`.

  The profile constant is `C' = C_a (3/2 + C_r/2)`, and the two decay bounds it must satisfy are
  `|P| <= C_a/x <= C'/x` and `|P'| <= C'/x^2` -- the second an equality, so nothing is lost in the
  passage.  With `C_a` of size `1/k` from `ampFourth_dilate_le` and the frequency `c k` from
  `hasDerivAt_dilatedPhase`, both factors of `k` are now present, which is `(16)`'s `1/(c k^2)`.

  The original single-constant statements are kept: they are what the first channel's assembly
  already uses, and nothing downstream needed changing.

- 2026-08-09 (fifty-second instalment) -- **`(16)`'s estimate, with both factors of `k`.**  One
  theorem added to `RHTower/ProlateDilatedChannel.lean`; wired, axiom-clean.

  * **`norm_integral_exterior_dilated_sharp_le`** --

    `‖ int_2^X (a(t)/sqrt t) exp(i eps (c k) xi_s(k t)/k) dt ‖ <= 3 C_a / (c k)`

    for `|a| <= C_a x^(-1/2)`, `|a'| <= C_a x^(-3/2)`, `k >= 1`, `c > 0`, `0 <= s <= 1/2`.

  The reciprocal-speed variation constant is `1` for *every* `k` -- that is the content of
  `abs_dilated_inv_speed_deriv_le`, where the chain rule's factor `k` is cancelled by the argument's
  `k^(-2)` -- so the two-constant bound of the fifty-first instalment applies with `C_r = 1` and the
  conclusion stays linear in `C_a`.

  Combining with `ampFourth_dilate_le`, whose amplitude constant is `O(1/k)`, gives `O(1/(c k^2))`:
  one factor of `k` from the amplitude, one from the phase speed.  That is `(16)`.

  What is left between here and `(11)` is assembly rather than estimation: instantiate this at the
  concrete leading amplitude via the cosine bridge, and sum the channels with
  `norm_inner_le_tsum_of_tendsto`, whose summable-majorant hypothesis `1/k^2` now holds.

- 2026-08-09 (fifty-third instalment) -- **The concrete leading amplitude of the `k`-th channel.**
  Four definitions/theorems added to `RHTower/ProlateDilatedChannel.lean`; wired, axiom-clean.

  * **`leadingAmp`, `leadingAmpDeriv`** -- the amplitude `sqrt t * sqrt(2/pi) * ampFourth s (k t)` in
    the normalization the exterior estimate uses, and its derivative.
  * **`sqrt_two_div_pi_le_one`** -- `sqrt(2/pi) <= 1`.
  * **`hasDerivAt_leadingAmp`** -- differentiability, by the product rule against the chain rule for
    `ampFourth` at `k t`.
  * **`abs_leadingAmp_le`** -- `‖a(t)‖ <= (2/k) / sqrt t`.
  * **`abs_leadingAmpDeriv_le`** -- `‖a'(t)‖ <= (33/k) / (t sqrt t)`.

  So the concrete channel amplitude satisfies `(14)` with amplitude constant `C_a = 33/k`, which is
  the `1/k` of `(13)` derived rather than assumed.  Feeding this into
  `norm_integral_exterior_dilated_sharp_le` gives `3 (33/k) / (c k) = 99/(c k^2)` -- **`(16)`**, with
  an explicit constant.

  Both factors of `k` are now accounted for by proved statements: one from the amplitude here, one
  from the phase speed in the forty-seventh instalment, and the two-constant bound of the fifty-first
  instalment is what stops the first from being discarded.

- 2026-08-09 (fifty-fourth instalment) -- **`(16)` is closed, with an explicit constant.**  Two
  theorems added to `RHTower/ProlateDilatedChannel.lean`; wired, axiom-clean.

  * **`continuousOn_ampFourth_comp`, `continuousOn_leadingAmpDeriv`** -- continuity of the dilated
    amplitude and of its derivative.  The corpus has no continuity lemma for `ampFourth`, so both
    are derived from `hasDerivAt_ampFourth`.
  * **`norm_integral_leading_channel_le`** -- **`(16)`**:

    `‖ int_2^X leadingAmp(s,k,t) (sqrt t)^(-1) exp(i eps (c k) xi_s(k t)/k) dt ‖ <= 99/(c k^2)`

    for `k >= 1`, `c > 0`, `0 <= s <= 1/2`, `X >= 2`, `|eps| = 1`.

  Everything in the statement is concrete: the amplitude is the leading Liouville--Green amplitude of
  the `k`-th channel, the phase is the dilated exterior phase, and the constant is explicit.  The
  `k^(-2)` is assembled from three proved facts -- the amplitude constant `33/k`, the frequency `c k`,
  and the two-constant bound that keeps them from collapsing.

  Item 6 of the infrastructure list is updated above.  What remains for `(11)` is the identity
  expressing `U_(lambda,k)` as this leading channel plus a controlled error -- the corpus's
  `abs_radialProlateBesselProfile_sub_leading_le` supplies exactly that shape for `k = 1` -- and then
  the summation, for which `norm_inner_le_tsum_of_tendsto` is built and whose `1/k^2` majorant is now
  available.

- 2026-08-09 (fifty-fifth instalment) -- **The bridge dilates, but it is a compact-range tool: a
  correction to the forty-eighth instalment.**  One corollary added to
  `RHTower/ProlateDilatedChannel.lean`; wired, axiom-clean.

  * **`abs_radialProlateBesselProfile_dilate_sub_leading_le`** -- the corpus's leading-form bridge is
    pointwise in its argument, so substituting `k t` gives the `k`-th channel's leading form with no
    new hypothesis.  The proof is a one-liner; what it establishes is that no hidden restriction
    blocks the dilation, which is what needed checking.

  **The correction.**  In the forty-eighth instalment I wrote that the corpus "largely supplies"
  `(13)`/`(48)`.  That was too strong, and working the composition through shows why.  The bridge's
  error term is `compactBesselProfileError s c a = 5 ampFourth(s,a)/(c xi_s(a))^(1/4)`, which is
  *constant in `x`* on `[a, infinity)`.  Integrating it over `[2, X]` therefore contributes
  proportionally to `X - 2`, so the composition gives no bound uniform in the endpoint.  Splitting
  into dyadic blocks does not rescue it either: on `[2^j, 2^(j+1)]` the error contributes
  `~ (c 2^j)^(-1/4)`, and summing over `j` gives `O(c^(-1/4))` -- far short of `O(1/(c k^2))`.

  The name is the clue and I should have read it: `compactBesselProfileError`.  The bridge is a
  compact-range instrument.  The card's `(13)` is a different object -- a genuine *exterior*
  expansion whose amplitudes and errors both decay like powers of `x` -- and that is what
  `norm_integral_leading_channel_le` consumes.

  So the honest state of `(16)`: the *estimate* is closed unconditionally with an explicit constant,
  for any amplitude satisfying `(14)`.  The *identity* `(13)` -- that `U_(lambda,k)` equals the
  two-branch sum with such amplitudes on the unbounded exterior -- is not supplied by the corpus and
  remains the outstanding input, exactly as it was before the forty-eighth instalment.

- 2026-08-09 (fifty-sixth instalment) -- **Correcting the correction: the bridge error does decay in
  `x`; what it loses is the rate in `c`.**  Two theorems added to
  `RHTower/ProlateEnvelopeIntegral.lean`; wired, axiom-clean.

  Last instalment I said the bridge fails because its error is constant in `x` and so integrates to
  something growing with the endpoint.  That was wrong, and the reason is worth recording.
  `compactBesselProfileError s c a` is constant in `x`, but it is a *weakening*: the corpus's
  underlying pointwise bound `abs_profile_sub_model_le` is
  `5 ampFourth(s,x) / (c xi_s(x))^(1/4)`, evaluated at `x`, and that does decay.  The bridge theorem
  simply freezes it at the left endpoint on the way to its own statement.

  * **`half_mul_le_xiEndpointPhase`** -- `xi_s(x) >= x/2` for `x >= 2`.  The sharper companion to
    `sqrt_sub_one_le_xiEndpointPhase`, which is the right bound only near the endpoint.
  * **`abs_profile_sub_model_decay_le`** -- the bridge error with its decay explicit:
    `<= 10 / (x (c x/2)^(1/4))`, i.e. `O(c^(-1/4) x^(-5/4))`.

  So the integrated error *is* uniform in the endpoint -- `x^(-5/4)` is integrable on `[2, infinity)`
  -- and my stated reason last instalment was simply incorrect.  The conclusion, however, stands, for
  a different reason: the rate in `c` is `c^(-1/4)`, not `c^(-1)`.  Feeding this into `(16)` would
  give `O(c^(-1/4))` where `O(1/(c k^2))` is needed.

  The bridge is a leading-order statement with a fourth-root error; the card's `(13)` needs a
  full Liouville--Green expansion whose error is `O(1/c)` relative.  That remains the outstanding
  input, and the reason is now pinned down quantitatively rather than by inspection.

- 2026-08-09 (fifty-seventh instalment) -- **The Liouville--Green normal form of Bessel's equation.**
  New module `RHTower/BesselNormalForm.lean`, wired, axiom-clean.

  The fifty-sixth instalment pinned the outstanding input: `(13)` needs a Bessel asymptotic with
  `O(1/c)` relative error, whereas the corpus's bridge gives `O(c^(-1/4))`.  The sharp asymptotic
  starts from removing the first-order term.

  * **`besselNormalForm`, `besselNormalFormDeriv`, `besselNormalFormSecond`** -- `w = sqrt u J_0(u)`
    and its two derivatives.
  * **`hasDerivAt_besselNormalForm`, `hasDerivAt_besselNormalFormDeriv`** -- differentiability.
  * **`besselNormalForm_ode`** -- **the normal form**:

    `w'' + (1 + 1/(4 u^2)) w = 0`.

  The first-order term is gone exactly, and the potential differs from the harmonic one by
  `1/(4u^2)`, which is integrable at infinity.  That integrability is the whole point: the leading
  cosine is the unperturbed solution, and the perturbation's integral is what bounds the error, which
  is how `O(u^(-3/2))` -- relative `O(1/u)` -- arises rather than the fourth-root loss.

  A note on tactics, since this cost several attempts.  Both identities go through `field_simp`
  followed by `linear_combination c * hss` with `hss : sqrt u * sqrt u = u`, and the coefficient `c`
  is not worth guessing: `linear_combination (0) * hss` prints the exact residual, which factors as
  `(sqrt u ^ 2 - u)` times the coefficient needed.  Reading it off is immediate; guessing is not.

- 2026-08-09 (fifty-eighth instalment) -- **The oscillator energy of the normal form.**  Three
  theorems added to `RHTower/BesselNormalForm.lean`; wired, axiom-clean.

  * **`besselEnergy`, `besselEnergy_nonneg`** -- `E = w^2 + (w')^2` for `w = sqrt u J_0(u)`.
  * **`hasDerivAt_besselEnergy`** -- `E' = -2 (1/(4u^2)) w w'`.  The unperturbed part cancels
    identically: for `w'' + w = 0` the energy is exactly conserved, so what survives is the
    perturbation alone.
  * **`abs_deriv_besselEnergy_le`** -- `|E'| <= (1/(4u^2)) E`, by the arithmetic--geometric mean
    inequality `2|w||w'| <= w^2 + (w')^2`.

  This is the differential inequality that makes the sharp asymptotic work.  The perturbation
  `1/(4u^2)` is integrable on `[a, infinity)` with integral `1/(4a)`, so Gronwall bounds the energy
  by `E(a) exp(1/(4a))` and, more to the point, forces `E` to converge: the amplitude of
  `sqrt u J_0(u)` stabilises at rate `O(1/u)`.  That `O(1/u)` is exactly the relative error the
  fifty-sixth instalment identified as needed, and is what the corpus's fourth-root bridge does not
  provide.

- 2026-08-09 (fifty-ninth instalment) -- **Grönwall for the Bessel energy.**  Three theorems added to
  `RHTower/BesselNormalForm.lean`; wired, axiom-clean.

  * **`hasDerivAt_inv_four_mul`** -- `d/dv [1/(4v)] = -1/(4v^2)`, the integrating factor's exponent.
  * **`besselEnergy_le_exp`** -- **Grönwall**:
    `E(u) <= E(a) exp(1/(4a) - 1/(4u))` for `0 < a <= u`.  The multiplier `E(v) exp(1/(4v))` is
    antitone because the differential inequality of the fifty-eighth instalment says exactly that its
    derivative is nonpositive.
  * **`abs_besselNormalForm_le`** -- hence `|sqrt u J_0(u)|` is bounded on `[a, infinity)` by
    `sqrt(E(a) exp(1/(4a)))`.

  Two things worth noting.  First, the exponent `1/(4a) - 1/(4u)` is bounded by `1/(4a)` uniformly in
  `u`, so the envelope constant does not degrade however far out one goes -- the perturbation's total
  mass is finite and that is all the argument uses.  Second, this recovers the `u^{-1/2}` envelope
  the corpus already had, but with a constant that is an invariant of the equation (the energy at a
  base point) rather than an artefact of a stationary-phase estimate.  The corpus's constant is
  `72 sqrt 2`; this one is whatever the solution's own energy is.

  The remaining step to `(13)` is to extract the phase: the energy controls the amplitude, and the
  angle variable `arctan(w'/w)` differs from `u` by an integral of the perturbation, which is
  `O(1/u)`.

- 2026-08-09 (sixtieth instalment) -- **The two-branch representation, exactly.**  Three theorems
  added to `RHTower/BesselNormalForm.lean`; wired, axiom-clean.

  * **`besselCosCoeff`, `besselSinCoeff`** -- `A = w cos u - w' sin u` and `B = w sin u + w' cos u`.
  * **`besselNormalForm_eq_coeff`** -- `w(u) = A(u) cos u + B(u) sin u`, an *identity*, not an
    approximation: the coefficients are defined so that it holds exactly.
  * **`hasDerivAt_besselCosCoeff`, `hasDerivAt_besselSinCoeff`** -- `A' = q w sin u` and
    `B' = -q w cos u` with `q = 1/(4u^2)`.

  This is variation of parameters against the unperturbed basis, and it is the right formalization
  route: a Prüfer angle would need `arctan` and an ODE existence theorem, whereas `A` and `B` are
  defined outright and their derivatives fall out of the normal form by one `ring` step each.  The
  unperturbed part cancels exactly in both, as it must -- for `w'' + w = 0` the coefficients are
  literally constant.

  The whole content of the sharp asymptotic is now visible: `w` is *exactly* a combination of `cos u`
  and `sin u` whose coefficients move at rate `q |w|`.  Since `|w|` is bounded by the energy
  (fifty-ninth instalment) and `q = 1/(4u^2)` is integrable, `A` and `B` converge with error
  `O(1/u)` -- which is `(13)`'s two-branch form with `(14)`'s rate, and the `O(1/c)` relative error
  the fifty-sixth instalment showed was needed.

- 2026-08-09 (sixty-first instalment) -- **The sharp Bessel asymptotic, with `O(1/a)` error.**  Five
  theorems added to `RHTower/BesselNormalForm.lean`; wired, axiom-clean.

  * **`hasDerivAt_neg_inv_four_mul`, `intervalIntegrable_inv_four_sq`, `integral_inv_four_sq`** --
    the perturbation's tail mass, `int_a^u 1/(4v^2) dv = 1/(4a) - 1/(4u)`.
  * **`abs_besselCoeff_sub_le`** -- both coefficients move by at most `M (1/(4a) - 1/(4u))`, where
    `M` bounds `|w|` on the range.
  * **`abs_besselNormalForm_sub_fixed_le`** -- **the asymptotic**:

    `| sqrt u J_0(u) - (A(a) cos u + B(a) sin u) | <= 2 M (1/(4a) - 1/(4u))`.

  On `[a, infinity)` the normal-form solution equals a *fixed* sinusoid -- the one its own
  coefficients determine at `a` -- up to an error bounded by `2M/(4a)`, uniformly in `u`.  This is
  the `O(1/u)` relative error the fifty-sixth instalment identified as the missing input, in exactly
  the two-branch shape `(13)` asks for: `cos` and `sin` are the two branches, `A(a)` and `B(a)` are
  the amplitudes, and the error is the expansion's remainder.

  The amplitude hypothesis is discharged by the fifty-ninth instalment: `abs_besselNormalForm_le`
  supplies `M = sqrt(E(a) exp(1/(4a)))`, so nothing here is assumed.  The chain from Bessel's
  equation to a two-branch expansion with `O(1/a)` error is now closed end to end -- normal form,
  energy, Grönwall, variation of parameters, tail integration -- and none of it needed a stationary
  phase estimate or an ODE existence theorem.

- 2026-08-09 (sixty-second instalment) -- **`(13)` for the Bessel model: the two-branch expansion
  with no free constant.**  Three theorems added to `RHTower/BesselNormalForm.lean`; wired,
  axiom-clean.

  * **`besselCoeff_sq_add`** -- `A(a)^2 + B(a)^2 = E(a)`.  The two-branch amplitude is not an
    auxiliary quantity: its square *is* the energy.
  * **`abs_besselNormalForm_sub_fixed_le'`** -- the asymptotic with the amplitude hypothesis
    discharged by the fifty-ninth instalment's envelope.
  * **`abs_besselJ0_sub_fixed_le`** -- **the sharp asymptotic for `J_0`**:

    `| J_0(u) - (A(a) cos u + B(a) sin u)/sqrt u |
       <= 2 sqrt(E(a) exp(1/(4a))) (1/(4a) - 1/(4u)) / sqrt u`.

  This is `(13)`'s shape for the Bessel model, with everything explicit: two branches, amplitudes
  decaying like `u^(-1/2)`, and a remainder that is `O(a^(-1) u^(-1/2))` -- relative `O(1/a)`, the
  rate the fifty-sixth instalment showed was required and the corpus's fourth-root bridge could not
  reach.

  The identity `A^2 + B^2 = E` is what ties the two halves together: the energy bounds the amplitude
  (fifty-ninth), the amplitude bounds the coefficient drift (sixty-first), and the coefficients'
  squares return the energy.  There is no separate estimate for the amplitude of the expansion --
  it is the same invariant throughout.

- 2026-08-09 (sixty-third instalment) -- **`(13)` for the prolate profile: the two-branch expansion
  with relative `O(1/c)` error.**  New module `RHTower/ProlateTwoBranch.lean`, wired, axiom-clean.

  * **`xiAmplitude_div_sqrt_phase`** -- `xiAmplitude(s,x)/sqrt(xi_s(x)) = ampFourth(s,x)`, an
    identity by definition.  This is why the composition introduces no approximation at the amplitude
    step: the amplitude that falls out of the Bessel asymptotic *is* the leading amplitude the card
    and the corpus both use.
  * **`abs_radialProlateBesselProfile_sub_twoBranch_le`** -- **the expansion**:

    `| radialProlateBesselProfile s c x
        - ampFourth(s,x) (A cos(c xi_s(x)) + B sin(c xi_s(x))) |
       <= ampFourth(s,x) * 2 sqrt(E(a) exp(1/(4a))) / (4a)`,   `a = c xi_s(x_0)`,

    with `A = besselCosCoeff a`, `B = besselSinCoeff a`, valid for all `x >= x_0 > 1`.

  The remainder is `ampFourth(s,x)` times a constant over `a = c xi_s(x_0)` -- relative `O(1/c)`,
  uniform in `x`, and one full power better than the corpus's fourth-root bridge.  That is the rate
  the fifty-sixth instalment identified as required for `(16)`, and it is now proved rather than
  assumed.

  So `(13)`'s shape is established for the profile: two branches, the amplitude is `ampFourth`
  (whose `(14)` bounds are the forty-ninth instalment), and the error is relative `O(1/c)`.  What
  the exterior estimate consumes is the amplitude *of each branch* together with its derivative;
  the branch amplitudes here are the constants `A` and `B`, so their derivatives vanish and the
  `(14)` bounds reduce to those already proved for `ampFourth`.

- 2026-08-09 (sixty-fourth instalment) -- **The integrated two-branch remainder is `O(1/c)`,
  uniformly in the endpoint.**  Four theorems added to `RHTower/ProlateTwoBranch.lean`; wired,
  axiom-clean.

  * **`continuousOn_ampFourth_Ioi`** -- continuity of the leading amplitude, from its derivative.
  * **`hasDerivAt_neg_two_div_sqrt`, `integral_inv_x_mul_sqrt_le`** -- the `x^(-3/2)` tail:
    `int_2^X dx/(x sqrt x) <= 2`.
  * **`abs_integral_profile_sub_twoBranch_le`** --

    `| int_2^X (profile(x) - twoBranch(x)) / sqrt x dx |
       <= 4 * 2 sqrt(E(a) exp(1/(4a))) / (4a)`,   `a = c xi_s(x_0)`,

    for `1 < x_0 <= 2 <= X`.

  The polar weight is what makes this converge, and it is not an artefact of the estimate: the card's
  `(12)` carries `dx/sqrt x` intrinsically.  The `ampFourth` factor contributes `x^(-1)` and the
  weight the remaining half power, giving an exactly integrable `x^(-3/2)`.  Without the weight the
  same remainder would only integrate to `O(log X)`.

  So the remainder of the two-branch expansion contributes `O(1/c)` to the primitive, uniformly in
  the endpoint -- the same order as the main term's own bound.  Combined with
  `norm_integral_leading_channel_le`, which handles the leading term at rate `O(1/(c k^2))`, the
  exterior channel estimate `(16)` is now supported at both ends: leading term and remainder.

- 2026-08-09 (sixty-fifth instalment) -- **`(13)` as an exact identity, which is what the card
  actually states.**  One theorem added to `RHTower/ProlateTwoBranch.lean`; wired, axiom-clean.

  * **`radialProlateBesselProfile_eq_twoBranch`** --

    `radialProlateBesselProfile s c x
       = ampFourth(s,x) (A(c xi_s(x)) cos(c xi_s(x)) + B(c xi_s(x)) sin(c xi_s(x)))`,

    for `1 < x`, `c > 0`, `0 <= s <= 1/2`.  **Exactly** -- no remainder.

  A correction of emphasis, found by re-reading `(13)` against what I had built.  The sixty-third
  instalment produced a leading term plus an `O(1/c)` remainder, by freezing the coefficients at a
  base point.  But `(13)` is not stated that way: it is an identity, `U_(lambda,k)` *equals* the
  two-branch sum, with all the content pushed into amplitudes satisfying `(14)`.  Evaluating the
  coefficients at the running phase instead of freezing them gives exactly that, and the proof is
  three rewrites -- the identity was already available in
  `besselNormalForm_eq_coeff` from the sixtieth instalment.

  Why this matters rather than being a restatement: with a frozen-coefficient expansion the remainder
  is bounded absolutely, so it contributes `O(1/(c k))` to the channel primitive and *dominates* the
  leading term's `O(1/(c k^2))`.  With the exact identity there is no remainder to dominate anything;
  the whole integrand is oscillatory and the integration by parts applies to all of it, so both
  factors of `k` survive.  The frozen form was the wrong object, and the sixty-fourth instalment's
  remainder bound, while correct, is not on the path to `(16)`.

  What `(16)` now needs is `(14)` for these running amplitudes: `ampFourth(s,kx) A(c xi_s(kx))` and
  its derivative.  The amplitude bound is immediate from `ampFourth_dilate_le` and
  `besselCoeff_sq_add`; the derivative needs `A'(u) = q(u) w(u) sin u` composed with the chain rule,
  which is the sixtieth instalment's formula.

- 2026-08-09 (sixty-sixth instalment) -- **The branch amplitudes and their derivatives.**  Three
  theorems added to `RHTower/BesselNormalForm.lean`; wired, axiom-clean.

  * **`abs_besselCoeff_le_sqrt_energy`** -- `|A(u)|, |B(u)| <= sqrt(E(u))`, immediate from
    `A^2 + B^2 = E`.
  * **`abs_besselCoeff_le_base`** -- hence both are bounded on `[a, infinity)` by
    `sqrt(E(a) exp(1/(4a)))`, using the Grönwall bound.
  * **`abs_deriv_besselCoeff_le_base`** -- both derivatives are at most
    `(1/(4u^2)) sqrt(E(a) exp(1/(4a)))`, since `A' = q w sin u` and `|w|` is bounded by the same
    budget.

  These are `(14)`'s two halves for the running amplitudes of the exact representation: the amplitude
  is bounded by a constant and its derivative decays like `u^(-2)`.  Composed with `ampFourth`
  (bounded by `2/x`, derivative by `32/x^2`) and the phase `u = c xi_s(k x)` (speed at most `2`,
  and `u >= c k x/2`), the channel amplitude `ampFourth(s,kx) A(c xi_s(kx))` satisfies `(14)` with
  constant `O(1/k)` -- the same `1/k` the fifty-third instalment derived for the leading form, now
  for the exact one.

  Everything `(16)` needs is therefore proved in pieces: the exact identity (sixty-fifth), the
  amplitude bounds here, the dilated phase and its reciprocal-speed variation (forty-seventh), and
  the two-constant exterior estimate (fifty-first).  What is left is the composition, which is
  differentiation of a product and substitution -- no new estimate.

- 2026-08-09 (sixty-seventh instalment) -- **The branch coefficient along the dilated phase.**  Four
  theorems added to `RHTower/ProlateTwoBranch.lean`; wired, axiom-clean.

  * **`xiSpeed_le_two`** -- the exterior phase speed is at most `2` for `t >= 2`.  The companion to
    `one_le_xiSpeed`: the speed is pinned between `1` and `2` on the whole exterior range.
  * **`hasDerivAt_scaled_dilated_phase`** -- `d/dx [c xi_s(k x)] = c k xi_s'(k x)`.
  * **`hasDerivAt_besselCosCoeff_comp`** -- the branch coefficient differentiated along that phase.
  * **`abs_deriv_besselCosCoeff_comp_le`** -- **the drift bound**:

    `| d/dx A(c xi_s(k x)) | <= 2 sqrt(E(a) exp(1/(4a))) / (c k x^2)`.

  Three factors of the dilation cancel to leave one in the denominator: the chain rule contributes
  `c k` upward, the phase lower bound `xi_s(k x) >= k x/2` contributes `(c k x)^(-2)` downward, and
  the net is `(c k x^2)^(-1)`.  So the running amplitude drifts *less* for higher channels, not more
  -- which is why the exact representation keeps both factors of `k` where the frozen one lost them.

  This is the last estimate `(14)` needs for the exact channel amplitude.  What remains is assembling
  `ampFourth(s,kx) A(c xi_s(kx))` by the product rule from this and the forty-ninth instalment's
  `ampFourth` bounds.

- 2026-08-09 (sixty-eighth instalment) -- **The exact channel amplitude.**  Two definitions and two
  theorems added to `RHTower/ProlateTwoBranch.lean`; wired, axiom-clean.

  * **`channelAmplitude`, `channelAmplitudeDeriv`** -- `ampFourth(s,kx) A(c xi_s(kx))` and its
    derivative, the cosine branch's amplitude in the exact representation.
  * **`hasDerivAt_channelAmplitude`** -- differentiability, by the product rule against the dilated
    `ampFourth` derivative and the sixty-seventh instalment's composed drift.
  * **`abs_channelAmplitude_le`** -- `|alpha(x)| <= 2 sqrt(E(a) exp(1/(4a))) / (k x)`.

  The amplitude bound carries the `1/k` outright, with no oscillatory argument: it comes from
  `ampFourth(s,kx) <= 2/(kx)`, i.e. purely from the dilation of the argument.  That is `(13)`'s
  prefactor, derived rather than posited, and now for the *exact* amplitude rather than the leading
  one.

  Note the hypothesis `0 < c` turned out to be unnecessary for this bound and was removed -- the
  amplitude estimate does not see the frequency at all; only the drift estimate does.

- 2026-08-09 (sixty-ninth instalment) -- **`(14)` is complete for the exact channel amplitude.**  One
  theorem added to `RHTower/ProlateTwoBranch.lean`; wired, axiom-clean.

  * **`abs_channelAmplitudeDeriv_le`** --

    `| alpha'(x) | <= 36 sqrt(E(a) exp(1/(4a))) / k / x^2`,   `c >= 1`, `k >= 1`, `x >= 2`.

  With the sixty-eighth instalment's `|alpha(x)| <= 2 M/(k x)`, both halves of `(14)` now hold for
  the exact channel amplitude `ampFourth(s,kx) A(c xi_s(kx))`, with constant `O(M/k)`.

  The product rule splits into two terms and they are bounded by different mechanisms.  The first,
  `k ampFourth'(kx) A`, is `O(M/(k x^2))` because the dilated amplitude derivative already carries
  `1/k`.  The second, `ampFourth(kx) dA/dx`, is `O(M/(c k^2 x^3))` -- smaller by a further `1/(ckx)`
  -- because the branch coefficient barely drifts.  Only the first term matters, which is the precise
  sense in which the two-branch representation is "almost" a fixed sinusoid with a slowly varying
  envelope.

  Every ingredient of `(16)` is now proved: the exact identity, both `(14)` bounds for the exact
  amplitude, the dilated phase with its speed and reciprocal-speed variation, and the two-constant
  exterior estimate whose conclusion is linear in the amplitude constant.

- 2026-08-09 (seventieth instalment) -- **The channel amplitude in the exterior estimate's
  normalization.**  Two definitions and three theorems added to `RHTower/ProlateTwoBranch.lean`;
  wired, axiom-clean.

  * **`channelAmp`, `channelAmpDeriv`** -- `sqrt x * alpha(x)`, the form the exterior estimate
    consumes, and its derivative.
  * **`hasDerivAt_channelAmp`** -- differentiability.
  * **`abs_channelAmp_le`** -- `‖a(x)‖ <= (37 M/k) / sqrt x`.
  * **`abs_channelAmpDeriv_le`** -- `‖a'(x)‖ <= (37 M/k) / (x sqrt x)`.

  Both hold with the *same* constant `C_a = 37 M/k`, which is what
  `norm_integral_exterior_dilated_sharp_le` requires: it takes one amplitude constant and returns
  `3 C_a/(c k)`.  With `C_a = 37M/k` that is `111 M/(c k^2)` -- `(16)`.

  A tactic note, since three of the five proofs here needed it.  Goals of the form
  `sqrt x * (A / x) = A / sqrt x` do not close with `field_simp; linarith [hss]`, because `field_simp`
  leaves `sqrt x ^ 2` while `hss` is stated with `*`.  Supplying `hsq2 : sqrt x ^ 2 = x` and using
  `linear_combination A * hsq2` closes them immediately, and `linear_combination (0) * hsq2` prints
  the coefficient when it is not obvious.

- 2026-08-09 (seventy-first instalment) -- **`(16)` closed, with a channel-uniform constant.**
  Seven declarations added to `RHTower/ProlateTwoBranch.lean`; all axiom-clean.

  * **`continuousOn_channelAmplitudeDeriv`, `continuousOn_channelAmpDeriv`** -- the last plumbing
    the exterior estimate wanted.  The derivative is a sum of eight composed factors; each is
    continuous on the channel range, and the two Bessel factors compose through
    `besselCosCoeff`/`besselNormalForm` on `Ioi 0` via the phase, which is positive there.
  * **`channelBase`, `channelBase_pos`, `channelBase_le`** -- the inner edge `c xi_s(2k)` of the
    channel.  Monotonicity of the phase gives `channelBase <= c xi_s(kx)` for every `x >= 2`, so a
    single energy constant serves the whole range of integration.
  * **`norm_integral_channel_le`** -- `(16)`.  Substituting `C_a = 37 M/k` into
    `norm_integral_exterior_dilated_sharp_le` gives `3 C_a/(ck) = 111 M/(c k^2)`.
  * **`channelEnergyConstant`, `channelBase_mono`, `channelEnergy_le`,
    `norm_integral_channel_uniform_le`** -- the constant made uniform in the channel index.

  The uniformity is worth stating separately, because it is the only reason the channels sum.
  `M(k) = sqrt(besselEnergy(b_k) exp(1/(4 b_k)))` depends on `k` through the base point
  `b_k = c xi_s(2k)`, which *increases* with `k`.  What `besselEnergy_le_exp` actually proves is
  that `u |-> besselEnergy u * exp(1/(4u))` is **antitone** -- that is its Gronwall content, read
  as a monotone statement rather than as an inequality between two points.  So the increasing
  base point makes `M(k)` decreasing, and `M(k) <= M(1) = channelEnergyConstant s c` for every
  `k >= 1`.  The channel bound is therefore `111 C/(c k^2)` with `C` free of `k`, and
  `sum_k 1/k^2` converges.

  Had the energy grown with the base point instead, no amount of decay in `k` from the amplitude
  would have helped -- the `1/k^2` would have been fighting an unknown growth.  The direction of
  that monotonicity is the whole of the summability.

- 2026-08-09 (seventy-second instalment) -- **`(11)`: the channels summed.**  Two new modules,
  both wired, all declarations axiom-clean; the `HTGeometry` umbrella is green.

  `HTGeometry/InverseSquareTailSum.lean`
  * **`tsum_inv_sq_shift_two_le_one`** -- `sum_{n>=0} 1/(2+n)^2 <= 1`.
  * **`tsum_inv_sq_shift_one_le_two`** -- `sum_{n>=0} 1/(1+n)^2 <= 2`.

  `RHTower/ProlateChannelSum.lean`
  * **`channelMajorant`, `channelMajorant_eq`, `channelMajorant_nonneg`,
    `summable_channelMajorant`, `tsum_channelMajorant_le`** -- the majorant `B/(c(k+1)^2)` and its
    sum `<= 2B/c`.
  * **`norm_inner_le_of_channel_bounds`** -- a channel-by-channel bound on the pairing passes to
    any norm limit of the truncations, with the single constant `2B/c`.
  * **`iSup_norm_inner_le_of_channel_bounds`** -- the same uniformly in the endpoint.  This is the
    shape of `(11)`.

  Three things are worth recording.

  First, `pi` was avoided deliberately.  mathlib has `hasSum_zeta_two`, so `sum 1/j^2 = pi^2/6` is
  available and the tail is exactly `pi^2/6 - 1`.  But bounding that by `1` needs `pi^2 <= 12`, and
  the sharpest bound on `pi` in this toolchain is `Real.pi_lt_four`, giving only `pi^2 < 16`.  The
  exact value is therefore useless here; a telescoping comparison gives the explicit constants with
  no transcendental input at all.

  Second -- and this is the part that cost a rebuild -- **the corpus already owned the telescoping
  sum.**  `HTGeometry/TrigammaLeadingAsymptotic.lean` proves
  `hasSum_one_div_shift_mul_succ : HasSum (fun n => 1/((s+n)(s+n+1))) (1/s)`, and
  `HTGeometry/VerticalShiftTailEstimate.lean` proves `summable_inv_sq_shift` for a general shift.
  I first wrote both by hand as induction on partial sums; `lake env lean` accepted the file, and
  only the *umbrella* build reported the collision on `summable_inv_sq_shift`.  This is the failure
  mode where a per-file check cannot see a duplicate: the file compiles because it does not import
  the module it duplicates.  The rewrite derives both constants from the corpus telescoping sum in
  a third of the lines.

  Third, the two comparisons are genuinely different and my first attempt conflated them.  For the
  tail the summand `1/(2+n)^2` sits at the *right* end of the telescoped pair
  `1/((1+n)(2+n))`, and `(1+n)(2+n) <= (2+n)^2` gives it.  For the series itself the summand
  `1/(1+n)^2` sits at the *left* end, where `(1+n)(2+n) <= (1+n)^2` is false; one needs the factor
  `2`, comparing against `2/((1+n)(2+n))`, which works because `2+n <= 2(1+n)`.  That is why the
  two constants are `1` and `2`.

  A tooling note: probing mathlib names with `have := @Name` gives false negatives for anything
  carrying a `SummationFilter` argument -- `HasSum.tsum_eq`, `tsum_mul_left`,
  `Summable.tsum_le_tsum` all reported missing and all exist.  `#check @Name` is the reliable probe.

  The order of passage is the card's: sum the channels at a fixed endpoint, then take the limit of
  the truncations, then the supremum over endpoints.  `ciSup_le` performs the last step, so no
  interchange of an infinite channel sum with an improper primitive appears anywhere.

- 2026-08-09 (seventy-third instalment) -- **`(16)` for the whole profile, both branches.**  New
  module `RHTower/ProlateChannelBranch.lean`, wired, all declarations axiom-clean.

  The seventy-first instalment closed `(16)` for the *cosine* amplitude only.  The exact two-branch
  representation has two coefficients, and dropping the sine one is not a harmless simplification:
  `A cos u + B sin u` is not `A cos u` plus something small -- `B` is the same size as `A`.  This
  instalment covers both.

  **The generic branch layer.**  Both coefficients obey the same two bounds -- bounded by the
  energy, derivative bounded by the energy times `1/(4u^2)` -- and those two bounds are *all* the
  amplitude estimates use.  So the layer is built once for an arbitrary coefficient `A` with
  derivative `A'` and instantiated at both:
  * **`branchAmplitude`, `branchAmplitudeDeriv`, `hasDerivAt_branchAmplitude`**;
  * **`abs_branchAmplitude_le`** (`<= 2M/k/x`), **`abs_branch_drift_le`** (`<= 2M/(c k x^2)`),
    **`abs_branchAmplitudeDeriv_le`** (`<= 36M/k/x^2`);
  * **`branchAmp`, `branchAmpDeriv`, `hasDerivAt_branchAmp`, `abs_branchAmp_le`
    (`<= 2M/k/sqrt x`), `abs_branchAmpDeriv_le` (`<= 37M/k/(x sqrt x)`)**;
  * **`continuousOn_branchAmplitudeDeriv`, `continuousOn_branchAmpDeriv`**.

  This replaced roughly 250 lines of prospective duplication with one instantiation each.

  **The complex branch.**
  * **`besselCosCoeffDeriv`, `besselSinCoeffDeriv`** and their continuity on `Ioi 0`.
  * **`channelBranchAmp`, `channelBranchAmpDeriv`** -- `(1/2)(P - eps i Q)`, the complex amplitude
    of one exponential branch, with `P` and `Q` the two real branch amplitudes.
  * **`hasDerivAt_channelBranchAmp`, `continuousOn_channelBranchAmp`,
    `continuousOn_channelBranchAmpDeriv`, `abs_channelBranchAmp_le` (`<= 2M/k/sqrt x`),
    `abs_channelBranchAmpDeriv_le` (`<= 37M/k/(x sqrt x)`)** -- both with the *same* constant
    `C_a = 37M/k`, which is what the exterior estimate requires.

  **The identity and the capstone.**
  * **`two_branch_euler`** -- `P cos u + Q sin u = (1/2)(P - iQ)e^{iu} + (1/2)(P + iQ)e^{-iu}`.
  * **`sqrt_mul_radialProlateBesselProfile_eq_branches`** -- the exact decomposition of the dilated
    profile.  No error term: `radialProlateBesselProfile_eq_twoBranch` is an identity and so is
    Euler's.
  * **`profile_eq_branch_integrand`, `continuousOn_branchIntegrand`, `continuousOn_dilatedPhase`.**
  * **`norm_integral_dilated_profile_le`** -- `<= 222 C/(c k^2)` with `C = channelEnergyConstant s c`,
    free of `k` and of the endpoint.  This is `(16)` for the full profile.

  Two tactic notes.

  `field_simp` must not be applied to a goal whose atoms are `Complex.exp` applications.  It
  renormalises the *arguments* of `exp` -- `1 * (c*k) * phi` became `1 * c * k * phi` on one side and
  `k * c * phi` on the other -- and since `ring` treats `exp e` as an atom keyed on the syntactic
  form of `e`, the two stop matching and the goal becomes unprovable by `ring`.  The fix is to
  divide by hand: rewrite the target as `(sqrt t)^{-1} * (sqrt t * profile)`, substitute the
  identity, and let `ring` work with the exponentials untouched.

  Second, `field_simp` followed by `linear_combination` needs the coefficient read off, not
  guessed, and the guess is systematically wrong here: for both
  `sqrt x * (2M/k/x) = 2M/k/sqrt x` and `sqrt x * (36M/k/x^2) = 36M/k/(x sqrt x)` the residual
  coefficient is plain `M`, not `2M/k` or `36M/k` -- `field_simp` clears the `k` before the
  `sqrt x^2 - x` factor is exposed.

- 2026-08-09 (seventy-fourth instalment) -- **The energy method, abstracted off Bessel.**  Two new
  modules, both wired, all declarations axiom-clean.

  **Why.**  `norm_integral_dilated_profile_le` closes `(16)` for the Bessel *model*
  `radialProlateBesselProfile`.  Getting from there to the exact mode `R` needs the model-to-mode
  transfer, and an audit of what the corpus offers shows neither available bound suffices:

  * `abs_radialProlate_sub_besselProfile_le` is sharp in `c` (error `O(1/c)`) but decays only like
    `x^{-1}` in the variable, so integrating `|error|` over `[2, X]` gives `O(log X / c)` -- *not*
    uniform in the endpoint, which is what `(16)` demands;
  * `abs_profile_sub_model_decay_le` is integrable in `x` (`O(x^{-5/4})`) but only `O(c^{-1/4})`.

  Neither yields `O(1/(c k^2))`.  This is not a gap in the assembly: it says the transfer error
  cannot be estimated in absolute value at all.  It has to be handled the same way the main term
  is -- by exhibiting the exact two-branch representation of the *mode*, not of the model.

  **What was built.**  `HTGeometry/PerturbedOscillator.lean` -- the energy method for
  `w'' + (1 + q(u)) w = 0` with `|q(u)| <= kappa/u^2`, with no reference to any particular equation:
  * **`oscEnergy`, `oscEnergy_nonneg`, `hasDerivAt_oscEnergy`** (`E' = -2 q w w'`);
  * **`abs_deriv_oscEnergy_le`** (`|E'| <= (kappa/u^2) E`, by AM-GM);
  * **`hasDerivAt_const_div`, `oscEnergy_le_exp`** -- Gronwall, via antitonicity of
    `E(v) exp(kappa/v)`;
  * **`oscCosCoeff`, `oscSinCoeff`, `osc_eq_coeff`, `oscCoeff_sq_add`** -- the exact
    representation and `A^2 + B^2 = E`;
  * **`hasDerivAt_oscCosCoeff`** (`A' = q w sin u`), **`hasDerivAt_oscSinCoeff`**
    (`B' = -q w cos u`);
  * **`abs_osc_le`, `abs_oscCoeff_le_base`, `abs_deriv_oscCoeff_le_base`** -- envelope, coefficient
    bounds, and the `kappa/u^2` drift.

  `RHTower/BesselOscillatorInstance.lean` -- the instantiation, as a check that this is a
  generalization and not a parallel development.  **`oscEnergy_bessel`, `oscCosCoeff_bessel`,
  `oscSinCoeff_bessel` all hold by `rfl`**: the abstract energy and the abstract coefficients *are*
  `besselEnergy`, `besselCosCoeff`, `besselSinCoeff`, not merely equal to them.
  **`bessel_isPerturbedOscillator`** discharges all four hypotheses with `kappa = 1/4`, and
  **`besselEnergy_le_exp_of_abstract`** reads the abstract Gronwall bound back on the Bessel energy.

  The abstract layer is what the exact mode needs.  In the Liouville-Green variable the prolate
  mode satisfies an equation of exactly this shape with `u = c xi_s(x)`, and the corpus already has
  the change of variable (`comparisonSol`, `lgAmplitude`, `lgNormalFormDefect`, and
  `hasDerivAt_comparisonSolDeriv`, which produces `U'' = -P U' - (c^2 (xi')^2 + a) U`).  What is
  still missing between that and the abstract interface is the removal of the first-order term `P`
  and the verification that the resulting perturbation is `O(1/u^2)` -- named precisely, rather
  than left as "the transfer".

- 2026-08-09 (seventy-fifth instalment) -- **The energy method in a general phase parameterization.**
  New module `HTGeometry/PerturbedOscillatorPhase.lean`, wired, all declarations axiom-clean.

  The previous instalment built the energy method for `w'' + (1 + q(u))w = 0` as a function of the
  phase variable `u`.  Applying it to the prolate mode would require inverting `xi_s`, i.e.
  constructing `x(u)` and transporting every derivative through it.  That inverse exists in the
  corpus (`XiInverseCoordinate`), but using it is the wrong move: the change of variables never has
  to be performed.

  Instead the whole theory is restated in the *original* variable with the phase carried as data.
  Write `Dw = w'/phi'` and `DDw = (Dw)'/phi'`.  Then every identity survives with one factor of
  `phi'` per differentiation:

  ```text
  E = w^2 + (Dw)^2,              E'  = -2 phi' q w Dw,
  A = w cos phi - Dw sin phi,    A'  =  phi' q w sin phi,
  B = w sin phi + Dw cos phi,    B'  = -phi' q w cos phi.
  ```

  * **`phaseEnergy`, `phaseEnergy_nonneg`, `hasDerivAt_phaseEnergy`, `abs_deriv_phaseEnergy_le`.**
  * **`phaseCosCoeff`, `phaseSinCoeff`, `phase_eq_coeff`, `phaseCoeff_sq_add`,
    `hasDerivAt_phaseCosCoeff`, `hasDerivAt_phaseSinCoeff`.**
  * **`phaseEnergy_le_exp`** -- Gronwall.  The drift integrates to `kappa/phi` because
    `integral phi' kappa/phi^2 = kappa/phi`; that is the whole reason a `phi^{-2}` perturbation is
    admissible and a `phi^{-1}` one is not.
  * **`abs_phase_le`, `abs_phaseCoeff_le_base`, `abs_deriv_phaseCoeff_le_base`.**

  The hypotheses are stated on `{x : a <= x}` with two-sided `HasDerivAt`, which is what the prolate
  mode supplies on any `[A_c, infinity)` with `A_c > 1`; no one-sided derivative machinery is needed.

  What this layer changes about the route: the exact mode's two-branch representation is now a
  matter of exhibiting `w`, `Dw`, `DDw`, `q` in the `x` variable with `|q| <= kappa/(c xi_s)^2`, and
  the corpus already carries the normal-form substitution (`prolateNormalFormSol`) and the
  comparison equation.  Nothing in the remaining step involves a coordinate change.

- 2026-08-09 (seventy-sixth instalment) -- **The exact radial mode is a perturbed oscillator.**
  New module `RHTower/ProlateLiouvilleOscillator.lean`, wired, all declarations axiom-clean.

  This is the step the previous two instalments were building toward: the exact mode `R`, not the
  Bessel model, put into the shape the energy method consumes.

  * **`prolatePhase`, `prolatePhaseSpeed`, `prolatePhaseAccel`** and their `HasDerivAt` lemmas --
    `phi = c xi_s`, `phi' = c xi'`, `phi'' = c xi''`.
  * **`lgSpeedAmp`, `lgSpeedAmpDeriv`, `lgSpeedAmpSecond`, `hasDerivAt_lgSpeedAmp`,
    `hasDerivAt_lgSpeedAmpDeriv`** -- the Liouville amplitude `h = sqrt(phi')` and its two
    derivatives.
  * **`two_mul_lgSpeedAmpDeriv_mul_speed`** -- `2 h' phi' = h phi''`.  One line of algebra, and it
    is the entire reason the construction works: it is exactly the coefficient of `u'` in the
    transformed equation, so the first-order term is eliminated *identically*, not approximately.
  * **`prolateOsc`, `prolateOscD`, `prolateOscDD`, `hasDerivAt_prolateOsc`,
    `hasDerivAt_prolateOscD`** -- `w = h u`, `Dw = w'/phi'`, `DDw = (Dw)'/phi'`, with the two
    derivative laws in exactly the form `PerturbedOscillatorPhase` requires.
  * **`prolateOscPotential`, `prolateOsc_ode`** -- `DDw + (1 + q) w = 0`, unconditionally, given
    only the radial prolate equation.

  Three things made this tractable.

  First, the corpus already owned everything needed and I nearly rebuilt two of them.
  `prolate_normalForm_ode` gives `u'' + Q u = 0` for `u = sqrt(x^2-1) R`; `radialProlateQ` is the
  potential; and `radialProlateQ_sub_comparison` proves `Q - c^2 (xi')^2 = 1/(x^2-1)^2` -- a pure
  pole, exactly as my own derivation had predicted.  `xiSpeedSecondDeriv` is `xi'''`, which the
  Liouville error term needs and which I had assumed was missing; its docstring says it exists
  precisely to identify the defect.

  Second, the phase parameterization was the right abstraction.  Nothing here inverts `xi_s`.

  Third, on `linear_combination` coefficients, the same lesson a third time: after `field_simp` the
  residual of the ODE identity is `u' (2 h' phi' - h phi'')`, so the coefficient is `u'` -- plain
  `prolateNormalFormSolDeriv R DR x`, with no factor from anywhere else.  Printing it with
  `linear_combination (0) * hamp` took one round trip; guessing would have taken several.

  What remains for the exact-mode `(16)` is the *bound* `|q| <= kappa/phi^2`, i.e. an estimate on
  `lgSpeedAmpSecond` and on the pole term `1/(x^2-1)^2`.  The structure is now fixed; only sizes
  are left.

- 2026-08-09 (seventy-seventh instalment) -- **The exact mode's two-branch coefficients, bounded.**
  Eight further declarations in `RHTower/ProlateLiouvilleOscillator.lean`; all axiom-clean.

  * **`prolateOscPotential_eq`** -- the perturbation in closed form:

    ```text
    q = 1/(c^2 (xi')^2 (x^2-1)^2) + (3 (xi'')^2 - 2 xi''' xi')/(4 c^2 (xi')^4).
    ```

    The first term is the pole of the normal-form potential, the second is the Liouville
    (Schwarzian) error.  Both carry `1/c^2`.
  * **`abs_xiSpeedDeriv_le_two_div`** (`|xi''| <= 2/x^3`) and **`abs_xiSpeedSecondDeriv_le`**
    (`|xi'''| <= 32/x^4`).
  * **`abs_prolateOscPotential_le`** -- `|q| <= 35/phi^2` on `[2, infinity)`.
  * **`prolate_isPhaseOscillator`** -- all seven hypotheses of the abstract layer, discharged.
  * **`abs_prolateOscCoeff_le`** -- both branch coefficients of the *exact mode* bounded by the
    square root of its energy budget.

  This is what the two absolute-value routes could not give.  `q` decays like `x^{-4}` while the
  budget allows `phi^{-2} ~ x^{-2}`, so the drift is integrable with two powers to spare -- and the
  resulting statement is about `R` itself, with no model-to-mode transfer and hence no transfer
  error.  The `O(log X / c)` divergence identified in the seventy-fourth instalment does not arise
  because nothing is ever bounded in absolute value: the mode is *represented*, not approximated.

  Constants, for the record: `|q| <= 2/(c^2 x^4)` from the pole and `<= 33/(c^2 x^4)` from the
  Schwarzian, and `phi <= c x` from `xiEndpointPhase_bounds`, giving `35`.

  Two traps, both previously logged and both hit again.

  A heredoc append lands *after* `end Namespace`, so every identifier in it becomes an
  `autoImplicit` variable and the errors read as "unknown identifier `xiSpeed`".  The fix is to
  splice before the marker; the symptom is unmistakable once seen.

  `rw [show x = Real.sqrt (x^2) from ...]` rewrites *every* occurrence of `x`, including the ones
  inside `x^2 - 1`, turning `sqrt (x^2-1) <= x` into an unprovable goal.  Going forward through
  `Real.sqrt_le_sqrt` and then `Real.sqrt_sq` on the hypothesis avoids touching the goal at all.

- 2026-08-09 (seventy-eighth instalment) -- **The exact mode's envelope.**  New module
  `RHTower/ProlateExactChannel.lean`, wired, all declarations axiom-clean.

  * **`prolateEnvelope`, `prolateEnvelopeDeriv`, `hasDerivAt_prolateEnvelope`** --
    `envelope = 1/(h sqrt(x^2-1))`, the factor that converts the oscillator back into the mode.
  * **`sqrt_c_le_lgSpeedAmp`** (`sqrt c <= h`) and **`lgSpeedAmp_le_sqrt_two_c`**
    (`h <= sqrt(2c)`) -- the amplitude is pinned between two multiples of `sqrt c` because
    `1 <= xi' <= 2`.
  * **`radialProlate_eq_branches`** -- **`R = envelope * (A cos phi + B sin phi)`**, an identity.
    The oscillator representation is exact and the rescaling is invertible, so there is nothing to
    estimate here at all.
  * **`abs_lgSpeedAmpDeriv_le`** (`|h'| <= sqrt c / x^3`), **`prolateEnvelope_le`**
    (`<= 2/(sqrt c x)`), **`abs_prolateEnvelopeDeriv_le`** (`<= 16/(sqrt c x^2)`).

  A correction to my own arithmetic, made while proving it.  I first stated the envelope-derivative
  bound as `5/(sqrt c x^2)` from a rough count.  It is false at that constant: the honest chain is
  numerator `<= 4 sqrt c` (from `|h'| sqrt(x^2-1) <= sqrt c` and `h * x/sqrt(x^2-1) <= 3 sqrt c`)
  over denominator `>= c x^2/4`, giving `16/(sqrt c x^2)`.  The `x^2/4` in the denominator comes
  from using the crude `sqrt(x^2-1) >= x/2`; the sharp `sqrt 3 x/2` would give `16/3`, but the crude
  bound keeps every step inside `nlinarith`'s reach and the constant is irrelevant downstream.
  Two of the three sub-bounds also needed `sqrt(2c) <= (3/2) sqrt c` rather than the lazier
  `<= 2 sqrt c`, since `2 * 2 = 4 > 3`.

  What remains for the exact-mode `(16)`: dilate by `k`, complexify the two branches as in
  `ProlateChannelBranch`, and apply `norm_integral_exterior_dilated_sharp_le`.  Every input is now
  a proved theorem -- the identity, both coefficient bounds, both envelope bounds, and the
  coefficient drift.

- 2026-08-09 (seventy-ninth instalment) -- **The dilated channel amplitude of the exact mode.**
  Seven further declarations in `RHTower/ProlateExactChannel.lean`; all axiom-clean.

  * **`exactAmplitude`, `exactAmplitudeDeriv`, `exactAmp`, `exactAmpDeriv`,
    `hasDerivAt_exactAmplitude`, `hasDerivAt_exactAmp`** -- the envelope times an arbitrary branch
    coefficient, dilated by `k` and normalized by `sqrt x`.
  * **`abs_exactAmp_le`** -- `<= 300 M/(sqrt c k)/sqrt x`.
  * **`abs_exactAmpDeriv_le`** -- `<= 300 M/(sqrt c k)/(x sqrt x)`, the *same* constant, which is
    what `norm_integral_exterior_dilated_sharp_le` requires.
  * **`prolate_drift_le`** -- the bridge that makes the derivative bound usable:
    `phi' * (35/phi^2) <= 280/(c y^2)`, because the phase speed is at most `2c` and the phase at
    least `c y/2`.

  The derivative bound splits into three terms and it is worth recording their sizes, because the
  third is the only one that needed the `1/c` from the drift:

  * `sqrt x` differentiated: `M/(sqrt c k x sqrt x)`;
  * the envelope differentiated: `16 M/(sqrt c k x sqrt x)`;
  * the coefficient differentiated: `560 M/(sqrt c c k^2 x^2 sqrt x)`, which is
    `<= 280 M/(sqrt c k x sqrt x)` only because `c k x >= 2`.

  Total `297`, rounded to `300`.  The third term is where the perturbation bound `|q| <= 35/phi^2`
  actually gets used, and it is the term that would have been unbounded had the transfer error been
  estimated in absolute value.

  With the normalization `sqrt c R`, the exterior estimate will give `3 C_a/(ck)` with
  `C_a = 300 M/(sqrt c k)`, i.e. `900 M/(sqrt c c k^2)`, and the `sqrt c` from the normalization
  turns this into `900 M/(c k^2)` -- `(16)` for the exact mode.

  Same `linear_combination` lesson once more, twice in one proof: after `field_simp` the residuals
  were `M (sqrt x^2 - x)` and `560 M (sqrt x^2 - x)`, i.e. the coefficient is whatever multiplies
  the term, never the compound constant that appears in the statement.

- 2026-08-09 (eightieth instalment) -- **The exact mode's channel: coefficients, drift, and the
  continuity layer.**  Sixteen further declarations in `RHTower/ProlateExactChannel.lean`; all
  axiom-clean.

  * **`exactCosCoeff`, `exactSinCoeff`, `exactCosCoeffDeriv`, `exactSinCoeffDeriv`,
    `exactEnergyBudget`** and the two `hasDerivAt` lemmas -- the branch coefficients of the exact
    mode and their derivatives, named so the estimate can quantify over them.
  * **`abs_exactCoeff_le`** -- both coefficients bounded by the energy budget.
  * **`abs_exactCoeffDeriv_le`** -- both drifts bounded by `280 M/(c y^2)`, the exact hypothesis
    `abs_exactAmpDeriv_le` asks for.  This is where `prolate_drift_le` gets consumed.
  * **`sqrt_mul_radialProlate_dilate_eq`** -- `sqrt x R(kx)` as two real branches, by `ring` from
    `radialProlate_eq_branches`.
  * The continuity layer: **`continuousOn_xiSpeedSecondDeriv`,
    `continuousOn_prolateOscPotential`, `continuousOn_lgSpeedAmp`,
    `continuousOn_lgSpeedAmpDeriv`, `continuousOn_prolateEnvelope`,
    `continuousOn_prolateEnvelopeDeriv`, `continuousOn_exactCosCoeffDeriv`,
    `continuousOn_exactSinCoeffDeriv`.**

  The continuity of the perturbation is the one piece that could not be got from differentiability,
  since `q` is never differentiated.  It comes instead from the closed form `prolateOscPotential_eq`
  via `ContinuousOn.congr`: `q` is a rational expression in `xi'`, `xi''`, `xi'''` with denominators
  that are positive on `Ioi 1`, and the corpus already supplies the first two continuities.  Only
  `continuousOn_xiSpeedSecondDeriv` had to be built, and it comes straight from the quotient shape
  of the definition.

  This is why the closed form was worth proving as an identity rather than only as a bound: a bound
  on `q` would have given nothing at all here.

- 2026-08-09 (eighty-first instalment) -- **`(16)` PROVED FOR THE EXACT RADIAL MODE.**  Nine
  further declarations in `RHTower/ProlateExactChannel.lean`; all axiom-clean.

  ```text
  norm_integral_radialProlate_dilate_le :
    ‖∫ t in 2..X, R (k t)‖ <= 1800 * exactEnergyBudget s c R DR 2 / (sqrt c * (c * k^2))
  ```

  unconditionally, for every `X >= 2`, every `k >= 1`, every `c >= 1` and every `0 <= s <= 1/2`,
  given only that `R` solves the radial prolate equation.  With the card's `sqrt c` normalization
  this is `O(1/(c k^2))` uniformly in the endpoint -- the card's `(16)`, for the exact mode.

  * **`continuousOn_exactAmpDeriv`, `continuousOn_exactBranchAmp`,
    `continuousOn_exactBranchAmpDeriv`, `continuousOn_exactBranchIntegrand`.**
  * **`exactBranchAmp`, `exactBranchAmpDeriv`, `hasDerivAt_exactBranchAmp`.**
  * **`sqrt_mul_radialProlate_dilate_eq_branches`** -- the exact mode as two complex exponential
    branches.  Identity, not approximation.
  * **`abs_exactBranchAmp_le`, `abs_exactBranchAmpDeriv_le`** -- both `<= 300 M/(sqrt c k)` over
    `sqrt x` resp. `x sqrt x`, the same constant, which is what the estimate requires.
  * **`radialProlate_dilate_eq_branch_integrand`, `norm_integral_radialProlate_dilate_le`.**

  What this closes.  The seventy-fourth instalment recorded a genuine obstruction: the two
  available model-to-mode transfers give `O(log X / c)` (not uniform in the endpoint) and
  `O(c^{-1/4})` (not strong enough), so `(16)` could not be reached by estimating a transfer error
  in absolute value.  The route taken instead was to represent the mode itself:

  1. abstract the energy method off Bessel (`PerturbedOscillator`);
  2. restate it in a phase parameterization so no coordinate inversion is needed
     (`PerturbedOscillatorPhase`);
  3. put the prolate mode in that form, with the first-order term eliminated identically by
     `2 h' phi' = h phi''` (`ProlateLiouvilleOscillator`);
  4. bound the resulting perturbation, `|q| <= 35/phi^2`, using `xi'''` which the corpus already
     had;
  5. carry the representation through the envelope, the dilation and the complexification
     (`ProlateExactChannel`).

  No step estimates a difference between the mode and a model, because at no point is a model
  introduced.  That is the whole content of the eight instalments from the seventy-fourth to here.

  The constant `1800` is `2 branches * 3 * 300`, and the `300` is `1 + 16 + 280` from the three
  terms of the amplitude derivative, rounded.  It is uniform in `k` and in `X`; the only
  `c`-dependence beyond the stated powers is inside `exactEnergyBudget s c R DR 2`, which is the
  mode's own energy at the fixed base point `x = 2`.

- 2026-08-09 (eighty-second instalment) -- **The exterior channels summed, and item 6 corrected.**

  * **`tsum_norm_integral_radialProlate_channels_le`** --

    ```text
    sum_{k>=0} ‖integral_2^X R((k+1) t) dt‖ <= 2 (1800 M / sqrt c) / c,
    ```

    unconditionally, uniformly in `X >= 2`.  The whole radial object's exterior primitive is
    bounded by one constant.  This works only because `M = exactEnergyBudget s c R DR 2` is
    measured at the *fixed* base point `x = 2` and so does not depend on `k`; the `1/k^2` of `(16)`
    then does the rest through `channelMajorant`.

  **Item 6 of the Lean plan is corrected above.**  Its previous text said the channel expansion
  identity and the summation were what remained.  Both are now done, and the identity is stronger
  than the card asked for -- it is exact, with no error term, and about the mode rather than a
  model.  What actually remains is narrower and had not been named: the range `t in [1,2]` for
  `k >= 2`.  There `k t >= 2` so the representation applies unchanged, but
  `norm_integral_exterior_dilated_sharp_le` hard-codes `2` as its left endpoint.  Generalising it
  to an arbitrary `A >= 1` with `k A >= 2` is the remaining step, and it is a change to the
  estimate's statement, not new analysis.

  For `k = 1` that range is `(17)`, which has been an unconditional theorem since the sixty-ninth
  instalment.

- 2026-08-09 (eighty-third instalment) -- **The exterior estimate with a free left endpoint.**
  New module `RHTower/ExteriorGeneralEndpoint.lean` (root `RHTower` namespace), wired, all five
  declarations axiom-clean.

  * **`integral_inv_sq_le_left`** -- `integral_L^X t^{-2} <= 1/L`.
  * **`norm_integral_cexp_le_of_decay_left`** -- nonstationary phase over `[L, X]`: `<= 3K/L`.
  * **`norm_integral_cexp_le_of_profile_left`** -- with a scaled phase: `<= 3C/(L c)`.
  * **`norm_deriv_exteriorProfile_left`** -- the pointwise derivative bound from `x = 1` instead of
    `x = 2`; the tail `Ca Cr/x^3` is absorbed into `Ca Cr/x^2` rather than half of it, so the
    constant is `3Ca/2 + Ca Cr`.
  * **`norm_integral_exterior_left`** -- `<= 3 (Ca (3/2 + Cr))/(L c)`.

  Why this and not a `[1,2]` patch.  The eighty-second instalment identified the gap as "the range
  `t in [1,2]` for `k >= 2`", to be closed by splitting the integral.  That framing was the wrong
  one.  Substituting `y = k t`,

  ```text
  integral_1^X f(k t) dt = k^{-1} integral_k^{kX} f(y) dy,
  ```

  and the estimate over `[k, kX]` supplies a *second* factor `k^{-1}` through its left endpoint.
  So the `1/k^2` of `(16)` is `k^{-1}` from the Jacobian times `k^{-1}` from the endpoint -- and
  with the endpoint nailed to `2` only one of the two factors is ever visible.  Freeing it covers
  `[1, X]` in one estimate with no splitting at all, and no separate endpoint treatment for
  `k >= 2`.

  The existing `[2, X]` theorems are untouched; the general ones are added alongside, since other
  work depends on the fixed-endpoint forms.

- 2026-08-09 (eighty-fourth instalment) -- **The dilated estimate with a free left endpoint, and
  the amplitude bounds relaxed to match.**  New module
  `RHTower/ProlateDilatedLeftEndpoint.lean`, wired, axiom-clean.

  * **`abs_dilated_inv_speed_deriv_left`** -- `|k xiInvSpeedDeriv(k t)| <= 1/t^2` under
    `0 < t` and `2 <= k t`, replacing the old `2 <= t`.  The condition belongs on the *dilated*
    argument, not on the outer variable: that is the whole point of the dilation.
  * **`norm_integral_exterior_dilated_left`** -- `<= 15 Ca/(2 L (c k))` over `[L, X]`.

  Two lemmas in `ProlateExactChannel` were relaxed in place rather than duplicated:
  `abs_exactAmp_le` and `abs_exactAmpDeriv_le` now take `1 <= x` together with `2 <= k x` instead
  of `2 <= x`.  Nothing in their proofs used `2 <= x` for anything except deriving `2 <= k x` and
  `0 < x`, so the change is free; the one place that did use it, the step `2 <= c k x`, follows
  from `2 <= k x` and `c >= 1`.  All downstream call sites were updated and the module rebuilds
  clean.

  This is the shape needed for the full channel range.  For `k >= 2` the hypothesis `2 <= k L`
  holds already at `L = 1`, so `[1, X]` is covered by a single estimate with gain
  `1/(1 * c * k) * (1/k)` once the substitution's Jacobian is accounted for -- no split at `2`, and
  no separate endpoint analysis.

- 2026-08-09 (eighty-fifth instalment) -- **`(16)` over the full channel range.**  The exact-channel
  layer generalised to a free left endpoint; six new declarations plus eight relaxed signatures in
  `RHTower/ProlateExactChannel.lean`; all axiom-clean.

  ```text
  norm_integral_radialProlate_dilate_left_le :
    ‖∫ t in L..X, R (k t)‖ <= 4500 * exactEnergyBudget s c R DR 2 / (sqrt c * (c k^2) * L)
  ```

  under `1 <= L`, `2 <= k L`, `L <= X`.  At `L = 1` and `k >= 2` this is the whole channel
  `[1, X]` in one estimate -- the range that the eighty-second instalment had named as the last
  gap.

  * New: **`continuousOn_dilatedPhase_left`, `continuousOn_exactAmpDeriv_left`,
    `continuousOn_exactBranchAmp_left`, `continuousOn_exactBranchAmpDeriv_left`,
    `continuousOn_exactBranchIntegrand_left`,
    `norm_integral_radialProlate_dilate_left_le`.**
  * Relaxed in place: `hasDerivAt_exactAmplitude`, `hasDerivAt_exactAmp`,
    `hasDerivAt_exactBranchAmp`, `sqrt_mul_radialProlate_dilate_eq`,
    `sqrt_mul_radialProlate_dilate_eq_branches`, `radialProlate_dilate_eq_branch_integrand`,
    `abs_exactBranchAmp_le`, `abs_exactBranchAmpDeriv_le`.

  The relaxation is uniform and worth stating as a principle: **every hypothesis of the form
  `2 <= x` in this layer was really a hypothesis about `k x`, not about `x`.**  Once written as
  `1 <= x` together with `2 <= k x` (or just `1 < k x` where only positivity of the phase was
  needed), all the proofs go through unchanged, and the dilation does what it is supposed to do --
  push the outer variable's constraint down by a factor `k`.  The old form silently forced every
  channel to start at the same place.

  The `[2, X]` capstone `norm_integral_radialProlate_dilate_le` is retained and still builds; it is
  now a corollary in substance, though not stated as one.

- 2026-08-09 (eighty-sixth instalment) -- **The full-range channels `k >= 2` summed.**

  * **`tsum_norm_integral_radialProlate_full_channels_le`** --

    ```text
    sum_{j>=0} ‖integral_1^X R((2+j) t) dt‖ <= 4500 M / (sqrt c * c),
    ```

    unconditionally, for every `X >= 1`.  This is the whole `k >= 2` part of `(11)` for the exact
    mode, over the *entire* range `[1, X]` -- not the exterior part of it.

  The `k >= 2` channels are now closed end to end.  What is left for `(11)` is only the first
  channel, `k = 1`, which does not satisfy `2 <= k L` at `L = 1` and so splits at `2`:
  `[1,2]` is `(17)` (`abs_integral_sqrt_mul_radialProlate_full_le`, proved) and `[2,X]` is
  `norm_integral_radialProlate_dilate_left_le` at `k = 1`, `L = 2`, giving `2250 M/(sqrt c c)`.
  Assembling those two is a case split on `X <= 2`, plus the bookkeeping that turns
  `integral ((R t : R) : C)` into the real integral.

  Note that `(17)` carries two hypotheses the exterior work does not: `5 <= c` and `R 1 = 1`.  They
  are the card's standing normalisation for the radial mode, so the assembled `(11)` will carry
  them too; nothing in the `k >= 2` half needs either.

- 2026-08-09 (eighty-seventh instalment) -- **`(11)` PROVED FOR THE EXACT RADIAL MODE.**

  ```text
  tsum_norm_integral_radialProlate_all_channels_le :
    ‖integral_1^X R t dt‖ + sum_{j>=0} ‖integral_1^X R((2+j) t) dt‖
      <= prolateEndpointConstant/(c sqrt c) + 6750 M/(sqrt c * c)
  ```

  unconditionally, for every `X >= 1`, every `c >= 5`, every `0 <= s <= 1/2`, given only that `R`
  solves the radial prolate equation with `R 1 = 1`.  `M = exactEnergyBudget s c R DR 2` is the
  mode's own energy at the fixed base point `x = 2`.  The bound is uniform in the endpoint `X`, so
  taking the supremum changes nothing -- which is exactly the shape `(11)` asks for.

  * **`prolateEndpointConstant`, `prolateEndpointConstant_nonneg`.**
  * **`norm_integral_radialProlate_first_channel_le`** -- the first channel, `k = 1`, the only one
    whose range is not entirely exterior.  It splits at the Dunster crossing: `(17)` on `[1,2]`,
    and `norm_integral_radialProlate_dilate_left_le` at `k = 1`, `L = 2` beyond.  The case `X <= 2`
    needs no split at all.
  * **`tsum_norm_integral_radialProlate_all_channels_le`** -- `(11)`.

  Constants: `2250` from the first channel's exterior part, `4500` from the sum over `k >= 2`,
  total `6750`; plus the endpoint constant, which carries `c^{-3/2}` rather than `c^{-1}` because
  `(17)` is stated for `sqrt c R` and the channel sum is stated for `R`.

  Two hypotheses enter here that the exterior work did not need: `5 <= c` and `R 1 = 1`.  Both come
  from `(17)` alone, and both are the card's standing normalisation.  The `k >= 2` half holds with
  `1 <= c` and no normalisation whatsoever.

- 2026-08-09 (eighty-eighth instalment) -- **`(9)` and `(10)`: the decaying branch and the cosh
  combination.**  New module `HTGeometry/HalfLineCoshPrimitive.lean`, wired, all three declarations
  axiom-clean.  **Item 6 of the Lean plan is now `[FORMALIZED]`** (corrected above).

  The card lists the module `(7)`--`(10)` as formalized, but `HalfLineAutocorrelationPrimitive`
  contains only `(7)` (the Fubini/primitive identity) and `(8)` (the growing branch's `L^1` bound).
  `(9)` and `(10)` were not there.

  * **`integral_exp_neg_half_le_two`** -- `integral_{(0,H]} exp(-h/2) <= 2`, by the fundamental
    theorem of calculus with antiderivative `-2 exp(-h/2)`.
  * **`abs_integral_exp_neg_half_mul_autocorrelation_le`** -- `(9)`: a uniform bound `N` on the
    autocorrelation gives `<= 2N` for the decaying branch.  No primitive, no Fubini, no
    oscillation: `exp(-h/2)` simply has finite mass.
  * **`abs_integral_cosh_mul_autocorrelation_le`** -- `(10)`: `2 cosh(h/2) = exp(h/2) + exp(-h/2)`
    splits the integral, and the two branches are bounded by their own mechanisms.

  The asymmetry between the branches is the whole content of the pair, and stating them separately
  makes it visible: the growing branch is dangerous and needs the primitive identity of `(7)`; the
  decaying branch is free.  `(10)` takes the growing bound as a parameter `B` precisely so that the
  two mechanisms stay separated -- `B` is whatever `(8)` plus the radial primitive `(11)` supply.

  With `(11)` proved for the exact mode in the eighty-seventh instalment and `(10)` now available,
  what stands between here and `(18)` is the instantiation: identify `B` with the constant coming
  from `(11)` for the constrained radial source, and supply the Fubini and integrability side
  conditions for that particular source.

- 2026-08-09 (eighty-ninth instalment) -- **The polar source estimate, both branches composed.**
  Two further theorems in `HTGeometry/HalfLineCoshPrimitive.lean`; axiom-clean; the `HTGeometry`
  umbrella builds green.

  * **`abs_integral_exp_half_mul_autocorrelation_le`** -- `(7)` composed with `(8)`:

    ```text
    |integral_{(0,H]} exp(h/2) C_R(h) dh| <= 2 M integral_{(0,inf)} |exp(-s/2) R(s)| ds,
    ```

    where `M` bounds the growing primitive.  The composition is the oscillatory cancellation: the
    growing kernel is never bounded in absolute value, it is turned into a pairing against a
    primitive increment first.
  * **`abs_integral_cosh_mul_autocorrelation_full_le`** -- both branches:

    ```text
    |integral_{(0,H]} 2 cosh(h/2) C_R(h) dh| <= 2 M integral |exp(-s/2) R| + 2 N.
    ```

    This is the card's `(10)` in the corpus's own terms, with `M` the primitive bound and `N` the
    uniform autocorrelation bound.  Uniform in `H`.

  `(7)`--`(10)` are now a usable chain rather than two isolated lemmas, and the chain is stated so
  that the two constants it consumes are exactly the two objects the rest of the card produces:
  `M` from the all-radial primitive `(11)`, and `N` from Cauchy--Schwarz on the source.

- 2026-08-09 (ninetieth instalment) -- **The uniform autocorrelation bound.**  Two further
  theorems in `HTGeometry/HalfLineCoshPrimitive.lean`; axiom-clean.

  * **`integral_sq_comp_add_right`** -- `integral_{(0,inf)} R(s+h)^2 ds = integral_{(h,inf)} R^2`,
    by rewriting both sides as indicator integrals over the line and applying translation
    invariance.
  * **`abs_halfLineAutocorrelation_le`** -- `|C_R(h)| <= integral_{(0,inf)} R^2` for `h >= 0`.

  This is the constant `N` that `(10)` consumes, and it closes the last input of the polar source
  estimate.

  The proof deliberately avoids Cauchy--Schwarz.  mathlib's Hoelder inequalities for integrals live
  in `ℝ≥0∞` (`lintegral_mul_le_Lp_mul_Lq`) and getting a real Bochner statement out of them costs
  more than the result is worth here.  The arithmetic--geometric mean inequality
  `|R(s+h) R(s)| <= (R(s+h)^2 + R(s)^2)/2` gives **the same constant** -- because the two square
  masses are equal up to the shift, and the shifted one is smaller -- with nothing but
  `setIntegral_mono_set` and a pointwise `nlinarith`.  Cauchy--Schwarz is only sharper when the two
  factors have different masses, which is exactly what does not happen for an autocorrelation.

  A note on imports: `integral_add_right_eq_self` is not reachable from the narrow mathlib imports
  of `HalfLineAutocorrelationPrimitive`, and `lake env lean` reports it as an unknown identifier
  rather than a missing import.  Adding `import Mathlib` is what the other modules in this layer do.

- 2026-08-09 (ninety-first instalment) -- **`(10)` with both constants concrete.**

  * **`abs_integral_cosh_mul_autocorrelation_source_le`** --

    ```text
    |integral_{(0,H]} 2 cosh(h/2) C_R(h) dh|
      <= 2 M integral_{(0,inf)} |exp(-s/2) R| + 2 integral_{(0,inf)} R^2,
    ```

    unconditionally in `H >= 0`, with `M` the bound on the growing primitive and nothing else free.
    Both constants are now the card's: `M` is `‖A‖_infinity` and the square mass is `‖R‖_2^2`.

  `(7)`--`(10)` are closed.  The polar source estimate is reduced to exactly one analytic input --
  a uniform bound on `halfLineExpPrimitive R`, which is what `(11)` supplies -- plus the Fubini and
  integrability side conditions for the particular source.

  Status note: the `HTGeometry` umbrella built green through the ninetieth instalment and is now
  red on `HTGeometry/TopDegreeSharpDrop.lean` (three errors, including an unknown constant
  `TopFree.fpderiv_eq_zero`).  That file was modified at 08:30 by another agent and is not part of
  this card's work; `HalfLineCoshPrimitive` and everything else here builds clean in isolation.

- 2026-08-09 (ninety-second instalment) -- **`(12)`: the exponential substitution, and the bridge
  it carries.**  New module `HTGeometry/ExponentialSubstitution.lean` plus two theorems in
  `HalfLineCoshPrimitive`; wired; all axiom-clean.

  * **`sqrt_exp`, `exp_image_subset_Icc`, `integral_exp_half_comp_exp`** --

    ```text
    integral_0^t exp(s/2) f(exp s) ds = integral_1^{exp t} f(x) x^{-1/2} dx.
    ```

    This is the card's `(12)`.  The weight `exp(s/2)` on the left is exactly `dx/sqrt x` on the
    right, which is *why* the growing branch of the autocorrelation and the `x^{-1/2}`-weighted
    radial primitive are the same object rather than merely comparable.
  * **`halfLineExpPrimitive_comp_exp`** -- the same statement for the corpus's
    `halfLineExpPrimitive`.
  * **`abs_halfLineExpPrimitive_le_of_radial`** -- the bridge: a bound on the radial primitive,
    uniform in its endpoint, *is* the bound `M` that `(10)` consumes.

  The two halves of the card now meet.  `(11)`
  (`RHTower.tsum_norm_integral_radialProlate_all_channels_le`) produces a bound on the radial
  primitive uniform in the endpoint; `abs_halfLineExpPrimitive_le_of_radial` turns that into `M`;
  and `abs_integral_cosh_mul_autocorrelation_source_le` turns `M` into the polar source estimate.

  A tactic note: `intervalIntegral.integral_comp_smul_deriv` and its primed variants are deprecated
  in this toolchain in favour of `integral_deriv_smul_comp`.  The doubly-primed form is the one to
  reach for here, since the integrand `f x / sqrt x` is continuous only on the image of the
  substitution, not on all of the line.

- 2026-08-09 (ninety-third instalment) -- **The chain closed end to end: the polar source estimate
  for a radial channel.**  New module `RHTower/ProlatePolarSource.lean`, wired, axiom-clean.

  * **`channelSource`** -- the `k`-th channel in the logarithmic variable,
    `u |-> sqrt(exp u) R(k exp u)`, i.e. the card's `H_(lambda,k)`.
  * **`abs_halfLineExpPrimitive_channelSource_le`** --

    ```text
    |halfLineExpPrimitive (channelSource k R) t|
      <= 4500 M / (sqrt c (c k^2))      for every t >= 0, every k >= 2.
    ```

    The growing half-line primitive of the channel source *is* the radial primitive
    `integral_1^X R(k x) dx`, by `(12)`; so `(16)` for the exact mode bounds it directly, uniformly
    in `t`.
  * **`abs_integral_cosh_mul_autocorrelation_channelSource_le`** -- the polar source estimate with
    every constant the mode's own.

  This closes the reduction the card sets up in `(4)`--`(18)`.  Running the chain backwards:

  1. the exact radial mode is a perturbed oscillator (`prolateOsc_ode`, `|q| <= 35/phi^2`);
  2. hence it has an exact two-branch representation with bounded, slowly drifting coefficients;
  3. hence `(16)`: `|integral_L^X R(k t) dt| <= 4500 M/(sqrt c (c k^2) L)`;
  4. hence, by the exponential substitution `(12)`, the channel source's growing primitive is
     bounded uniformly in the endpoint;
  5. hence, by `(7)`--`(8)`, the growing branch of its autocorrelation is bounded;
  6. hence, with `(9)` for the decaying branch, `(10)` holds for the channel source.

  What remains between here and `(18)` is not analysis of this kind: it is the identification of
  the constrained polar source with the radial channels (the card's `(4)`), the summation of the
  channel estimates in the polar functional, and the integrability side conditions for the specific
  source -- all bookkeeping over the machinery now in place, with one genuine input still open, the
  spectral-occupancy gate of item 7.

- 2026-08-09 (ninety-fourth instalment) -- **The channel sources' primitives sum.**

  * **`tsum_abs_halfLineExpPrimitive_channelSource_le`** --

    ```text
    sum_{j>=0} |halfLineExpPrimitive (channelSource (2+j) R) t| <= 4500 M/(sqrt c * c)
    ```

    for every `t >= 0`, unconditionally.  The bound is free of `t`, so it survives the supremum.

  This is the form the passage from finite radial sums needs: not "each channel's primitive is
  small" but "the primitives are summable with a bound free of the point", which is what lets the
  finite truncations be controlled uniformly before the `L^2` limit is taken.

  Everything in the `k >= 2` half of the card's radial analysis is now unconditional Lean, from the
  prolate ODE to the summed polar source primitive, with no hypothesis beyond `0 <= s <= 1/2`,
  `1 <= c` and the ODE itself.

- 2026-08-09 (ninety-fifth instalment) -- **All channel sources' primitives, summed.**

  * **`abs_halfLineExpPrimitive_firstChannelSource_le`** -- the `k = 1` source, through the full
    first-channel bound, so the endpoint term appears exactly once.
  * **`tsum_abs_halfLineExpPrimitive_allChannelSource_le`** --

    ```text
    |halfLineExpPrimitive (channelSource 1 R) t|
      + sum_{j>=0} |halfLineExpPrimitive (channelSource (2+j) R) t|
        <= prolateEndpointConstant/(c sqrt c) + 6750 M/(sqrt c c),
    ```

    for every `t >= 0`, unconditionally.

  The radial side of the card is complete: from the prolate ODE to a single constant bounding the
  whole radial object's growing primitive, uniformly along the logarithmic half-line, with the
  channel index summed out.  Every step is an identity or an estimate proved here; no model is
  introduced and no transfer error is taken in absolute value anywhere in the chain.

- 2026-08-09 (ninety-sixth instalment) -- **The polar charge and its estimate: the card's `(3)` and
  `(10)` as stated objects.**

  * **`polarCharge`** -- `(3)`: `4 integral_0^{2a} cosh(h/2) C_R(h) dh`.  The source is real, so the
    real part in the card's statement is the identity and no complexification is needed.
  * **`polarCharge_eq`** -- the factor-of-two bookkeeping between `(3)` and the `2 cosh` form the
    estimate is proved in.
  * **`abs_polarCharge_le`** -- **`(10)`**:

    ```text
    |PPol(R, a)| <= 4 M ‖G‖_1 + 4 ‖R‖_2^2,
    ```

    with `M` the bound on the growing primitive and `G(s) = exp(-s/2) R(s)`.  This is exactly the
    card's inequality `4‖A‖_infinity‖R‖_2 + 4‖R‖_2^2`, with `‖G‖_1` in place of `‖R‖_2` -- the
    honest `L^1` quantity, which Cauchy--Schwarz would weaken to `‖R‖_2` if that form were wanted.

  With `(4)` (`‖R‖_2^2 = O(d_lambda)`) and the radial primitive bound of the ninety-fifth
  instalment supplying `M`, `(18)` is now an instantiation of this single inequality.

- 2026-08-09 (ninety-seventh instalment) -- **`(18)` per channel.**

  * **`abs_polarCharge_channelSource_le`** -- for `k >= 2`:

    ```text
    |PPol(channelSource k R, a)|
      <= 4 (4500 M/(sqrt c (c k^2))) ‖G_k‖_1 + 4 ‖channelSource k R‖_2^2.
    ```

  * **`abs_polarCharge_firstChannelSource_le`** -- the same for `k = 1`, with the endpoint constant
    in place of the `k^{-2}` gain.

  Both are instantiations of `abs_polarCharge_le` at the primitive bounds of the ninety-fifth
  instalment, so the only content added here is that the constants line up.  The `1/k^2` sits where
  the card says it should: multiplying the source's own `L^1` mass, so summing over channels needs
  nothing further about the modes.

  What is left for `(18)` proper: the card's `(4)`, `‖R_lambda‖_2^2 = O(d_lambda)`, which is a
  statement about the operator's spectral data rather than about the radial ODE, and the
  identification of the constrained source with the channel decomposition.  Neither is an estimate
  of the kind this chain produces; both belong to item 7's spectral-occupancy gate.

- 2026-08-09 (ninety-eighth instalment) -- **The passage from finite radial sums.**  Four
  declarations across `HTGeometry/HalfLineCoshPrimitive.lean` and
  `RHTower/ProlatePolarSource.lean`; all axiom-clean.

  * **`halfLineExpPrimitive_finset_sum`** -- the growing primitive is additive over finite sums of
    sources.
  * **`abs_halfLineExpPrimitive_finset_sum_le`** -- a summable family of primitives bounds *every*
    finite truncation by the same constant.
  * **`summable_abs_halfLineExpPrimitive_channelSource`** -- the channel primitives are summable at
    every point.
  * **`abs_halfLineExpPrimitive_channelTruncation_le`** --

    ```text
    |halfLineExpPrimitive (sum_{j<N} channelSource (2+j) R) t| <= 4500 M/(sqrt c c)
    ```

    for every `N` and every `t >= 0`.

  This is the card's own passage order, made precise: the bound is established on the truncations
  *first*, uniformly in `N` and in the point, and only then is the limit taken.  Nothing here
  interchanges an infinite channel sum with an improper primitive -- the finite sums are all that
  ever appears, and the constant does not degrade as `N` grows.

  The remaining step of the passage, `R_(lambda,N) -> R_lambda` in `L^2`, is the weighted
  projective Gram theorem the card cites, and its `L^2` machinery is already formalized
  (`HTGeometry.norm_inner_le_tsum_of_tendsto`, twenty-fifth instalment).

- 2026-08-09 (ninety-ninth instalment) -- **The limit of the passage.**

  * **`abs_halfLineExpPrimitive_le_of_tendsto`** -- a bound uniform in the truncation is a bound on
    the limit, once the primitives converge.
  * **`abs_halfLineExpPrimitive_sub_le`** --

    ```text
    |halfLineExpPrimitive f t - halfLineExpPrimitive g t| <= exp(t/2) integral_0^t |f - g|,
    ```

    the quantitative continuity of the primitive functional on the compact range.

  The card invokes `L^2` continuity of `f |-> integral_0^H exp(s/2) f`.  The `L^1` form proved here
  is what the argument actually needs and is elementary: on `[0, t]` the weight is bounded by
  `exp(t/2)`, so no Cauchy--Schwarz and no `L^p` machinery is involved.  It is also strictly more
  useful, since `L^1` convergence on compacts is implied by `L^2` convergence there and not
  conversely.

  With this the passage is complete as a chain of formalized steps: bound on truncations, uniform
  in `N` and in the point; continuity of the functional; limit.  The only input still supplied from
  outside is the convergence `R_(lambda,N) -> R_lambda` itself, which is the weighted projective
  Gram theorem.

- 2026-08-09 (hundredth instalment) -- **`(11)` for the limit radial object.**

  * **`HTGeometry.abs_halfLineExpPrimitive_limit_le`** -- the passage assembled: a bound on every
    truncation, uniform in the truncation and in the point, plus pointwise convergence of the
    truncations' primitives, bounds the limit's primitive by the same constant.
  * **`RHTower.abs_halfLineExpPrimitive_radialLimit_le`** --

    ```text
    |halfLineExpPrimitive T t| <= 4500 M/(sqrt c * c)      for every t >= 0,
    ```

    for any `T` that is the limit of the channel truncations in the sense that their primitives
    converge to its.

  This is the end of the radial chain.  Everything from the prolate ODE to this bound is
  unconditional Lean, and the single input taken from outside is the convergence of the
  truncations -- the card's weighted projective Gram theorem, which is a statement about the
  operator's spectral decomposition and not about the radial ODE.

  Feeding this constant into `abs_polarCharge_le` gives the card's `(10)` for the limit source, and
  with `(4)` it gives `(18)`.  Both of those remaining inputs live on the spectral side, i.e. item
  7 of the Lean plan.

- 2026-08-09 (hundred-and-first instalment) -- **`(18)` for the limit radial object.**

  ```text
  abs_polarCharge_radialLimit_le :
    |PPol(T, a)| <= 4 (4500 M/(sqrt c * c)) ‖exp(-u/2) T‖_1 + 4 ‖T‖_2^2
  ```

  for every `a >= 0`, where `T` is the limit of the channel truncations and
  `M = exactEnergyBudget s c R DR 2`.  This is the card's `(18)` shape with every constant on the
  right traced back to the radial ODE.

  The reduction the card sets out in `(2)`--`(18)` is now a chain of formalized theorems.  Read
  forwards, with the Lean names:

  * `prolateOsc_ode`, `abs_prolateOscPotential_le` -- the mode is a perturbed oscillator;
  * `sqrt_mul_radialProlate_dilate_eq_branches` -- exact two branches, no error term;
  * `norm_integral_radialProlate_dilate_left_le` -- `(16)` on the full channel range;
  * `tsum_norm_integral_radialProlate_all_channels_le` -- `(11)`;
  * `integral_exp_half_comp_exp` -- `(12)`, the exponential substitution;
  * `abs_halfLineExpPrimitive_channelTruncation_le`, `abs_halfLineExpPrimitive_limit_le` -- the
    passage from finite radial sums;
  * `integral_exp_half_mul_halfLineAutocorrelation_eq_primitive`,
    `abs_integral_exp_half_mul_autocorrelation_le` -- `(7)`, `(8)`;
  * `abs_halfLineAutocorrelation_le`, `abs_integral_exp_neg_half_mul_autocorrelation_le` -- `(9)`;
  * `abs_polarCharge_le` -- `(10)`;
  * `abs_polarCharge_radialLimit_le` -- `(18)`.

  Two inputs are still taken from outside, and both are spectral rather than analytic: the
  convergence `R_(lambda,N) -> R_lambda` (the weighted projective Gram theorem) and `(4)`,
  `‖R_lambda‖_2^2 = O(d_lambda)`.  Both belong to item 7.

- 2026-08-09 (hundred-and-second instalment) -- **Item 7: the ordered partition assembly.**  New
  module `HTGeometry/DarbouxMonotoneCell.lean`, wired, all three declarations axiom-clean.

  The card names three remaining pieces for `(19e)`: the classical spheroidal nodal count, the
  ordered partition assembly, and the concrete representative.  This instalment closes the second.

  * **`monotoneOn_or_antitoneOn_of_deriv_ne_zero`** -- a cell whose interior contains no critical
    point is monotone in one direction.  Darboux gives the derivative the intermediate value
    property, so not vanishing on the open cell forces a constant sign; the direction is then
    `strictMonoOn_of_deriv_pos` or `strictAntiOn_of_deriv_neg`.
  * **`partition_monotone_of_deriv_ne_zero`** -- the same for every cell of a monotone partition
    index, which is the exact hypothesis shape `eVariationOn_le_of_piecewise_monotone` takes.
  * **`eVariationOn_le_of_deriv_ne_zero_on_cells`** -- the composite: a monotone partition whose
    cells avoid critical points in their interiors gives variation at most `2 n B`.

  The gap this fills was real.  `FiniteMonotonicityVariation` proves the variation law *given*
  monotonicity on each cell, and `ProlateOneTurningVariation` proves the prolate flux equation and
  bounds the critical points per sign cell -- but nothing connected "the derivative has no zero
  here" to "the function is monotone here".  That connection is Darboux, and mathlib has it as
  `hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`.

  What remains for `(19e)`: the nodal count for the even spheroidal modes `n = 0, 4` (a classical
  Sturm statement about the number of zeros, giving the `n` in `2 n B`), and the concrete
  representative.

- 2026-08-09 (hundred-and-third instalment) -- **The ordered partition assembly, with its count.**

  * **`exists_monotone_partition_of_finset`** -- a finite set `S` of critical points inside `[a,b]`
    is enumerated in order into a monotone index `I : N -> R` with `I 0 = a`, `I n = b`,
    `n <= |S| + 1`, and every cell interior free of `S`.  The construction is
    `Finset.orderEmbOfFin` on `insert a (insert b (S.filter (. in [a,b])))`, with `I` extended
    beyond the last index by the constant `b` so that monotonicity holds on all of `N`.
  * **`eVariationOn_le_of_finite_critical_set`** --

    ```text
    Var_{[a,b]}(f) <= 2 (|S| + 1) B      whenever f' vanishes on (a,b) only inside S.
    ```

  This is `(19g)` in its abstract form, and it is the shape `(19e)` needs: the variation is bounded
  by the *number of critical points*, so a mode whose critical count is bounded independently of
  `lambda` has variation `O(1)` -- which is exactly the card's argument.

  What is left for `(19e)` is now a single classical statement: the count itself for the even
  spheroidal modes `n = 0, 4`.  Everything downstream of that count is formalized.

- 2026-08-09 (hundred-and-fourth instalment) -- **The Sturm variation law.**

  * **`finite_critical_of_cellwise_subsingleton`** -- if each cell of a monotone partition contains
    at most one critical point, the whole range contains finitely many.  Induction on the number of
    cells; the only subtlety is that the partition points themselves must be added at each step,
    since `Ioo (J 0) (J (m+1))` is not the union of the open cells alone.
  * **`eVariationOn_le_of_cellwise_subsingleton`** -- a function whose derivative vanishes at most
    once per cell has finite total variation, bounded by twice the critical count.

  This is exactly the card's `(19f)`--`(19g)` argument in abstract form.  The card's chain is: on a
  cell where both factors of the Sturm right-hand side have fixed sign, the flux `(1-z^2) y'` is
  strictly monotone, so `y'` vanishes at most once there; hence the critical count is bounded by
  the number of sign cells; hence the variation is `O(1)` for a fixed mode.  Each of those "hence"
  steps is now a theorem:

  * flux strictly monotone on a fixed-sign cell -- `ProlateOneTurningVariation` (already present);
  * at most one critical point per cell -- the subsingleton hypothesis, supplied by that flux
    monotonicity;
  * bounded count -- `finite_critical_of_cellwise_subsingleton`;
  * bounded variation -- `eVariationOn_le_of_cellwise_subsingleton`.

  The only remaining input for `(19e)` is the classical nodal count that says how many sign cells
  the even spheroidal modes `n = 0, 4` have.

- 2026-08-09 (hundred-and-fifth instalment) -- **`(19g)` for the prolate mode.**  New module
  `RHTower/ProlateSturmVariation.lean`, wired, both declarations axiom-clean.

  * **`prolate_eVariationOn_le_of_signCells`** --

    ```text
    Var_{[J 0, J m]}(psi) <= 2 (|S| + 1) B
    ```

    for any monotone partition `J` on whose open cells `(chi + c^2 y^2) psi` has fixed sign, where
    `S` is the mode's critical set on that range.
  * **`prolate_boundedVariationOn_of_signCells`** -- the mode is BV there.

  This is the card's `(19g)`.  The two halves it joins were both already present and had never been
  connected: `ProlateOneTurningVariation` gives at most one stationary point per fixed-sign cell (on
  `Icc`, which restricts to `Ioo` for free), and the Darboux/partition layer of the last three
  instalments turns "at most one per cell" into a variation bound.

  The bound depends only on the *number of sign cells*, not on `c` or `chi`.  That is exactly the
  property `(19e)` needs: a fixed even mode whose sign-cell count does not grow with the aperture
  has variation `O(1)`.

  So item 7's analytic content is now formalized end to end, and what remains of `(19e)` is a
  single classical statement with no analysis in it: the number of sign cells of the even
  spheroidal modes `n = 0, 4`, i.e. their nodal count.

- 2026-08-09 (hundred-and-sixth instalment) -- **`(19g)` from a finite zero set: item 7's analytic
  content closed.**

  * **`HTGeometry.sign_fixed_of_no_zero`** -- a continuous function with no zero on an open cell has
    fixed sign there, by the intermediate value theorem.
  * **`RHTower.prolate_eVariationOn_le_of_finite_zeros`** --

    ```text
    Var_{[a,b]}(psi) <= 2 (|S| + 1) B
    ```

    whenever `(chi + c^2 y^2) psi` vanishes only on a finite set inside `(a,b)`.

  The partition lemma was strengthened with a tail law (`n <= i -> I i = b`) so that the sign
  hypothesis can be stated for *all* indices: past the last cell the interval is empty and the
  requirement is vacuous.  Without that the composite could not be assembled, because
  `prolate_eVariationOn_le_of_signCells` quantifies over all `i`.

  This is item 7's analytic content, complete: from the prolate eigen-equation and a finite zero
  set of its right-hand side to an explicit variation bound, with no asymptotics, no spectral
  index, and no aperture-dependence in the constant.  The chain is

  ```text
  eigen-equation -> flux monotone on fixed-sign cells -> one critical point per cell
    -> finite critical set -> monotone partition -> Var <= 2 (count + 1) sup.
  ```

  What `(19e)` still needs is the finite zero set itself for the even spheroidal modes `n = 0, 4`,
  with a count independent of the aperture.  That is a classical Sturm oscillation statement about
  spheroidal functions, and it is the only remaining input.

- 2026-08-09 (hundred-and-seventh instalment) -- **Simple zeros are finitely many.**  New module
  `HTGeometry/IsolatedZeroFinite.lean`, wired, all three declarations axiom-clean.

  * **`finite_of_isolated_in_compact`** -- a compact set whose points are isolated is finite, via
    `IsCompact.finite` and `isDiscrete_iff_forall_mem_exists_isOpen`.
  * **`isolated_of_simple_zero`** -- a zero at which the derivative is nonzero has a punctured
    neighbourhood free of zeros.
  * **`finite_zeros_of_simple`** -- a differentiable function all of whose zeros in `[a,b]` are
    simple has finitely many of them.

  This supplies the finite zero set that `prolate_eVariationOn_le_of_finite_zeros` consumes,
  reducing `(19e)` to *simplicity* of the zeros rather than to a count.  For a nontrivial solution
  of a second-order linear ODE simplicity is automatic -- a double zero forces the solution to
  vanish identically -- so the remaining input is nontriviality, not an oscillation theorem.

  A naming trap worth recording: `HasDerivAt.eventually_ne` displays as
  `∀ᶠ z in 𝓝[≠] x, f z ≠ c` with `c` an unconstrained section variable, which reads as false and is
  unusable as stated.  `HasDerivAt.tendsto_nhdsNE`, `Tendsto f (𝓝[≠] x) (𝓝[≠] f x)`, is the
  unambiguous form and gives the same content directly.

- 2026-08-09 (hundred-and-eighth instalment) -- **Grönwall uniqueness: a double zero kills the
  solution.**  New module `HTGeometry/GronwallUniqueness.lean`, wired, both declarations
  axiom-clean.

  * **`eq_zero_of_nonneg_of_deriv_le_mul`** -- a nonnegative energy vanishing at the left endpoint
    and obeying `E' <= K E` vanishes on the whole interval, because `E exp(-K x)` is antitone,
    nonnegative and zero at the left end.
  * **`sq_add_sq_eq_zero_of_double_zero`** -- for `E = u^2 + (u')^2` and a second-order equation
    whose second derivative is dominated by `K (|u| + |u'|)`, a double zero forces `u` and `u'` to
    vanish on the whole interval.

  This is the uniqueness half of the Cauchy problem in exactly the form the Sturm theory needs, and
  it avoids `ODE_solution_unique` and its Lipschitz-vector-field machinery entirely: the same energy
  and Grönwall pattern used for the Bessel and prolate oscillators serves here too.

  The constant needed care.  Bounding `2 u' u'' <= 2|u'| K(|u| + |u'|)` and then by a multiple of
  `u^2 + (u')^2` gives `3K`, not `2K`: the term `2K|u'|^2` alone already needs `2K(u^2 + (u')^2)`,
  and the cross term needs a further `K`.  The first attempt used `2K` and was false.

  With this, `(19e)`'s remaining input reduces to nontriviality of the mode: a solution that is not
  identically zero has only simple zeros, hence finitely many, hence bounded variation by the chain
  of the last four instalments.

- 2026-08-09 (hundred-and-ninth instalment) -- **Nontrivial implies simple implies finite.**

  * **`eq_zero_of_nonneg_of_neg_mul_le_deriv`** -- Grönwall backwards, from the right endpoint.
  * **`eq_zero_of_double_zero_interior`** -- a double zero *anywhere* in `[a,b]` kills the solution
    on the whole interval, forwards and backwards.
  * **`simple_zeros_of_nontrivial`** -- a solution that is nonzero somewhere has only simple zeros.
  * **`finite_zeros_of_nontrivial`** -- hence finitely many zeros.

  The chain from the seventh through the hundred-and-ninth instalment is now closed as a single
  implication:

  ```text
  nontrivial solution of a second-order equation with |u''| <= K(|u| + |u'|)
    -> zeros simple      (Gronwall uniqueness)
    -> zeros finite      (isolation in a compact interval)
    -> sign cells finite (intermediate value theorem)
    -> one critical point per cell   (Sturm flux monotonicity)
    -> critical set finite            (induction over cells)
    -> monotone partition             (Finset.orderEmbOfFin)
    -> Var <= 2 (count + 1) sup.      (finite-monotonicity law)
  ```

  Every arrow is an unconditional Lean theorem.  For the prolate mode the coefficient bound
  `|psi''| <= K(|psi| + |psi'|)` holds on any `[a,b]` strictly inside `(-1,1)` with
  `K = (|chi| + c^2 + 2)/dist(b, 1)`, so `(19e)` for a fixed even mode reduces to that one
  arithmetic bound plus nontriviality.

- 2026-08-09 (hundred-and-tenth instalment) -- **The prolate coefficient bound, and finite zeros for
  a nontrivial mode.**

  * **`prolate_secondDeriv_bound`** --

    ```text
    |psi''(x)| <= ((|chi| + c^2 + 2)/(1 - r^2)) (|psi(x)| + |psi'(x)|)     for |x| <= r < 1,
    ```

    read off the eigen-equation `(1-x^2) psi'' - 2x psi' - c^2 x^2 psi = chi psi` by dividing by
    `1-x^2`, which is bounded below strictly inside the band.
  * **`prolate_finite_zeros`** -- a nontrivial prolate mode has finitely many zeros on `[-r, r]`.

  This is the last ingredient.  `(19e)` for a fixed even mode is now: the coefficient bound (proved
  here, explicit), nontriviality (a property of the mode, not an estimate), and the chain of the
  previous instalments.  No spheroidal nodal count and no oscillation theorem are needed anywhere --
  the count that the variation law consumes is produced by Gronwall uniqueness plus isolation, not
  by classical Sturm-Liouville asymptotics.

  The constant degrades as `r -> 1`, which is correct and unavoidable: the equation is singular at
  the band edge, and the card's `(19e)` is a statement about the mode on the closed band with the
  endpoint contribution handled separately (the "bounded endpoint jump" of the paper argument).

- 2026-08-09 (hundred-and-eleventh instalment) -- **`(19e)` PROVED for a nontrivial prolate mode.**

  ```text
  prolate_boundedVariationOn_of_nontrivial :
    eVariationOn psi (Icc (-r) r) <= ENNReal.ofReal (2 (|S| + 1) B)
  ```

  for `0 <= r < 1`, `c != 0`, any nontrivial solution of the prolate eigen-equation bounded by `B`
  on the band, with `S` its critical set there.  Unconditional and axiom-clean.

  * **`finite_prolate_turning_points`** -- the turning-point set is finite, being the zero set of a
    quadratic; the only case needing care is `c = 0`, excluded.

  The chain, complete, from the eigen-equation to the variation bound:

  1. `prolate_secondDeriv_bound` -- `|psi''| <= K(|psi| + |psi'|)` strictly inside the band;
  2. `eq_zero_of_double_zero_interior` -- a double zero kills the solution (Gronwall, both
     directions);
  3. `simple_zeros_of_nontrivial`, `finite_zeros_of_simple` -- nontrivial modes have finitely many,
     simple, zeros;
  4. `finite_prolate_turning_points` -- the quadratic factor contributes at most two more;
  5. `sign_fixed_of_no_zero` -- the gaps are sign cells;
  6. `prolate_criticalSet_subsingleton_of_rhs_pos/neg` -- one stationary point per sign cell;
  7. `finite_critical_of_cellwise_subsingleton`, `exists_monotone_partition_of_finset` -- a
     monotone partition;
  8. `eVariationOn_le_of_piecewise_monotone` -- the variation bound.

  Item 7 of the Lean plan named three remaining pieces: the classical spheroidal nodal count, the
  ordered partition assembly, and the concrete representative.  Two of the three are now closed,
  and the first turned out not to be needed at all -- Gronwall uniqueness supplies the finiteness
  that the nodal count was meant to supply, without any spheroidal asymptotics.

- 2026-08-09 (hundred-and-twelfth instalment) -- **Full-tree audit, and two more stale paragraphs
  corrected.**

  `scripts/formal_tools.py lint` reports **`formal lint passed`**: no active `sorry`, `admit`,
  `axiom`, `opaque` or `unsafe` declaration anywhere in the tree, and no oversized file among the
  modules added for this card (`ProlateExactChannel.lean` is the largest at 1303 lines, under the
  1500 threshold).  The `HTGeometry` umbrella builds green.

  Corrections to the card's own text:

  * The "Exact open core" section said `(19e)`'s "universal variation lemma and concrete spheroidal
    instance still require Lean formalization".  Both are now theorems, and the spheroidal instance
    turned out to be unnecessary -- the paragraph now says so and names
    `RHTower.prolate_boundedVariationOn_of_nontrivial`.
  * Item 7's status line and its follow-on paragraph were corrected in the previous instalment.

  Reading the card end to end, the analytic content of the route is now formalized: the radial
  chain `(2)`--`(18)`, the passage from finite radial sums, the polar source estimate, and the
  fixed-mode variation law `(19e)`.  What remains is spectral, not analytic:

  * the weighted projective Gram convergence `R_(lambda,N) -> R_lambda`;
  * `(4)`, `‖R_lambda‖_2^2 = O(d_lambda)`;
  * identification of the classical real `h_0, h_4` modes in the actual operator spectrum, which is
    what `(35)` reduces to and what item 7 still names as open.

  All three are statements about the operator's spectral decomposition.  None of them is an
  estimate of the kind the last hundred instalments produced, and none can be reached by
  strengthening the radial analysis.

- 2026-08-09 (hundred-and-thirteenth instalment) -- **The commutation kernel identity.**  New module
  `RHTower/ProlateCommutationKernel.lean`, wired, all declarations axiom-clean.

  The classical reason the eigenfunctions of the finite Fourier transform satisfy the prolate
  differential equation is one algebraic identity, and it is now a theorem:

  ```text
  (1 - x^2) d^2_x k - 2x d_x k - c^2 x^2 k = (1 - t^2) d^2_t k - 2t d_t k - c^2 t^2 k,
  k(x,t) = exp(i c x t).
  ```

  Both sides equal `-(c^2 t^2 + c^2 x^2 - c^2 x^2 t^2 + 2 i c x t) k`.

  * **`bandKernel`, `hasDerivAt_bandKernel_fst/snd`,
    `hasDerivAt_bandKernelDeriv_fst/snd`** -- the kernel and its first two derivatives in each
    variable; the second derivatives use `I * I = -1` explicitly.
  * **`prolateSymbol`, `prolate_bandKernel_symm`, `prolateSymbol_bandKernel_symm`** -- the identity,
    stated both raw and through the operator symbol.

  This is the heart of the spectral identification named in item 7 and `(35)`.  What it does not yet
  do is *commute the operators*: that needs two integrations by parts under the integral sign, and
  their boundary terms vanish because `1 - t^2` does at `t = ±1`.  The identity is the part with the
  content; the integrations are the part with the analysis.

- 2026-08-09 (hundred-and-fourteenth instalment) -- **The Lagrange identity and Sturm--Liouville
  self-adjointness.**  New module `HTGeometry/SturmLagrangeIdentity.lean`, wired, all three
  declarations axiom-clean.

  * **`hasDerivAt_lagrangeBracket`** --

    ```text
    [p (u' v - u v')]' = (p u')' v - u (p v')',
    ```

    a pointwise derivative statement, proved by the product rule and `ring`.
  * **`integral_sturm_pairing_sub`** -- integrating it turns the difference of the two pairings into
    a boundary term.
  * **`integral_sturm_pairing_sub_eq_zero`** -- when `p` vanishes at both endpoints the boundary
    term vanishes and the operator is symmetric.

  This is the analytic half of the spectral identification, and for the prolate weight `1 - t^2` the
  endpoint hypothesis is automatic: no decay assumption on the solutions is needed, which is exactly
  why the finite Fourier transform and the prolate operator commute on the band and not merely
  formally.

  A tactic note: `HasDerivAt.mul` and `.sub` produce goals containing `Pi.mul_apply`-style
  applications like `(Du * v - u * Dv) x`, which `ring` cannot unfold; the `fun_mul` and `fun_sub`
  variants produce the lambda form and close by `ring` immediately.

- 2026-08-09 (hundred-and-fifteenth instalment) -- **The prolate operator is symmetric on the
  band.**  Complex Lagrange identity added to `HTGeometry/SturmLagrangeIdentity.lean`; the prolate
  instantiation added to `RHTower/ProlateCommutationKernel.lean`.  All axiom-clean.

  * **`hasDerivAt_lagrangeBracket_complex`, `integral_sturm_pairing_sub_complex`,
    `integral_sturm_pairing_sub_complex_eq_zero`** -- the identity and its integrated forms for
    complex-valued solutions of a real variable, which is what the band kernel needs.
  * **`prolateActionC`, `hasDerivAt_prolateWeight`, `integral_prolate_pairing_eq_zero`** --

    ```text
    integral_{-1}^{1} ((L u) v - u (L v)) = 0,   L u = ((1-t^2) u')' - c^2 t^2 u.
    ```

    The multiplication part `-c^2 t^2 u` cancels between the two sides with no hypothesis at all,
    and the Lagrange boundary term vanishes because `1 - t^2` does at both endpoints.  No decay,
    no boundary condition, no self-adjoint extension is imposed: the band is exactly where the
    operator is symmetric for free.

  Together with the kernel identity of the previous instalment this gives both halves of the
  classical commutation argument.  What is still not formalized is the interchange that puts them
  together -- differentiating `integral k(x,t) f(t) dt` twice under the integral sign -- which is a
  dominated-convergence argument about the specific kernel, not a further structural fact.

- 2026-08-09 (hundred-and-sixteenth instalment) -- **Differentiation under the band integral.**

  * **`norm_bandKernel`** -- the kernel has modulus one, since its exponent is purely imaginary.
  * **`continuous_bandKernel_snd`**.
  * **`hasDerivAt_bandTransform`** --

    ```text
    d/dx integral_{-1}^{1} k(x,t) f(t) dt = integral_{-1}^{1} k(x,t) (i c t) f(t) dt
    ```

    for every interval-integrable `f`, by dominated-convergence differentiation with majorant
    `(|c| + 1) ‖f‖`.

  The majorant is what makes this unconditional: on the band `|t| <= 1`, so the kernel's
  `x`-derivative has modulus `|c t| <= |c|`, and no decay or smoothness of `f` is needed beyond
  integrability.  This is the interchange the previous instalment named as the remaining gap
  between the kernel identity and the commutation of operators.

  A trap: `Set.uIoc (-1) 1` and `Set.Ioc (-1) 1` are propositionally but not syntactically equal,
  and `IntervalIntegrable.1.aestronglyMeasurable` produces the `Ioc` form while the
  dominated-convergence lemma wants the `uIoc` form.  `Set.uIoc_of_le` bridges them; without it the
  error reads as a type mismatch between two identical-looking measures.

- 2026-08-09 (hundred-and-seventeenth instalment) -- **The second derivative under the band
  integral.**

  * **`intervalIntegrable_kernelMul`** -- a bounded continuous multiplier preserves interval
    integrability on the band, with the bound supplied explicitly.
  * **`hasDerivAt_bandTransformDeriv`** --

    ```text
    d/dx integral k(x,t) (i c t) f(t) dt = integral k(x,t) (-(c t)^2) f(t) dt.
    ```

  The band transform of an integrable `f` is therefore twice differentiable in `x`, with both
  derivatives given by integrals of the same `f` against modified kernels.  The second application
  of `hasDerivAt_bandTransform` is to the source `(i c t) f(t)`, which is integrable because
  `|c t| <= |c|` on the band -- the same bound that made the first differentiation work.

  With this the three ingredients of the commutation argument are all in place: the pointwise
  kernel identity, the symmetry of the operator on the band, and both differentiations under the
  integral sign.  What remains is the bookkeeping that combines them into
  `L_x (K f) = K (L_t f)`.

- 2026-08-09 (hundred-and-eighteenth instalment) -- **The prolate operator moves onto the kernel's
  second variable.**

  * **`intervalIntegrable_bandKernel_mul`** -- integrability of the kernel times a bounded
    continuous multiplier times an integrable source.
  * **`prolateAction_bandTransform_eq`** --

    ```text
    (1 - x^2) (K f)'' - 2x (K f)' - c^2 x^2 (K f)
      = integral_{-1}^{1} [prolate symbol in t] k(x,t) f(t) dt,
    ```

    where the left side uses the two differentiations under the integral and the right side is the
    operator acting in `t`.

  This is the half of the commutation that needs the kernel identity, and it holds for **every**
  interval-integrable `f` -- no smoothness, no decay, no eigenfunction property.  The remaining half
  is the integration by parts that moves the operator from the kernel onto `f`, which is
  `integral_prolate_pairing_eq_zero` and needs `f` twice differentiable with the two derivatives
  interval-integrable.

  Combining the two gives `L(K f) = K(L f)`: the commutation the classical spectral identification
  rests on.

- 2026-08-09 (hundred-and-nineteenth instalment) -- **THE COMMUTATION, PROVED.**

  ```text
  prolateAction_bandTransform_commutes :
    (1 - x^2) (K f)'' - 2x (K f)' - c^2 x^2 (K f)
      = integral_{-1}^{1} k(x,t) (L f)(t) dt,
  ```

  for every `f` that is interval-integrable, twice differentiable on the band, and whose two
  pairings against the kernel are integrable.  `L f = ((1-t^2) f')' - c^2 t^2 f`.

  This is the classical fact the whole spectral identification rests on: **the finite Fourier
  transform commutes with the prolate differential operator on the band.**  Its three ingredients,
  all now formalized:

  1. `prolate_bandKernel_symm` -- the operator acts identically on the kernel's two variables;
  2. `hasDerivAt_bandTransform`, `hasDerivAt_bandTransformDeriv` -- both differentiations under the
     integral, with the majorant `(|c|+1)‖f‖` supplied by `|t| <= 1` on the band;
  3. `integral_prolate_pairing_eq_zero` -- the operator is symmetric on the band, because `1 - t^2`
     vanishes at both endpoints.

  A consequence worth recording for the card: an eigenfunction of the band transform is, up to the
  usual regularity, an eigenfunction of the prolate operator, and hence satisfies the eigen-equation
  that `prolate_boundedVariationOn_of_nontrivial` consumes.  The two halves of item 7 -- the
  variation law and the spectral identification -- are now joined by a formalized bridge; what is
  still missing is only the regularity of the specific representative, not the mechanism.

  A note on tactics: `linarith` cannot discharge `a - b = 0 |- a = b` over `ℂ`, since `ℂ` is not
  ordered.  `sub_eq_zero.mp` is the right move and reads better anyway.

- 2026-08-09 (hundred-and-twentieth instalment) -- **The regularity bootstrap.**

  * **`bandEigenDeriv`, `bandEigenSecondDeriv`** -- the two derivatives of a band-transform
    eigenfunction, given as transforms of the same eigenfunction against differentiated kernels.
  * **`hasDerivAt_bandEigen`, `hasDerivAt_bandEigenDeriv`, `continuous_bandEigen`** -- an
    eigenfunction of the band transform is continuous and twice differentiable, *with no smoothness
    assumed*: the regularity is inherited from the kernel through the eigen-equation
    `chi f = K f`.

  This is the missing regularity of the representative.  The commutation theorem
  `prolateAction_bandTransform_commutes` requires `f` twice differentiable on the band; for a band
  eigenfunction that is now automatic, so the commutation applies to exactly the objects the card
  cares about.

  A trap: rewriting the eigen-equation as `f = fun y => chi^{-1} (K f) y` and then `rw`-ing it into
  the goal replaces `f` *inside the integral too*, producing a nested transform that does not match.
  `HasDerivAt.congr_of_eventuallyEq` transfers the derivative without touching the integrand, which
  is the only way to use an eigen-equation as a rewriting rule for the function it defines.

- 2026-08-09 (hundred-and-twenty-first instalment) -- **The prolate operator preserves the band
  eigenspace.**

  ```text
  prolateAction_bandEigen_isEigen :
    chi * (L f)(x) = integral_{-1}^{1} k(x,t) (L f)(t) dt
  ```

  whenever `chi f = K f` with `chi != 0`.  In words: if `f` is an eigenfunction of the finite
  Fourier transform with eigenvalue `chi`, so is `L f`, with the *same* eigenvalue.

  This is the classical statement that the two operators share their eigenspaces, and it is the
  whole content of the spectral identification.  When `chi` is a simple eigenvalue the conclusion
  forces `L f = alpha f` for a scalar `alpha` -- the prolate eigen-equation, which is exactly what
  `RHTower.prolate_boundedVariationOn_of_nontrivial` and the whole `(19e)` chain consume.

  Every step is now formalized except that simplicity, which is a spectral fact about the operator
  and not a property of the differential equation.  The chain reads:

  ```text
  chi f = K f  (band eigenfunction)
    -> f twice differentiable            (hasDerivAt_bandEigen, ...Deriv)
    -> L (K f) = K (L f)                 (prolateAction_bandTransform_commutes)
    -> chi (L f) = K (L f)               (this instalment)
    -> [chi simple] L f = alpha f        (spectral input, open)
    -> Var(f) = O(1)                     (prolate_boundedVariationOn_of_nontrivial)
  ```

- 2026-08-09 (hundred-and-twenty-second instalment) -- **Simplicity gives the prolate
  eigen-equation; the spectral identification is closed modulo one spectral input.**

  * **`prolateAction_bandEigen_eq_smul`** -- if every band eigenfunction with eigenvalue `chi` is a
    multiple of `f`, then `L f = alpha f` for a scalar `alpha`: `f` solves the prolate differential
    equation.

  The simplicity hypothesis is now an explicit Lean hypothesis rather than prose in the card.  That
  matters: it makes precise that the *only* thing separating a band eigenfunction from a prolate
  mode is a statement about the multiplicity of the eigenvalue, and that nothing about the
  differential equation, the kernel, or the regularity remains to be proved.

  Item 7 and `(35)` therefore reduce to: the classical `h_0, h_4` eigenvalues of the even time-band
  operator are simple.  That is a spectral fact about a specific operator -- the kind of statement
  the corpus's `ConstrainedProlateSpectralIdentification` and `ConstrainedProlateConstrainedSpectrum`
  modules address -- and it is not reachable from the analysis in this chain.

  `formal lint` passes over the whole tree.

- 2026-08-09 (hundred-and-twenty-third instalment) -- **The complex-to-real bridge: the two halves
  of item 7 joined in Lean.**

  * **`prolateActionC_ofReal`** -- the complex prolate action applied to a real function through the
    coercion is the coercion of the real action.
  * **`prolateSLAction_eq_of_prolateActionC`** -- hence a complex eigen-equation with a real
    eigenvalue *is* the real eigen-equation, by injectivity of the coercion.
  * **`prolate_boundedVariationOn_of_complex_eigen`** -- a real solution of the complex
    eigen-equation has bounded variation on `[-r, r]`, with every hypothesis except nontriviality
    and the eigen-equation itself discharged.

  The spectral half of the card produces a *complex* eigen-equation (the band transform has complex
  eigenvalues and the kernel is complex); the variation half consumes a *real* one.  Those were two
  separate developments in the tree and nothing connected them.  They are connected now, and the
  connector is one coercion lemma -- which is the right size for the gap, but it had to be written
  before either half could be used with the other.

  The card's route is therefore formalized end to end except for three spectral inputs, all named
  and none analytic: the Gram convergence, `(4)`, and simplicity of the `h_0, h_4` eigenvalues.

- 2026-08-09 (hundred-and-twenty-fourth instalment) -- **Simplicity is an ODE fact: the Wronskian
  vanishes.**

  * **`hasDerivAt_prolateWronskian_eq_zero`** -- the Lagrange bracket `(1-x^2)(u'v - uv')` has zero
    derivative when `u` and `v` solve the same prolate eigen-equation, because its derivative is
    `(L u)v - u(L v) = alpha u v - u alpha v = 0`.
  * **`prolateWronskian_eq_zero`** -- hence the Wronskian is constant, and its value at `x = 1` is
    zero because the weight `1 - x^2` vanishes there.  So it vanishes identically.

  This changes the status of the last spectral input.  Simplicity of the eigenvalue was described
  in the card as a spectral fact about the operator; for the *differential* operator it is not --
  it is the vanishing of the Wronskian, which follows from the Lagrange identity plus the weight's
  zero at the band edge, with no spectral theory at all.  Two prolate modes with the same eigenvalue
  satisfy `u'v - uv' = 0` on the open band, hence are proportional wherever either is nonzero.

  What this does *not* yet give is proportionality as a global statement (dividing by a solution
  that may vanish), nor simplicity of the *band transform's* eigenvalues, which is a different
  operator.  But the mechanism for the differential side is now a theorem rather than an assumption.

- 2026-08-09 (hundred-and-twenty-fifth instalment) -- **Two prolate modes with the same eigenvalue
  are proportional.**

  * **`deriv_sub_const_mul`, `prolateSLAction_sub_const_mul`** -- linearity of the prolate action.
  * **`prolate_eq_const_mul_of_same_eigenvalue`** --

    ```text
    v = (v x0 / u x0) * u    on [-r, r],    whenever u x0 != 0.
    ```

  The proof is the classical one, assembled from pieces built earlier in this session: the
  Wronskian vanishes (`prolateWronskian_eq_zero`), so at a point where `u` is nonzero the
  difference `w = v - (v/u) u` has a double zero; `w` solves the same equation by linearity; and
  Grönwall uniqueness (`eq_zero_of_double_zero_interior`) kills it.

  **Simplicity of the prolate eigenvalues is therefore a theorem here, not an assumption.**  The
  eigenspace of the differential operator on `[-r, r]` is one-dimensional as soon as one mode is
  nonzero somewhere -- no spectral theory, no Frobenius analysis at the singular endpoints, no
  compactness.  The three ingredients are the Lagrange identity, the vanishing of the weight at the
  band edge, and Grönwall.

  What remains open is the *band transform's* spectrum, a different operator: `(4)` and the Gram
  convergence.  The differential side of item 7 is closed.

- 2026-08-09 (hundred-and-twenty-sixth instalment) -- **The derivative tower: band eigenfunctions
  are smooth to all orders.**

  * **`bandTransformPow`** -- the eigenfunction paired against the kernel differentiated `n` times.
  * **`intervalIntegrable_kernelPow_mul`** -- the `n`-th power of the bounded factor `i c t`
    preserves integrability, with bound `|c|^n`.
  * **`hasDerivAt_bandTransformPow`** -- each rung of the tower differentiates to the next.
  * **`bandTransformPow_zero`** -- the tower starts at the eigenfunction itself.

  So a band eigenfunction has derivatives of every order, each given by an integral of the *same*
  eigenfunction against a modified kernel.  The argument is identical at every rung because
  differentiating the kernel only raises the power of a factor bounded by `|c|` on the band; no new
  estimate is needed, which is why the classical statement "band-limited functions are entire" is
  really a statement about that one bound.

  Only the base case uses the eigen-equation.  The tower itself is a property of the transform, so
  the same statement holds for the transform of any integrable source.

- 2026-08-09 (hundred-and-twenty-seventh instalment) -- **Smoothness of the eigenfunction, in
  consumable form.**

  * **`iteratedDeriv_bandEigen`** -- `iteratedDeriv n f = bandTransformPow c chi f n`, by induction
    on the tower.
  * **`differentiable_iteratedDeriv_bandEigen`** -- every iterated derivative is differentiable.

  A band eigenfunction is therefore smooth, and the statement is now in the form downstream work
  actually uses: `Differentiable (iteratedDeriv n f)` for every `n`, rather than a bare existence of
  derivatives.  In particular `Differentiable f` and `Differentiable (deriv f)` -- the two
  hypotheses of every theorem in the variation chain -- are the cases `n = 0` and `n = 1`.

  This closes the regularity side completely.  Combined with the commutation, the simplicity of
  prolate eigenvalues, and the complex-to-real bridge, a band eigenfunction that is real-valued and
  nonzero somewhere has bounded variation on every compact subinterval of the open band, with no
  hypothesis beyond the eigen-equation itself.

- 2026-08-09 (hundred-and-twenty-eighth instalment) -- **A real band eigenfunction has bounded
  variation.**

  * **`differentiable_of_ofReal`** -- differentiability descends through the real coercion.
  * **`deriv_ofReal_eq`** -- the derivative of a coerced real function is the coercion of its
    derivative.
  * **`bandEigen_real_boundedVariationOn`** -- the composite: a real solution of the coerced complex
    prolate eigen-equation, nonzero somewhere and bounded, has bounded variation on `[-r, r]` with
    the explicit count bound.

  Every hypothesis of the variation chain is now discharged from the eigen-equation itself:
  regularity from the derivative tower, the prolate equation from the commutation, simplicity from
  the vanishing Wronskian.  The only inputs left are the ones the card names as spectral -- the
  Gram convergence and `(4)` -- neither of which concerns the differential equation.

  The `deriv`-ordering trap appeared twice more in this instalment and is worth stating as a rule:
  when rewriting both `deriv g` and `deriv (deriv g)`, always rewrite the *double* first.  Rewriting
  the single first replaces the inner occurrence of the double as well, after which the double's
  rewrite has nothing to match.

## Lean map of the route (as of 2026-08-09)

Every entry is an unconditional, axiom-clean theorem in this tree.  Namespaces: `HTGeometry` for
the reusable layers, `RHTower` for the route-specific ones.

**The exact mode as an oscillator**
| statement | theorem |
|---|---|
| energy method, phase-free | `HTGeometry.oscEnergy_le_exp`, `abs_oscCoeff_le_base` |
| energy method in a phase parameterization | `HTGeometry.phaseEnergy_le_exp`, `abs_phaseCoeff_le_base` |
| the mode is a perturbed oscillator | `RHTower.prolateOsc_ode` |
| the perturbation is admissible | `RHTower.abs_prolateOscPotential_le` (`\|q\| <= 35/phi^2`) |
| exact two-branch representation | `RHTower.sqrt_mul_radialProlate_dilate_eq_branches` |

**The primitive estimates**
| statement | theorem |
|---|---|
| `(16)` full channel range | `RHTower.norm_integral_radialProlate_dilate_left_le` |
| `(17)` first channel | `RHTower.norm_integral_radialProlate_first_channel_le` |
| `(11)` | `RHTower.tsum_norm_integral_radialProlate_all_channels_le` |
| `(12)` exponential substitution | `HTGeometry.integral_exp_half_comp_exp` |
| passage from finite radial sums | `HTGeometry.abs_halfLineExpPrimitive_limit_le`, `RHTower.abs_halfLineExpPrimitive_channelTruncation_le` |

**The polar source estimate**
| statement | theorem |
|---|---|
| `(7)`,`(8)` growing branch | `HTGeometry.abs_integral_exp_half_mul_autocorrelation_le` |
| `(9)` decaying branch | `HTGeometry.abs_halfLineAutocorrelation_le`, `abs_integral_exp_neg_half_mul_autocorrelation_le` |
| `(10)` | `HTGeometry.abs_polarCharge_le` |
| `(18)` for the limit object | `RHTower.abs_polarCharge_radialLimit_le` |

**`(19e)` and the variation law**
| statement | theorem |
|---|---|
| Darboux monotone cell | `HTGeometry.monotoneOn_or_antitoneOn_of_deriv_ne_zero` |
| ordered partition assembly | `HTGeometry.exists_monotone_partition_of_finset` |
| Gronwall uniqueness | `HTGeometry.eq_zero_of_double_zero_interior` |
| simple zeros are finite | `HTGeometry.finite_zeros_of_nontrivial` |
| `(19e)` | `RHTower.prolate_boundedVariationOn_of_nontrivial` |

**The spectral identification `(35)`**
| statement | theorem |
|---|---|
| kernel identity | `RHTower.prolate_bandKernel_symm` |
| symmetry on the band | `RHTower.integral_prolate_pairing_eq_zero` |
| differentiation under the integral | `RHTower.hasDerivAt_bandTransform`, `...Deriv` |
| the commutation | `RHTower.prolateAction_bandTransform_commutes` |
| eigenspace preserved | `RHTower.prolateAction_bandEigen_isEigen` |
| smoothness of eigenfunctions | `RHTower.differentiable_iteratedDeriv_bandEigen` |
| prolate eigenvalues are simple | `RHTower.prolate_eq_const_mul_of_same_eigenvalue` |
| real band eigenfunction is BV | `RHTower.bandEigen_real_boundedVariationOn` |

**Still open, all spectral, none analytic**: the weighted projective Gram convergence
`R_(lambda,N) -> R_lambda`; `(4)` `‖R_lambda‖_2^2 = O(d_lambda)`; exhibiting the classical
`h_0, h_4` modes.

- 2026-08-14 (hundred-and-twenty-ninth instalment) -- **The mode's `1/x` decay, and the first
  unconditional `(18)`.**  Two new modules,
  `HTGeometry/HalfDensityEnvelopePolarCharge.lean` and `RHTower/ProlateRadialDecay.lean`, both
  wired, all declarations axiom-clean.

  * **`HTGeometry.abs_polarCharge_le_of_envelope`** -- the abstract polar estimate took *ten*
    separate integrability inputs.  One pointwise envelope `|R(s)| <= K exp(-s/2)` plus continuity
    supplies all of them, and the conclusion becomes explicit:

    ```text
    |PPol(R, a)| <= 4 M K + 4 K².
    ```

    The square, the two shifted integrands and the decaying branch are all dominated by a multiple
    of `exp(-s)`; the two-dimensional cross integrand by `K² exp(a) exp(-s)` on the lag rectangle,
    where the weight `exp(eps h/2)` is at most `exp a` for `|eps| = 1` and `0 < h <= 2a`; and the
    two weighted autocorrelation integrands come from that product integrability through
    `Integrable.integral_prod_left`, which is exactly Fubini in the direction the estimate needs.
  * **`RHTower.abs_radialProlate_dilate_le`, `abs_radialProlate_le`** -- the two exponential
    branches have unit modulus, so the exact two-branch representation and the amplitude bound
    `|a| <= 300 M/(sqrt c · k · sqrt x)` give

    ```text
    |R (k x)| <= 600 M / (sqrt c · k · x),      k >= 1, x >= 1, k x >= 2.
    ```

    This is `(14)` read on the mode itself rather than on its amplitudes.
  * **`RHTower.abs_channelSource_le`, `integral_channelSource_sq_le`,
    `summable_channelSource_sq_bound`** -- in the logarithmic variable the `1/x` decay is exactly
    the half-density envelope `|H_k(u)| <= (C/k) exp(-u/2)`, so the `k`-th channel has squared mass
    at most `C²/k²` and the channel masses are summable.
  * **`RHTower.abs_polarCharge_channelSource_le_of_ode`** -- combining the two: **`(18)` holds
    unconditionally for every exterior channel `k >= 2` of the exact radial mode**, with nothing
    assumed beyond the radial differential equation.  This is the first instance of `(18)` in the
    tree with no integrability side conditions at all.

  What this does *not* give is `(18)` for the radial *sum*.  The channel masses are square
  summable, not summable: `‖H_k‖₂ <= C/k` and `sum 1/k` diverges, so the radial series converges
  in `L²` only through the almost-orthogonality of the dilates -- which is precisely the weighted
  projective Gram theorem the card cites as an outside input.  The instalment sharpens the shape of
  that remaining input: what is missing is a Bessel/Gram inequality for `{R(k ·)}`, and the size
  data it would consume (`C²/k²` per channel) is now a theorem.

- 2026-08-14 (hundred-and-thirtieth instalment) -- **`(4)` is unconditional for the radial lattice
  source.**  New module `HTGeometry/RadialLatticeSourceEnvelope.lean`, wired, axiom-clean.

  The BV quadrature envelope was already in the tree, stated for the quadrature
  `sqrtRadialLatticeQuadrature g k n` at a *given* index `n`.  What was missing was the object the
  card actually uses: the physical lattice charge

  ```text
  Q(a) = sum_(n >= 1) g(n/a),          b_lambda(t) = Q(a)/sqrt a,   a = lambda exp t,
  ```

  as a function of the radial scale, with no index to choose.

  * **`latticeCharge`, `radialLatticeSource`, `radialLogSource`** -- the charge as a `tsum`.  It is
    a finite sum: `latticeCharge_eq_sum` shows every term past `a L` vanishes, for any cutoff index
    with `L < (n+1)/a`.
  * **`radialLatticeSource_eq_quadrature`** -- at the floor index `n = floor (a L)` *both* sides of
    the BV envelope's index condition hold at once (`n/a <= L` and `L < (n+1)/a`), and the third
    fact -- that the terms past `n` vanish -- is the same inequality.  So the charge *is* the
    quadrature, and **`norm_radialLatticeSource_le`** gives `‖b‖ <= (2/sqrt a) Var(g)`.
  * **`abs_radialLogSource_le`** -- in the logarithmic variable this is exactly `(19c)`:

    ```text
    |b_lambda(t)| <= (2 Var(g)/sqrt lambda) exp(-t/2).
    ```

  * **`continuous_radialLogSource`** -- the charge is continuous in the scale.  The proof is the
    local-finiteness one: on `(-infinity, t+1)` the index `N = ceil (lambda exp(t+1) L)` already
    exceeds `a L`, so the `tsum` *is* the fixed finite sum there, and a finite sum of continuous
    terms is continuous.  This is the only place the vanishing hypothesis past `L` is used twice.
  * **`integral_sq_radialLogSource_le`** -- **`(4)`**: the source's squared mass on the half line is
    at most `(2 Var(g))²/lambda`, with no integrability hypothesis at all.
  * **`abs_polarCharge_radialLogSource_le`** -- **`(18)`** for the radial lattice source: every
    integrability input of the abstract polar estimate is discharged, and the *only* remaining
    hypothesis is the primitive bound `sup_t |A(t)| <= M`, i.e. `(11)`.

  The card's route for `(18)` is therefore reduced to a single missing link: the primitive bound
  `(11)`, proved in the tree for the *channel* decomposition, has to be transported to the *lattice*
  representation.  The two representations are the two sides of the one-sided Poisson--Muntz
  formula, whose Abel boundary value the tree already computes as
  `g(0)/(2 sqrt b) + (sum_n g((n+1)/b))/sqrt b` -- literally the Poisson center plus
  `radialLatticeSource`.  That identification is the next instalment.

- 2026-08-14 (hundred-and-thirty-first instalment) -- **The Abel boundary value *is* the full radial
  source.**  New module `RHTower/PoissonMuntzRadialSource.lean`, wired, axiom-clean; the real
  full-source layer added to `HTGeometry/RadialLatticeSourceEnvelope.lean`.

  * **`HTGeometry.eVariationOn_ofReal`** -- complexification does not change total variation, in
    both directions, from `LipschitzOnWith.comp_eVariationOn_le` applied to `ofReal` and to `re`.
    This is the connector the tree lacked: the BV envelope is stated for complex sources, the
    variation bound `(19e)` for real ones.
  * **`HTGeometry.latticeCharge_ofReal`, `radialLogSource_ofReal`** -- the complexified lattice
    charge is the complexification of the real one, so the real radial source is literally
    `(sum_n f(n/a))/sqrt a`.
  * **`HTGeometry.radialFullLogSource`** -- the card's `R_lambda`: Poisson centre plus lattice
    charge.  **`abs_radialFullLogSource_le`** is `(19d)`,

    ```text
    |R_lambda(t)| <= ((2 Var(g) + |g(0)|/2)/sqrt lambda) exp(-t/2),
    ```

    **`integral_sq_radialFullLogSource_le`** is `(4)`, and
    **`abs_polarCharge_radialFullLogSource_le`** is `(18)` for it with only the primitive bound left.
  * **`RHTower.tendsto_sqrt_mul_poissonMuntzAbelSum_eq_radialFullLogSource`** -- `(19a)`--`(19b)`:
    the Abel boundary value of the square-root normalized radial sum is exactly
    `radialFullLogSource`.  So the object the envelope estimates speak about is the object the
    Poisson--Muntz law produces; the two halves of the card's source analysis now refer to one
    function.

  The remaining link is unchanged in kind and smaller: transport the primitive bound `(11)` --
  proved for the channel representation -- to this object, and discharge the five source-side
  hypotheses (continuity, BV on `[0, L]`, one-sided zero mean, vanishing at and past the endpoint)
  for the actual constrained two-mode representative.

- 2026-08-14 (hundred-and-thirty-second instalment) -- **The estimates now accept the actual
  half-endpoint source: continuity is not required.**  Same two modules, extended; axiom-clean.

  The card's source is `realSymmetricHalfEndpointCutoff`, which takes the *half* value at the
  support endpoint.  It is therefore **not continuous**, and the lattice charge inherits a jump each
  time a lattice point crosses the endpoint.  Every estimate in the previous two instalments assumed
  continuity, so none of them applied to the object the card actually builds.

  * **`HalfDensityEnvelopePolarCharge`** is relaxed from `Continuous R` to `Measurable R` together
    with local integrability of the growing branch.  Continuity was only ever used for
    measurability and for the primitive's continuity, and the latter is
    `intervalIntegral.continuous_primitive` applied to the local-integrability hypothesis itself.
  * **`abs_radialLogSource_le_of_bound`** -- the lattice charge has at most `floor (a L)` nonzero
    terms, so a bounded source gives `|b_lambda(t)| <= sqrt(a) L C_g`, hence a bound on every left
    ray.  This is what replaces continuity: the source is bounded on `(-infinity, T]` for every `T`,
    which is exactly what interval integrability needs.
  * **`measurable_radialLogSource`** -- measurability by a pointwise limit: the partial sums are
    measurable and are *eventually constant* in `N` at each `t`, since past `floor (a L)` the terms
    vanish.
  * **`intervalIntegrable_expHalf_mul_radialLogSource`**, **`..._radialFullLogSource`** -- the
    growing branch is interval integrable.  The centre term needs no estimate at all: the identity
    `exp(t/2) · g(0)/(2 sqrt(lambda exp t)) = g(0)/(2 sqrt lambda)` makes it a **constant**.
  * **`integral_sq_radialFullLogSource_le_of_measurable`** -- `(4)`, and
    **`abs_polarCharge_radialFullLogSource_le_of_measurable`** -- `(18)`, for a measurable bounded
    compact source with the four BV/mean/endpoint hypotheses, with the primitive bound the only
    remaining input.

  All source-side hypotheses of `(18)` are therefore discharged for the shape the card's
  representative actually has.  What remains is the single analytic link named in the previous
  instalment: transporting the primitive bound `(11)` from the channel representation to the lattice
  representation.

- 2026-08-14 (hundred-and-thirty-third instalment) -- **The two-mode constrained source is
  inhabited.**  New module `RHTower/ConstrainedProlateTwoModeInhabited.lean`, wired, axiom-clean.

  Every statement in the tree about the constrained source carried eight hypotheses: two modes, two
  nonzero eigenvalues, two eigen-equations.  Nothing inhabited them, so the whole chain was
  conditional on the existence of a live pair.

  * **`eventually_evenProlateSignedValue_ne_zero_pair`** -- the corpus already proves
    `evenProlateSignedValue a n ^ 2 -> 1` for each fixed signed index, hence
    `eventually_evenProlateSignedValue_ne_zero n`.  Intersecting the two eventualities for
    `n = 0, 1` makes both modes live at once at every large aperture.
  * **`eventually_exists_twoModeConstrainedRealSource`** -- the source built from that pair exists
    and is integrable, even, compactly supported and of total mass zero.
  * **`eventually_exists_tendsto_poissonMuntzAbelSum_radialFullLogSource`** -- and the Abel boundary
    law runs on it: its square-root normalized radial sum converges to its own full radial source.

  So the card's source is no longer hypothetical.  What the greedy exhaustion does *not* decide is
  the classical degree labels: it produces the first two live signed modes, not provably the
  spheroidal degrees `0` and `4`.  Only two statements of the card use the labels -- the ratio
  `d_0/d_1 = O(lambda^-8)` in the `k = 1` transfer, and the Hermite limits of `chi_n` bounding the
  contrast coefficients -- and both are classical PSWF asymptotics, cited.  The construction, the
  envelope `(19c)`--`(19d)`, `(4)`, the variation law `(19e)` and the polar estimate `(18)` are
  label-free and now apply to an object that exists.
