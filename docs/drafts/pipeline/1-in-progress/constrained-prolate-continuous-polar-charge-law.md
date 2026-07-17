# The constrained prolate exterior tail has bounded continuous polar charge

- **ID:** `constrained-prolate-continuous-polar-charge-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / SOURCE ESTIMATE
- **Scientific status:** `[CONJECTURE WITH PROVED REDUCTION] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
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

For the fixed `m=0,4` constrained source, the remaining concrete source-side estimate is

```text
Var(g_lambda^+)=O(1).                                          (19e)
```

It follows from fixed-mode prolate-to-Hermite convergence in `W^(1,1)`; the weaker
`Var(g_lambda^+)=o(lambda*log lambda)` already suffices for the leading law below. This replaces
the former leakage-normalized `z^(-2)` far-field gate by a compact-source regularity theorem.

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
law `(19e)` make `(27)` `O(d_lambda*log(lambda)/lambda)=o(d_lambda)`. Even the weaker variation
target stated after `(19e)` is enough to preserve the positive leading coefficient after its rate
is paired with `(H+1)/lambda`.

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
5. `[PHASE FORMALIZED; AMPLITUDE OPEN]` a concrete radial-PSWF endpoint/exterior interface proving
   the all-radial primitive `(11)`;
6. `[ABEL BOUNDARY FORMALIZED; PERIODIZATION OPEN]` the fixed-mode source variation bound `(19e)`
   and the source-specific Poisson specialization `(19a)`;
7. the constrained-source and critical-Mellin specialization `(18)`--`(32)`.

No abstract hypothesis wrapper is sufficient: the concrete prolate primitive, one-sided Poisson
specialization, and fixed-mode variation estimate must be theorems before `(32)` can be promoted
or used in a paper.

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
- [ ] compute the scaled compact-periodization Fourier coefficients and thereby formalize the exact
  source-specific one-sided Poisson--Muntz specialization `(19a)`
- [ ] prove the fixed-mode source variation bound `(19e)`
- [ ] promote `(18)` and `(32)` after the primitive and source-regularity audits
- [ ] formalize the concrete radial-PSWF primitive theorem and its polar consequence in Lean
- [ ] true even ground/gap comparison
- [ ] locally uniform determinant convergence to `Xi`
