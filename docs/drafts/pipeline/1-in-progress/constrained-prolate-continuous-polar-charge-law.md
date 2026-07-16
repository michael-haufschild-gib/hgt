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

## Summed radial envelope

The center-cross estimate below needs one pointwise envelope, but no sharp constant.  Dunster's
exterior phase satisfies

```text
xi_c(z)+J(sigma_c)=z+O(z^(-1)),                                (19a)
```

and the exact interaction-picture amplitudes have limits at infinity, with tails
`O((c*z)^(-1))`.  The limiting two-branch combination is pinned by the exact Fourier endpoint
identity: because the compact source is even, its `z^(-1)` term is the sine term and there is no
cosine term of that order.  Consequently, for `z` larger than a fixed multiple of `c`,

```text
q_lambda(lambda*z)
 =g_lambda(lambda)/(pi*lambda*z)*sin(c*z)
  +sqrt(d_lambda/lambda)*E_lambda(z),                           (19b)

|E_lambda(z)|<=C*c^M/z^2.                                     (19c)
```

For `2<=z<=C*c`, the leading exterior bound itself is

```text
|q_lambda(lambda*z)|
 <=C*sqrt(d_lambda/lambda)/z.                                  (19d)
```

The point of `(19c)`--`(19d)` is that both estimates are normalized by the exterior leakage
`sqrt(d_lambda)`, not by an interior derivative norm.  Formula `(19a)` and Dunster's leading sine
law `(2.22)` give the phase matching; the interaction-picture tail prevents the additive Olver
remainder from losing its oscillatory normalization.

At `z=k*exp(t)`, split at `k*exp(t)=C*c`.  The finite part is bounded by `(19d)` and the harmonic
sum `O(log(2+c))`.  In the tail, the leading terms in `(19b)` sum to the classical bounded
sawtooth series,

```text
sum_(k>=1) sin(k*c*exp(t))/k.                                  (19e)
```

The remainders are absolutely summable by `(19c)`.  The single sector
`1<=z<=2` is covered by the pole-uniform Bessel envelope.  Using

```text
|g_lambda(lambda)|<=C*sqrt(lambda*d_lambda)                    (19f)
```

therefore gives

```text
|R_lambda(t)|
 <=C*log(2+c)*sqrt(d_lambda)*exp(-t/2),        t>=0.             (19g)
```

This is the global summed radial envelope used below.  It is stronger than the ambient Muntz
bound precisely because the radial ODE retains the leakage normalization in `(19c)`--`(19d)`.

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

where `J_H(t)` is the weighted cumulative defect up to `min(H,t)`.  At the full limit,

```text
J(t)=int_0^t exp(h/2)dM(h)
 =exp(t)-1+t-Psi(exp(t))
 =t-1-E(exp(t)).                                                (25)
```

The classical prime-number-theorem remainder gives

```text
|J(t)|<=C*(1+t+exp(t-kappa*sqrt(t)))                            (26)
```

for some `kappa>0`.  Therefore the remaining center audit reduces to the concrete summed radial
envelope

```text
|R_lambda(t)|
 <=C*lambda^M*sqrt(d_lambda)*exp(-t/2),        t>=0,             (27)
```

with one fixed `M`.  Equations `(24)`--`(27)` give

```text
|p_lambda|*
 |int_0^infinity exp(-t/2)R_lambda(t)J(t)dt|
 <=C*lambda^(M-1/2)*d_lambda^(3/2)
 =o(d_lambda).                                                  (28)
```

Equation `(27)` follows from `(19g)` after bounding the logarithm by a fixed power of
`lambda`.  It cannot be replaced by the ambient bounded-variation Muntz estimate, which loses the
factor `sqrt(d_lambda)`.

Once `(27)` is proved, `(22)`--`(28)` yield the genuine global statement

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
closure of the coupled global source law `(32)`.  No parent statement of this continuous polar
estimate was located in the CCM or radial-PSWF literature.  Significance is high if `(17)` and
`(27)` survive formula-level audit because they remove the first analytic source gate in the
determinant route without assuming a Weil floor or an RH-equivalent bound.

## Lean plan

The formal tree already contains the exact finite-dimensional polar signature, the
autocorrelation/Stieltjes identity, and the abstract first-order interaction-picture transport.
The required new infrastructure is:

1. a half-line autocorrelation/Fubini module formalizing `(7)`--`(10)`;
2. a concrete radial-PSWF interface with the pole-uniform Bessel and exterior phase bounds;
3. the summable all-radial primitive estimate `(11)` and summed envelope `(27)`;
4. the constrained-source and critical-Mellin specialization `(18)`--`(32)`.

No abstract hypothesis wrapper is sufficient: the concrete prolate primitive and summed-envelope
estimates must be theorems before `(32)` can be promoted or used in a paper.

## Gates

- [x] exact polar charge reduced to one weighted primitive
- [x] `k>=2` exterior primitive estimate reduced to existing phase-preserving amplitudes
- [x] `k=1` primitive split into endpoint, Bessel, and exterior sectors with summable envelopes
- [x] pass finite radial primitives to the exact radial sum by projective `L2` convergence
- [x] center autocorrelations reduced exactly to the Abel boundary value and the PNT-weighted
  radial integral `(24)`
- [x] reduce the global summed radial envelope to Dunster's phase cancellation `(2.18)`, leading
  sine law `(2.22)`, the exact endpoint coefficient, and the interaction-picture amplitude tail
- [x] audit the constant phase cancellation and leakage normalization against Dunster's formulas
- [ ] formalize the phase-preserving `z^(-2)` tail after exact endpoint matching
- [ ] promote `(18)` and `(32)` after the two analytic audits above
- [ ] formalize the concrete radial-PSWF primitive theorem and its polar consequence in Lean
- [ ] true even ground/gap comparison
- [ ] locally uniform determinant convergence to `Xi`
