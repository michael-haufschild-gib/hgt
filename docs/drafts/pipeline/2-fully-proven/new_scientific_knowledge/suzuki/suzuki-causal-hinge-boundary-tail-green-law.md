# Suzuki causal hinge boundary--tail Green law

- **ID:** `suzuki-causal-hinge-boundary-tail-green-law`
- **Stage:** 2-fully-proven
- **Type:** RH-FRONTIER SOURCE THEOREM / FAILED PRODUCER / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/suzuki-rooted-midpoint-compound-gram.md`
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiCausalHingeBoundaryTailGreenLaw`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, *Aspects of the screw function corresponding to the Riemann
  zeta function*, arXiv:2206.03682v4, Theorem 1.1(1); M. Suzuki, *Weil's quadratic form via the
  screw function*, arXiv:2606.09096v1, equations (1.3), (2.9)--(2.11), Sections 8.2--8.3

## Frontier under audit

The rooted-midpoint conjecture asked the completed-Xi deficit to pay exact half-gap debt `d^2`
atom by atom through a common-prime Julia--Bianchi Gram.  The corpus's independent cofinal audit
already proves raw critical Bianchi feature has infinite mass.  The present theorem tests a
stronger prerequisite: can one delayed von-Mangoldt hinge itself contribute a positive Pick
kernel after exact finite-aperture cancellation?

Suzuki's positive-half-line prime-power source is

```text
g_n(t)=a_n(t-ell_n)_+,
a_n=Lambda(n)/sqrt(n)>0,   ell_n=log(n)>0.             (1)
```

## Theorem A: delayed-hinge Laplace law `[PAPER-PROVED]`

For `ell>=0`, `Im z>0`, put `h_ell(t)=(t-ell)_+`.  Then

```text
M_ell(z)=integral_0^infinity h_ell(t)exp(i z t)dt
        =-exp(i z ell)/z^2.                            (2)
```

### Proof

The integrand vanishes below `ell`.  An antiderivative on `[ell,infinity)` is

```text
exp(i z t)[(t-ell)/(i z)+1/z^2].                       (3)
```

It tends to zero at infinity because `Im z>0`; its value at `ell` is
`exp(i z ell)/z^2`.  Subtracting the lower endpoint proves `(2)`.  No continuation is used.

## Theorem B: exact boundary--tail Green law `[PAPER-PROVED]`

Let `v` be integrable on `[-a,a]`, with zero mean where the endpoint specialization below uses
it, and define

```text
W(z)=integral_(-a)^a v(y)exp(i z y)dy,

T_(ell,a)(z)=integral_(-a)^a v(y)exp(i z y)
  integral_0^(a-y)(t-ell)_+ exp(i z t)dt dy,

R_(ell,a)=M_ell W-T_(ell,a).                           (4)
```

For `0<=ell<=2a`, put

```text
c=a-ell,
B_c=integral_(-a)^c v(y)dy,
A_c=integral_(-a)^c(c-y)v(y)dy,
W_[c,a](z)=integral_c^a v(y)exp(i z y)dy.              (5)
```

Then

```text
R_(ell,a)(z)
 =-exp(i z ell)W_[c,a](z)/z^2
  -exp(i z a)[A_c/(i z)+B_c/z^2].                     (6)
```

### Proof

The inner integral in `(4)` is zero unless `y<c`.  For `y<c`, `(3)` gives

```text
integral_0^(a-y)(t-ell)_+exp(i z t)dt
 =exp(i z(a-y))[(c-y)/(i z)+1/z^2]
  -exp(i z ell)/z^2.                                  (7)
```

After multiplication by `exp(i z y)` and integration on `[-a,c]`,

```text
T_(ell,a)
 =exp(i z a)[A_c/(i z)+B_c/z^2]
  -exp(i z ell)W_[-a,c](z)/z^2.                       (8)
```

Insert `(2)`, split `W=W_[-a,c]+W_[c,a]`, and cancel low Fourier mass before taking any limit.
This proves `(6)`.

At `ell=2a`, `c=-a`, so `A_c=B_c=W_[-a,c]=0`; `(6)` joins exactly to `(2)W`.  At `ell=0`,
`c=a`, zero mean gives `B_c=0`, `A_c=-integral yv(y)dy`, and `(6)` reduces to constant exterior
tail forced by first source moment.  Both endpoints agree with direct convolution.

## Theorem C: finite-aperture visibility trichotomy `[PAPER-PROVED]`

If `ell>=2a`, then `a-y<=2a<=ell` for every `y in [-a,a]`.  Thus

```text
T_(ell,a)=0,
R_(ell,a)(z)=-exp(i z ell)W(z)/z^2.                   (9)
```

Consequently:

1. prime powers `n<exp(2a)` enter local Volterra operator through boundary--tail law `(6)`;
2. entry wall `n=exp(2a)` has no discontinuity or half-atom ambiguity;
3. every prime power `n>exp(2a)` is invisible to local phase operator but survives as pure global
   Xi multiplier channel `(9)`.

This proves fixed finite common-prime carrier cannot equal complete compound source.

## Theorem D: one far prime has both Pick signs `[PAPER-PROVED]`

The physical Suzuki multiplier is `i` times Xi-real multiplier, while normalized interval is
`-i` times physical triangle.  Therefore a far prime with weight `a_n` contributes to jump
quotient

```text
m_(n,a)(z)=-i a_n exp(i z ell_n)/z^2.                 (10)
```

For scalar Pick kernel

```text
K_m(z,w)=[m(z)-conj(m(w))]/[z-conj(w)],
K_m(z,z)=Im(m(z))/Im(z).                               (11)
```

At `z=i*pi/ell`, `(10)` gives

```text
Im m(z)=a_n exp(-pi)/(pi/ell)^2>0.                    (12)
```

At the phase-aligned upper-half-plane point

```text
x=2pi/ell,   y=pi/ell=x/2,   z=x+i y,                (13)
```

one has `exp(i z ell)=exp(-pi)>0`.  Since

```text
Im[-i/z^2]=-(x^2-y^2)/(x^2+y^2)^2<0,                 (14)
```

equations `(10)--(11)` give

```text
K_m(i*pi/ell,i*pi/ell)>0,
K_m(2pi/ell+i*pi/ell,2pi/ell+i*pi/ell)<0.             (15)
```

Hence one actual positive von-Mangoldt hinge is not a positive Pick atom.

## Theorem E: compound denominator cannot repair atomwise sign `[PAPER-PROVED]`

For any compound denominator `D`, diagonal congruence is

```text
D(z)conj(D(z))K_m(z,z)=|D(z)|^2 K_m(z,z).             (16)
```

At phase-aligned node `(13)`, if `D(z)!=0`, `(15)--(16)` remain strictly negative.  Therefore no
factorization of specialized compound Bezoutian as direct sum of independent positive
prime-power kernels can match actual source.  Adding separate positive archimedean remainder does
not turn each claimed prime summand positive; required factorization must mix source channels
before sign is taken.

## Completed source coefficient audit

Write `lambda_k=2k+1/2`.  Suzuki's Lerch term expands for `t>0` as

```text
(1/4)e^(-t/2)Phi(e^(-2t),2,1/4)
 =sum_(k>=0)e^(-lambda_k t)/lambda_k^2.               (17)
```

The exact second-derivative source is therefore

```text
-g''
 =e^(t/2)+e^(-t/2)-sum_(k>=0)e^(-lambda_k t)
  -sum_(n>=2) Lambda(n)/sqrt(n) delta_(log n),         (18)
```

away from origin convention.  Regular part simplifies to the corpus formula

```text
e^(t/2)-e^(-5t/2)/(1-e^(-2t)).                        (19)
```

Thus prime atoms have opposite distributional sign to polar--Gamma channel.  Equations
`(15)` and `(18)` independently force collective prime--Gamma cancellation; neither raw prime
Gram nor separated positive archimedean remainder has correct source type.

## Hostile verdict on rooted-midpoint conjecture

`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`, in its stated atom-by-atom/direct-sum form, is
`[FALSIFIED]` twice:

1. critical rooted Bianchi mass diverges cofinally;
2. even at one finite far prime, actual Pick diagonal has both signs.

Exact half-gap debt `d^2` and midpoint Lorentz completion remain valid.  What fails is proposed
producer, not required completion amount.

## Strongest positive survivor and corrected RH frontier

### `SUZUKI-CAUSAL-APERTURE-ENTRY-COMPOUND-WELD` `[CONJECTURE]`

For one recurrence-selected aperture and admissible midpoint shift pair:

1. insert actual resolvent-dependent deficiency source into every finite-delay boundary law `(6)`;
2. keep complete far-prime tail `(9)` joined to exact polar--Gamma channel `(17)--(19)`;
3. assemble these inside canonical compound Bezoutian before any Gram or cofinal limit;
4. prove collective kernel pays exact rooted half-gap debt `d^2` and is positive.

This is sharper than “find prime--Gamma Gram.”  It requires a source covariance mixing aperture
entries and polar--Gamma tail.  Direct sum over prime powers, fixed finite common-prime carrier,
or raw critical Bianchi limit is impossible.  One negative principal minor of already-assembled
kernel refutes conjecture.  Proving it gives compound Pick positivity, existing pole tomography,
and RH.

## Novelty audit

- Laplace transform `(2)` and integration formula `(6)` are classical delayed-integrator
  calculus: `[BRIDGE]`.
- Suzuki 2023 states one-sided screw multiplier; Suzuki 2026 states screw source and finite
  operator construction.  Neither primary paper gives aperture wall `(6)`, far-prime visibility
  trichotomy, phase-aligned Pick sign change `(15)`, or consequence for compound Gram.
- Targeted arXiv searches for Suzuki screw/Volterra delayed-hinge boundary tails and Pick kernels
  found Suzuki papers but no matching source theorem.  Exact source-specific synthesis and
  frontier correction are `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; priority remains unverified.

## Formalization

`SuzukiCausalHingeBoundaryTailGreenLaw.lean` proves:

```text
suzukiDelayedHingeExteriorFromCut_eq_boundaryTail
suzukiDelayedHingeExteriorFromCut_entryWall
I_mul_suzukiDelayedHingeMultiplier
suzukiScalarPickKernel_self_eq_im_div
suzukiCriticalDelayedHingeJumpAtom_im_pos_vertical
suzukiCriticalDelayedHingeJumpAtom_im_neg_phaseAligned
suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_pos_vertical
suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_neg_phaseAligned
suzukiCompoundDenominatorScaledPick_self_eq
suzukiCompoundDenominatorScaledPick_delayedHinge_neg_phaseAligned
```

Physical integral evaluation `(2)--(9)` is proved on paper.  Lean formalizes exact closed-form
cancellation, entry wall, both source-specific Pick signs, and compound-denominator preservation.
No abstract positivity hypothesis represents missing RH theorem.

## Gates

- [x] internal corpus and primary source audit
- [x] delayed-hinge Laplace law
- [x] exact boundary--tail cancellation
- [x] endpoint and visibility classification
- [x] two-sign Pick diagonal theorem
- [x] compound-denominator sign preservation
- [x] archimedean/polar coefficient audit
- [x] atomwise direct-sum conjecture retired with positive survivor
- [x] dependency-closed algebraic core formalized
- [ ] collective aperture-entry compound weld

