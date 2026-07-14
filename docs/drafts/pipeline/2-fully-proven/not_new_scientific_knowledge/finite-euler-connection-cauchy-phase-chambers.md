# Finite Euler connection Cauchy phase chambers

- **ID:** `finite-euler-connection-cauchy-phase-chambers`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[POSITIVE COMPLETION OBLIGATION]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `semilocal-dual-pair-euler-connection-source-law.md`;
  `../3-formalized/finite-blaschke-allpass-group-delay.md`;
  `../3-formalized/not_new_scientific_knowledge/finite-prime-log-flow-spectrum.md`

## Goal

Determine whether the finite Euler connection identified by the semilocal dual-pair theorem already
has the one-Cauchy sign required by the Xi source gate.  It does not have a fixed sign.  More
usefully, its complete sign geometry is an explicit radial Poisson-kernel chamber, and every finite
nonempty prime packet visits both chambers.  This identifies the exact compensation that a
completed prime--Gamma construction must supply.

## One-prime centered source

For a prime `p`, put

```text
Phi_p(s)=log(p) p^(-s)/(1-p^(-s)),
H_p(s)=Phi_p(s)-Phi_p(1-s).                               (1)
```

For a centered coordinate `z=x+i y`, let

```text
s(z)=1/2+i z,
E_p(z)=-i Phi_p(s(z)),
T_p^FE(z)=-i H_p(s(z)).                                  (2)
```

Here `E_p` is the literal one-sided finite-place summand of the continued source on the Euler
half-plane.  The block `T_p^FE` is its centered FE-paired Schwarz completion.  Keeping the two
separate prevents the reflection completion from being mistaken for the raw finite Euler
truncation.

Assume `0<y<1/2`.  Both arguments in `(1)` then lie in the half-plane of absolute convergence.
Since

```text
s(conjugate(z))=1-conjugate(s(z)),
Phi_p(conjugate(s))=conjugate(Phi_p(s)),                  (3)
```

the FE-paired source has the exact centered Schwarz law

```text
T_p^FE(conjugate(z))=conjugate(T_p^FE(z)).                (4)
```

Thus its upper one-Cauchy diagonal is real and equals

```text
C_p(x,y)
  =Re((T_p^FE(conjugate(z))-T_p^FE(z))/(z-conjugate(z)))
  =-Im(T_p^FE(z))/y.                                     (5)
```

The literal one-sided contribution to a completed divided difference is

```text
C_hat_p(x,y)
  =Re((E_p(conjugate(z))-E_p(z))/(z-conjugate(z))).       (5a)
```

It need not satisfy a centered Schwarz law by itself; the real part in `(5a)` is essential.

## Exact Poisson radial-difference law

Write

```text
r_+=p^(-1/2+y),
r_-=p^(-1/2-y),
theta=x log(p),
P_r(theta)=(1-r^2)/(1-2r cos(theta)+r^2).                (6)
```

Then `0<r_-<r_+<1`, and direct substitution in `(1)` gives

```text
C_p(x,y)=log(p)/(2y) [P_(r_+)(theta)-P_(r_-)(theta)].     (7)
C_hat_p(x,y)=C_p(x,y)/2
            =log(p)/(4y) [P_(r_+)(theta)-P_(r_-)(theta)]. (7a)
```

Indeed,

```text
Re(r exp(-i theta)/(1-r exp(-i theta)))
  =(r cos(theta)-r^2)/(1-2r cos(theta)+r^2)
  =(P_r(theta)-1)/2.                                     (8)
```

For the raw summand, `s(conjugate(z))=1-conjugate(s(z))` gives

```text
C_hat_p(x,y)
  =[Re Phi_p(s(z))-Re Phi_p(1-conjugate(s(z)))]/(2y).    (8a)
```

The two real parts in `(8a)` have the same angular phase and radii `r_+` and `r_-`, respectively,
which proves `(7a)`.  The centered FE completion contributes the reflected copy as well, explaining
the exact factor two without changing the chamber.

Equation `(7)` identifies the finite Euler Cauchy orientation with the radial difference of the
same disk Poisson kernel that occurs as the positive group delay of one Blaschke all-pass section.
The individual group delays are positive, but their radial difference is orientation-sensitive.
The companion value law `finite-euler-imaginary-gamma-reflection-weld.md` identifies the same
quantity as the centered divided-difference shadow of a reciprocal Gamma-reflection quartet.

## Exact phase threshold

For `0<b<a<1`, elementary subtraction yields

```text
(a cos(theta)-a^2)/(1-2a cos(theta)+a^2)
 -(b cos(theta)-b^2)/(1-2b cos(theta)+b^2)

 =(a-b)[(1+ab)cos(theta)-(a+b)]
   /[(1-2a cos(theta)+a^2)(1-2b cos(theta)+b^2)].         (9)
```

All factors outside the square bracket are positive.  Therefore, with

```text
kappa_p(y)=(r_++r_-)/(1+r_+r_-)
          =(p^(-1/2+y)+p^(-1/2-y))/(1+p^(-1)),           (10)
```

one has `0<kappa_p(y)<1` and the complete chamber law

```text
C_p(x,y)>0  iff cos(x log(p))>kappa_p(y),
C_p(x,y)=0  iff cos(x log(p))=kappa_p(y),
C_p(x,y)<0  iff cos(x log(p))<kappa_p(y).                 (11)
```

In particular,

```text
C_p(0,y)>0,
C_p(pi/log(p),y)<0.                                      (12)
```

This is stronger than sign examples: `(11)` describes the entire positive seam, its boundary, and
the negative chamber.

## Simultaneous finite-packet sign theorem

Let `S` be a finite nonempty set of distinct primes and define

```text
T_S^FE=sum_(p in S) T_p^FE,
E_S=sum_(p in S) E_p,
C_S=sum_(p in S) C_p,
C_hat_S=sum_(p in S) C_hat_p.                            (13)
```

Then for every fixed `0<y<1/2` there exist real `x_+` and `x_-` such that

```text
C_S(x_+,y)>0,
C_S(x_-,y)<0,
C_hat_S(x_+,y)>0,
C_hat_S(x_-,y)<0.                                        (14)
```

### Proof

Take `x_+=0`; every summand is strictly positive by `(11)`.  Unique factorization makes the prime
logarithms rationally independent.  Hence the Kronecker orbit

```text
x |-> (x log(p) mod 2pi)_(p in S)                        (15)
```

is dense in the finite torus.  The product of the strict negative chambers in `(11)` is an open
neighborhood of `(pi)_(p in S)`.  Choose `x_-` whose orbit lies in that neighborhood.  Then every
summand in `(13)` is strictly negative, proving `(14)`. `QED`

The arithmetic input of this proof is already formalized as
`primeLogFrequency_ne_zero` in `HTGeometry/KroneckerFlow.lean`.  The current Lean corpus also
contains the character-average engine in `RHTower/WeylEquidistribution.lean`, but not the required
open-set hitting theorem for the finite prime torus.  No Lean theorem is claimed here.

## Positive completion obligation

Let `T` be the completed centered source, and subtract the literal one-sided finite Euler packet:

```text
R_S=T-E_S.                                                (16)
```

The one-Cauchy diagonal is additive:

```text
C_T(x,y)=C_hat_S(x,y)+C_(R_S)(x,y).                      (17)
```

Consequently any proof of the completed Xi source sign must establish the exact compensation law

```text
C_(R_S)(x,y)>=-C_hat_S(x,y).                             (18)
```

at every regular upper-half-strip point.  This is now a literal source decomposition, not a
symmetrized bookkeeping device.  On the simultaneous negative chamber constructed above, the
right side of `(18)` is strictly positive.  The complement is therefore not a cosmetic Gamma
normalization: it must provide a phase-locked positive correction against an explicitly negative
finite-prime radial current.

This is the positive content of the theorem.  The finite semilocal connection is a faithful source
coordinate with exact Poisson chamber geometry.  A successful completion must couple that
orientation coordinate to the cofinal prime--Gamma remainder strongly enough to satisfy `(18)`;
positivity of the individual Poisson/group-delay factors, or positivity of only their metric
shadow, cannot do so.

## Top-down chain

```text
[OPEN] phase-locked prime--Gamma compensation (18)
  -> completed one-Cauchy diagonal nonnegative
  -> continued prime--Gamma upper anti-Herglotz sign
  -> Xi Weil one-Cauchy gate
  -> RH.                                                   (19)
```

The new theorem does not discharge `(18)`.  It removes an ambiguity about the finite-place side:
the missing theorem is not positivity of the finite Euler connection, but compensation of its
explicit Poisson radial negative chamber by the completed remainder.

## Existing formal interfaces

- `HTGeometry/FiniteBlaschkeGroupDelay.lean` identifies a disk Poisson kernel with one all-pass
  logarithmic phase derivative and proves its strict positivity.
- `HTGeometry/PoissonFatou.lean` supplies the real angular Poisson kernel and denominator
  positivity.
- `HTGeometry/KroneckerFlow.lean` proves nonresonance of every nontrivial finite prime character.
- `RHTower/WeylEquidistribution.lean` proves vanishing time averages for nonzero finite
  characters and finite trigonometric polynomials.
- `RHTower/XiWeilOneCauchyGate.lean` turns the completed diagonal sign into RH.
- `RHTower/DigammaBounds.lean` supplies the reflection identity that converts the local Euler
  connection into its imaginary-slope Gamma form.

## Literature

- A. Connes, C. Consani, H. Moscovici,
  [*Zeta zeros and prolate wave operators: semilocal adelic operators*](https://arxiv.org/abs/2310.18423),
  for the semilocal multiplier whose logarithmic-position connection is `(1)`.
- The finite-torus step is the classical Kronecker approximation theorem; its arithmetic
  nonresonance here is just unique factorization of distinct primes.

## Gates

- [x] centered FE reflection law
- [x] one-prime Cauchy diagonal value
- [x] Poisson radial-difference identity
- [x] exact phase threshold
- [x] simultaneous positive and negative chambers for every finite nonempty packet
- [x] exact completed-remainder compensation identity
- [ ] formalize finite-torus open-set hitting from the existing character nonresonance
- [ ] formalize the Poisson chamber theorem
- [ ] prove the completed phase-locked compensation law
- [ ] conclude RH
