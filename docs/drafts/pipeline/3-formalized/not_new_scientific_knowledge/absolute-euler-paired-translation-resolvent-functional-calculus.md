# Absolute-Euler paired energy is one completed translation-resolvent form

- **ID:** `absolute-euler-paired-translation-resolvent-functional-calculus`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `absolute-euler-paired-gauss-resolvent-autocorrelation-law.md`
- **Statement:** On the rational damped-sine source core, the complete absolute-Euler paired Xi
  energy is eight times the quadratic form of one explicit half-line translation operator.  The
  Gamma terms are compensated resolvents of the translation semigroup, while every prime-power
  term is a discrete translation and every Euler-prime block is a geometric operator resolvent.

## 1. The real damped-sine core

Let

```text
E(x)=sum_j r_j exp(-w_j x),
y(x)=Im E(x),
```

where the family is finite, `r_j` is real, and `Re(w_j)>1/2`.  Thus `y` is a finite real linear
combination of functions

```text
exp(-a*x) sin(b*x),  a>1/2.                              (1)
```

Write `H=L2(R_+,R)`.  For `t>=0`, let

```text
(S_t y)(x)=y(x+t).                                       (2)
```

Then `(S_t)` is the contractive right-translation semigroup on `H`.  On the core `(1)`, and for
every real `c>-min_j Re(w_j)`, define the tail resolvent

```text
(R_c y)(x)=integral_0^infinity exp(-c*t) y(x+t) dt
           =integral_x^infinity exp(-c*(u-x)) y(u) du.   (3)
```

The slightly growing value `R_(-1/2)` is therefore well defined on this core even though it is
not a bounded resolvent on all of `H`.

## 2. Gauss squares are translation-resolvent values

Put

```text
y_c=R_c y,
Z_c=y_c(0),
B_c=integral_0^infinity y_c(x)^2 dx.
```

Termwise integration in the finite packet gives

```text
y_c(x)=Im sum_j r_j exp(-w_j*x)/(w_j+c).                  (4)
```

Moreover

```text
y_c'(x)=c*y_c(x)-y(x).                                   (5)
```

Since `y_c(x)` tends to zero exponentially, integration of the derivative of `y_c^2` yields the
exact identity

```text
Z_c^2+2*c*B_c=2*<y,R_c y>_H.                             (6)
```

Consequently the atom formula from the parent card is not merely a sum of two positive-looking
quantities.  It is one resolvent quadratic value:

```text
sum_(j,k) r_j*r_k P[w |-> d/(w+c)](w_j,w_k)
  =4*d*Z_c^2+8*d*c*B_c
  =8*d*<y,R_c y>_H.                                     (7)
```

The constant and exponential-lag atoms similarly satisfy

```text
sum_(j,k) r_j*r_k P[d](w_j,w_k)
  =8*d*||y||_H^2,                                       (8)

sum_(j,k) r_j*r_k P[-d*exp(-t*.)](w_j,w_k)
  =-8*d*<y,S_t y>_H.                                    (9)
```

Equations `(6)--(9)` are the functional-calculus lift of the paired scalar transform.

## 3. The completed translation operator

Let

```text
a_n=2*n+1/2.
```

On the core `(1)` define the Gamma quadratic operator by its convergent compensated series

```text
G_Gamma
 =R_(1/2)+R_(-1/2)-(log(pi)+EulerGamma)/2 * I
   +sum_(n>=0) (1/(2*(n+1))*I-R_(a_n)).                  (10)
```

The compensation inside each summand is essential; neither identity part nor resolvent series
is to be separated.  Define the critical Euler translation form by

```text
G_Euler
 =sum_(m>=2) Lambda(m)*m^(-1/2)*S_(log m).               (11)
```

For every vector in `(1)`, `(11)` converges absolutely as a quadratic form: translation by
`log m` supplies an additional factor `m^(-a)` for some `a>1/2`.

Let

```text
L(w)
 =1/(w+1/2)+1/(w-1/2)-1/2*log(pi)
   +1/2*psi(1/4+w/2)
   -sum_(m>=2) Lambda(m)*m^(-1/2)*exp(-w*log m).         (12)
```

Using the Gauss series

```text
1/2*psi(1/4+w/2)
 =-EulerGamma/2
   +sum_(n>=0) (1/(2*(n+1))-1/(w+a_n)),                 (13)
```

and applying `(7)--(9)` term by term gives the exact completed identity

```text
sum_(j,k) r_j*r_k P[L](w_j,w_k)
 =8*<y,(G_Gamma-G_Euler)y>_H.                            (14)
```

Thus the compensated Gauss-resolvent / prime-autocorrelation budget of the parent card is one
operator quadratic form, not two unrelated estimates.

## 4. Prime-by-prime Euler resolvents

For each prime `p`, put

```text
T_p=p^(-1/2)*S_(log p).                                  (15)
```

Since `||T_p||<=p^(-1/2)<1`, the prime-power block in `(11)` is the ordinary geometric operator
resolvent

```text
sum_(k>=1) log(p)*p^(-k/2)*S_(k*log p)
 =log(p)*T_p*(I-T_p)^(-1).                               (16)
```

Equivalently,

```text
T_p*(I-T_p)^(-1)
 =1/2*((I+T_p)*(I-T_p)^(-1)-I).                          (17)
```

The Cayley operator in `(17)` is accretive because `T_p` is a strict contraction.  Therefore
each finite-place block has a canonical positive Cayley part and one scalar contact subtraction.
This does **not** prove `(14)` nonnegative: the Euler blocks occur with the adverse sign, and the
infinite contact compensation has to be matched with the Gamma series before taking a limit.

The positive formulation of the remaining obstruction is:

> prove that the canonical Gamma contact/resolvent completion dominates the positive Cayley
> sectors of the complete Euler-prime family on the damped-sine core.

No cancellation between unnamed scalar expressions remains after `(14)--(17)`.

## 5. Top-down RH chain

The parent completeness theorem proves that rational damped-sine packets already span the
Xi--Hurwitz orientation sector.  Hence the exact live chain is

```text
<y,(G_Gamma-G_Euler)y> >= 0
  for every rational damped-sine packet y
  -> absolute-Euler paired Cauchy passivity
  -> positivity on the canonical orientation vector
  -> RH.                                                   (18)
```

The first line is the only open assertion in `(18)`.  It uses only the absolutely convergent
prime--Gamma formula and a fixed source core.  It assumes no Xi zero locations, continued-strip
sign, real-rootedness, limiting zero measure, or theta-tail current estimate.

## 6. Literature calibration

Burnol identifies each local term of the explicit formula with the spectral multiplier of the
local conductor operator and treats finite and archimedean places in one framework.  In
particular, the logarithmic derivative of the local Gamma factor is the multiplier of the
archimedean conductor operator.  This supports the interpretation of `(10)` as a half-line
resolvent realization of the archimedean local term:

- J.-F. Burnol, *The Explicit Formula and the conductor operator*,
  [arXiv:math/9902080](https://arxiv.org/abs/math/9902080).
- J.-F. Burnol, *Spectral Analysis of the local Conductor Operator*,
  [arXiv:math/9811040](https://arxiv.org/abs/math/9811040).

Burnol's positivity at a finite place is on the ramified/cuspidal sector.  The zeta Euler factors
in `(16)` lie in the unramified spherical channel, where the adverse Cayley contribution remains.
Thus the local conductor theorem does not discharge `(18)`.

Connes--Consani prove the archimedean Sonin compression positivity and explicitly present its
semilocal extension as the route where Weil positivity would imply RH.  Their result supplies a
possible operator-compression provider for `G_Gamma`, but not the all-prime domination in `(18)`:

- A. Connes and C. Consani, *Weil positivity and Trace formula, the archimedean place*,
  [arXiv:2006.13771](https://arxiv.org/abs/2006.13771).

The functional-calculus identities `(6)--(17)` are elementary semigroup/resolvent algebra.  They
are recorded as a project bridge, not as new scientific knowledge.

## Lean formalization

Status: **complete and unconditional** for every proved equation of this card.

Module `formal/GaloisForLFunctions/RHTower/PairedTranslationResolventCalculus.lean`:

- `packetProfile`, `resolventProfile`, `packetResolventPairing` — the core `y = Im E`, the tail
  resolvent `y_c = R_c y`, and the half-line pairing `⟨y, R_c y⟩`.
- `integral_exp_neg_atom`, `integral_exp_neg_mul_packetProfile` — **equation `(4)`**: on the core
  the tail resolvent is again a packet, with coefficients `rⱼ/(wⱼ + c)`.  Valid for every real `c`
  with `Re wⱼ + c > 0`, so the slightly growing value `c = -1/2` is included.
- `hasDerivAt_resolventProfile` — **equation `(5)`**: `y_c' = c y_c - y`.
- `bilSum_resolvent_law`, `hermSum_resolvent_law`, `resolvent_contact_law` — **equation `(6)`**:
  `Z_c² + 2 c B_c = 2 ⟨y, R_c y⟩`.  The proof is exact Cauchy-kernel algebra, not an integration
  by parts, so no decay estimate enters.
- `paired_resolvent_law` — **equation `(7)`**: a real Cauchy atom `d/(w+c)` has paired quadratic
  `8 d ⟨y, R_c y⟩`.
- **Equation `(8)`** is `RHTower.paired_const_law` and **equation `(9)`** is
  `RHTower.paired_lag_law` of `RHTower/PairedCauchyLaplaceIdentities.lean`;
  `packetAutocorrelation_eq_translation_pairing` records the lag autocorrelation as the
  translation pairing `⟨y, S_τ y⟩`.
- `tsum_pow_succ_eq_mul_inverse`, `one_sub_mul_inverse`, `one_add_mul_inverse_eq` — **equations
  `(16)`--`(17)`**: for a strict contraction `T`, `∑_{k≥1} T^k = T (1-T)^{-1}` and
  `(1+T)(1-T)^{-1} = 1 + 2 T (1-T)^{-1}`.
- `re_inner_cayley_eq`, `re_inner_cayley_nonneg` — the Cayley form of a contraction is accretive,
  with real part exactly the norm defect `‖v‖² - ‖Tv‖²`.
- `norm_real_smul_lt_one`, `norm_eulerPrimeBlock_lt_one` — `T_p = p^{-1/2} S_{log p}` is a strict
  contraction for every `p > 1` and every contraction `S`.

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

The compensated series `(10)`--`(14)` and the domination gate `(18)` are the card's open research;
they are not formalization debt.  The identities they are assembled from -- `(4)`--`(9)` and
`(16)`--`(17)` -- are all closed above.

## Gates

- [x] Gauss square identified with one translation-resolvent value
- [x] constant and prime-lag atoms lifted to half-line operators
- [x] complete paired source written as one compensated operator form
- [x] every prime-power block factored as a geometric Euler resolvent
- [x] local Cayley accretivity and its adverse global sign separated
- [x] literature interface with local conductor and archimedean Sonin operators calibrated
- [ ] prove the Gamma/Euler domination on the rational damped-sine core
- [ ] formalize after paper-level domination is available
- [ ] prove RH
