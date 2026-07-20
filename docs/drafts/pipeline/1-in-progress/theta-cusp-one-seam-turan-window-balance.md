# Theta-cusp one-seam Turan window balance

- **ID:** `theta-cusp-one-seam-turan-window-balance`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[OPEN CORE] [SOURCE-PURE CONSTRAINT]`
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **2026-07-20 target correction:** `[SUPERSEDED AS THE NATIVE GATE]`.  The two displayed window
  estimates remain valid sufficient conditions, but
  `theta-cusp-gaussian-aperture-composite-balance.md` proves that the consumer needs only one
  forced composite of `K_1` and `K_2`.  Do not attack `(8)` and `(9)` separately before testing
  that weaker exact balance.
- **Parent:**
  `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`
- **Value-chart input:**
  `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-continuous-half-density-residual-tail-chart.md`
- **Statement:** The first two positive crossing windows of the canonical first theta atom have the
  required opposite signed balances against its unique regular-curvature seam.  Equivalently, the
  exact reflected first-atom gates close without a numerical enclosure.

## Goal

Close the only two scalar inequalities still needed for the theta degree-one source Hankel block,
using the explicit first atom alone.  Do not use Xi zeros, real-rootedness, anti-Herglotz positivity,
an RH-equivalent measure, or a generic positivity statement that forgets the source value relations.

The resulting chain is

```text
one-seam window balances
  -> reflected first-atom gates
  -> complete degree-one prime--Gamma source Hankel cone
  -> [degree-at-least-two source cone or leading determinants from size three]
  -> RH.
```

The bracketed tail is independent and remains open.

## Fixed source data `[PROVED]`

Let `f=f_1`, `M_k=integral_0^infinity x^k*f(x) dx`, and `V=-log(f)`.  The parent proves

```text
V'(x)=2*t-9/2-6/(2*t-3),
t=pi*exp(2*x),
V''(x)>=19.
```

With

```text
s_0=(log f)'(0)>0,
E_reg(x)=d/dx ((V'(x)-V'(0))/x),
```

there is a unique `c>0` such that

```text
E_reg<0 on (0,c),
E_reg>0 on (c,infinity).                               (1)
```

For `m>=1`, put `p=2*m` and

```text
K_m(t)=integral_(0<u<t<v)
         u^p*v^p*(v^2-u^2)*f(u)*f(v) du dv.            (2)
```

Then `K_m>0`,

```text
K_m'(t)=t^(2*m)*f(t)*(M_(2*m+2)-t^2*M_(2*m)),          (3)
```

and `K_m` has the unique peak

```text
tau_m=sqrt(M_(2*m+2)/M_(2*m)),
tau_1<=tau_2.                                           (4)
```

The regular parts of the first two Turan defects are

```text
G_m=1/(2*m+1)*integral E_reg(t)*K_m(t) dt.             (5)
```

The reflected value pair independently gives

```text
sum_(j>=0) M_(2*j+1)/(4^j*(2*j+1)!)=exp(-pi),          (6)
2*sum_(j>=0) M_(2*j)/(4^j*(2*j)!)=(4*pi-1)*exp(-pi).  (7)
```

The value-chart successor strengthens `(6)`--`(7)` at every cutoff `a>=0`.  For
`R_k(a)=integral_a^infinity (x-a)^k*f(x) dx` and `q(a)=pi*exp(2*a)`, it proves

```text
2*sum_(j>=0) R_(2*j)(a)/(4^j*(2*j)!)
  =exp(a/2)*(4*q(a)-1)*exp(-q(a)),
sum_(j>=0) R_(2*j+1)(a)/(4^j*(2*j+1)!)
  =exp(a/2)*exp(-q(a)).                                (7a)
```

It also proves

```text
0<c<log 2,
tau_1<=tau_2<2/3<log 2,                                (7b)
```

and the exact window collapse

```text
K_m(c)=M_(2*m)*U_(2*m+2)(c)-M_(2*m+2)*U_(2*m)(c),     (7c)
```

where every `U_k(c)` is a finite binomial combination of the residual moments in `(7a)`.

## Exact target

Write

```text
a_j=2*M_(2*j),
H=1/2-(4*pi-1)*exp(-pi),
W=a_0+a_1/8,
delta=(W+H)/W,
P_m=s_0/(2*m+1)
    *(M_(2*m-1)*M_(2*m+2)-M_(2*m)*M_(2*m+1)).
```

It is necessary and sufficient for this card to prove

```text
G_1 >= (1/45+16*H/(45*a_0))*M_0*M_4-P_1,              (8)
G_2 <= (1-14*delta/15)*M_4^2-P_2.                      (9)
```

Equivalently, define the positive/negative seam masses

```text
B_m^- = integral_0^c (-E_reg(t))*K_m(t) dt,
B_m^+ = integral_c^infinity E_reg(t)*K_m(t) dt.        (10)
```

Then `(8)`--`(9)` are the two explicit inequalities

```text
B_1^+-B_1^- >= 3*((1/45+16*H/(45*a_0))*M_0*M_4-P_1), (11)
B_2^+-B_2^- <= 5*((1-14*delta/15)*M_4^2-P_2).         (12)
```

This is the native orientation statement: the same signed seam is tested by two ordered windows,
and the required orientations are opposite.

## Candidate moves

### A. Target-weighted window comparison

`[CONJECTURE]` Find explicit positive constants `lambda_-`, `lambda_+` such that suitable affine
combinations of `K_1` and `K_2` change sign only at `c`, with the constants calibrated by the right
sides of `(11)`--`(12)`.  The pointwise sign can then be multiplied by `(1)` and integrated.

`[ATTACK]` Monotonicity of `K_2/K_1` alone would generally compare `G_2` from below by `G_1`, while
the live target asks for a lower bound on `G_1` and an upper bound on `G_2`.  A usable comparison
must include the exact normalizations and boundary determinants; an unnormalized one-crossing
claim is insufficient.

### B. Peak/seam integration by parts

Since `K_m(0)=K_m(infinity)=0`, equations `(3)` and `(5)` give the exact alternative

```text
(2*m+1)*G_m
 =-integral (R_reg(t)-R_reg(c))*K_m'(t) dt,             (13)
```

where `R_reg=(V'-V'(0))/x` has its unique minimum at `c`.  Thus every factor in `(13)` has a known
sign: the integrand is nonpositive before `tau_m` and nonnegative after it.  The relative location
of `c` and `tau_m` controls how the decreasing and increasing branches of `R_reg` populate those
two signed pieces.

`[CONJECTURE]` Determine only the remaining internal order of `c,tau_1,tau_2`, then dominate the
resulting subintervals by the continuous residual budgets `(7a)`.  All three points are already
proved to lie in `(0,log 2)`, while every nontrivial arithmetic translate lies on the
positive-curvature side.  This uses the seam and the value relation simultaneously; a global
curvature norm would discard both.

### C. Antisymmetric tilted law

Let `nu` have density proportional to `cosh(x/2)f(x)`.  Equations `(6)`--`(7)` are equivalent to

```text
E_nu[tanh(X/2)]=1/(4*pi-1).                            (14)
```

`[CONJECTURE]` Apply a one-dimensional localization theorem with the bounded constraint `(14)`
and the exact score `(V')` to extremize the two window balances, not the raw moments separately.
The extremizer must retain the boundary score; replacing the source by an arbitrary log-concave
law is too coarse.

### D. Ward recurrence as a window envelope

The formal Gibbs equipartition supplies an all-order two-step decay relation, while `(6)`--`(7)`
fix the two parity-generating values.  `[CONJECTURE]` Use those relations to build explicit upper
and lower envelopes for the incomplete moments in `(2)`, preserving the determinant difference
instead of bounding its two products separately.

## Retired shortcuts

- `V''>=19` alone gives concentration but not the opposite margins `(8)`--`(9)`.
- Positivity of every `D_m` gives only ordinary Turan inequalities; it supplies no upper bound for
  `D_2`.
- The Csordas--Dimitrov secondary-concavity criterion gives double Turan inequalities, but their
  analogous Riemann-kernel condition is itself stated as a conjecture and does not contain the
  constants in `(8)`--`(9)`.
- Separate pointwise bounds for the two products defining `K_m` destroy the crossing cancellation.
- A numerical incomplete-Gamma box may certify the values but is outside the active method and does
  not explain the common source constraint.

## Gates

- [x] exact half-density even and odd budgets
- [x] exact higher-tail elimination
- [x] half-line slope-curvature identity and boundary determinant
- [x] source curvature floor and unique regular-curvature seam
- [x] positive unimodal crossing-window representation and ordered peaks
- [x] continuous residual half-density chart, ordinary survival corridor, and `c<log 2`
- [ ] prove the order-one lower window balance `(8)`
- [ ] prove the order-two upper window balance `(9)`
- [ ] transfer the two balances through the existing likelihood theorem
- [ ] close the independent degree-at-least-two or leading-determinant tail

## Literature boundary

- G. Csordas and R. S. Varga, *Moment inequalities and the Riemann hypothesis*,
  https://www.math.kent.edu/~varga/pub/paper_161.pdf
- G. Csordas and D. K. Dimitrov, *Conjectures and theorems in the theory of entire functions*,
  https://www.dcce.ibilce.unesp.br/~dimitrov/papers/varga.pdf

The first source supplies the classical Turan/slope-curvature parent theory.  The second proves a
secondary-concavity implication and explicitly leaves its Riemann-kernel version open.  Neither
states the one-atom reflected seam balances `(8)`--`(9)`.
