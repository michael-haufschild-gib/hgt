# The even CCM aperture form is an exact polar--Euler frame operator minus one scalar level

- **ID:** `ccm-polar-euler-frame-minus-level-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE REFERENCE SPLITTING / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the digamma partial-fraction expansion, Plancherel, translation-difference
  squares, and `ccm-polar-prime-critical-mellin-defect-law.md`
- **Statement:** At every aperture, the exact restricted Weil form is a countable positive Gamma
  resolvent frame plus the complete finite prime-difference frame, one positive even polar channel,
  one negative odd polar channel, and a scalar level. In the even sector it is exactly a positive
  frame operator minus that level. Hence RH is reduced to a cofinal lower-frame theorem for the
  source-defined feature map.

## 1. Positive digamma resolvent channels

Put

```text
m(xi)=Re psi(1/4+i xi/2)-log pi,
lambda_k=2k+1/2,       k>=0.                                  (1)
```

The classical partial-fraction expansion of the digamma function gives, for real `xi`,

```text
m(xi)-m(0)
 =sum_(k>=0) 2xi^2/[lambda_k(lambda_k^2+xi^2)].                 (2)
```

Indeed, with `b=xi/2` and `a=1/4`,

```text
Re psi(a+ib)-psi(a)
 =sum_(k>=0) b^2/[(k+a)((k+a)^2+b^2)],                         (3)
```

and `(2)` is the rescaling `lambda_k=2(k+a)`. Every summand is nonnegative.

For a zero-extended aperture vector `v`, let `D=-i partial_x` on the full line and define

```text
B_(Gamma,k)v
 =sqrt(2/lambda_k) D(lambda_k^2+D^2)^(-1/2)v.                  (4)
```

Then monotone convergence and Plancherel give

```text
1/(2pi) integral_R [m(xi)-m(0)]|hat(v)(xi)|^2dxi
 =sum_(k>=0)||B_(Gamma,k)v||_2^2.                              (5)
```

The right side is a closed countable positive frame form on the Gamma form domain.

## 2. Complete finite prime-difference frame

At aperture `a`, put

```text
X=exp(2a),
c_n=Lambda(n)n^(-1/2),
h_n=log n,
mu_a=2sum_(n<=X)c_n-m(0).                                     (6)
```

For every real `xi`,

```text
-2c_n cos(h_n xi)=c_n|1-exp(i h_n xi)|^2-2c_n.                (7)
```

Let `tau_h` be translation by `h` of the zero extension and set

```text
B_(p,a)v=(sqrt(c_n)(v-tau_(h_n)v))_(n<=X).                    (8)
```

The target is a finite direct sum and Plancherel gives

```text
||B_(p,a)v||^2
 =1/(2pi)integral_R
   sum_(n<=X)c_n|1-exp(i h_n xi)|^2 |hat(v)(xi)|^2dxi.         (9)
```

Thus every visible prime power occurs as an explicit positive difference channel; rational
determinant or scalar-symbol packaging has not removed any prime-log direction.

## 3. Bilateral polar channel

The exact aperture polar kernel is

```text
2cosh((x-y)/2)
 =2cosh(x/2)cosh(y/2)-2sinh(x/2)sinh(y/2).                    (10)
```

Define the scalar features

```text
b_+(v)=sqrt(2) inner(cosh(. /2),v),
b_-(v)=sqrt(2) inner(sinh(. /2),v).                            (11)
```

Then its quadratic form is

```text
|b_+(v)|^2-|b_-(v)|^2.                                       (12)
```

The positive feature survives only in the even sector, while the negative feature survives only
in the odd sector.

## 4. Exact frame-minus-level identity

Let

```text
B_a v=((B_(Gamma,k)v)_(k>=0), B_(p,a)v, b_+(v)).              (13)
```

Combining `(2)`, `(7)`, `(12)`, and the corrected finite-aperture symbol gives

```text
QW_a(v,v)
 =||B_a v||^2-mu_a||v||_2^2-|b_-(v)|^2.                      (14)
```

In particular, for every even form-domain vector,

```text
QW_a(v,v)=||B_a v||^2-mu_a||v||_2^2.                          (15)
```

For every odd vector,

```text
QW_a(v,v)
 =sum_k||B_(Gamma,k)v||^2+||B_(p,a)v||^2
  -mu_a||v||_2^2-|b_-(v)|^2.                                 (16)
```

These are exact identities, not asymptotic comparisons.

## 5. Positive lower-frame formulation of the CCM core

There are no real nontrivial zeta zeros in `0<s<1`: the alternating Dirichlet eta series is
positive there and `zeta(s)=eta(s)/(1-2^(1-s))<0`. Yoshida's even Weil criterion therefore reduces
RH to positivity of the even restricted forms for every aperture. By `(15)`, the exact positive
target is

```text
||B_a v||^2>=mu_a||v||_2^2
for every even v in the aperture form domain and every a>0.    (17)
```

Equivalently, the positive operator `B_a^*B_a` must have lower frame bound at least `mu_a`.
The construction supplies the complete carrier demanded by the corpus:

```text
countable Gamma resolvent channels
  + every visible prime-translation difference
  + distinguished even polar boundary moment
  + matching scalar level mu_a
  + Paley--Wiener aperture compression.                        (18)
```

The remaining theorem is not positivity of any one channel. It is the joint lower-frame estimate
`(17)` at the exact cofinal scalar level. Proving `(17)` proves RH; no such estimate is claimed
here.

## Relation to the direct route

This theorem constructs the positive reference splitting requested in equation (10) of
`ccm-direct-cofinal-weil-floor.md`, but it also fixes its correct orientation. The prime module
appears in the positive difference frame, while its total mass contributes to the scalar level.
The polar factor is not a scalar remainder: it is the rank-one even boundary feature in `(13)` and
the opposite odd feature in `(16)`.

Because `(2)` is the standard digamma partial fraction and `(7)` is the elementary difference-square
identity, this is classified as a bridge. Its value is the exact source-compatible assembly, not a
new parent mechanism.

## Lean decision

The tree already contains the digamma/trigamma partial-sum infrastructure in
`RHTower/ReflectionCocycleArchimedean.lean` and extensive Hilbert-space square identities. A Lean
formalization of `(2)`--`(16)` would certify this bridge but would not prove the lower-frame bound
`(17)`. No wrapper-only Lean file is added before the analytic core advances.

## Gates

- [x] digamma increment written as positive resolvent squares
- [x] every visible prime term written as a positive translation-difference square
- [x] polar block diagonalized into even-positive and odd-negative channels
- [x] exact full frame-minus-level identity proved
- [x] even RH core restated as the sharp lower-frame inequality
- [ ] prove the lower-frame inequality `(17)`
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "No wrapper-only Lean file is added" decision recorded above.  The
lower-frame bound `(17)` is indeed the open analytic core and stays open; what is now certified is
the card's own exact assembly `(2)`–`(16)`, i.e. that the identity really is *frame minus level*.

Module: `formal/GaloisForLFunctions/RHTower/CCMPolarEulerFrameLevel.lean`
(9 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `re_inv_add_mul_I`, `digamma_term_identity`, `digamma_term_nonneg` — **equations (2)–(3),
  termwise**: `Re(1/(A+ib)) = A/(A²+b²)` and hence
  `1/A − Re(1/(A+ib)) = b²/(A(A²+b²)) ≥ 0`.  Every digamma-increment summand is a nonnegative
  resolvent square, which is what makes `(5)` a positive frame form.
- `normSq_one_sub_exp`, `prime_difference_square` — **equation (7)**: `|1 − e^{iθ}|² = 2 − 2cos θ`,
  hence `−2c cos(hξ) = c|1 − e^{i h ξ}|² − 2c`.  Every visible prime power is an explicit positive
  translation-difference channel plus a contribution to the scalar level `μ_a`.
- `polar_kernel_split` — **equation (10)**: `2cosh((x−y)/2) = 2cosh(x/2)cosh(y/2) −
  2sinh(x/2)sinh(y/2)`, the exact even/odd polar splitting behind `(11)`–`(12)`.
- `frame_minus_level_even` — **equations (14) → (15)**: on an even vector the odd polar feature
  vanishes and the exact identity is frame minus level.
- `frame_minus_level_odd` — **equation (16)**: on an odd vector the even polar feature drops out.
- `lower_frame_iff` — **equation (17)**: positivity of the even form is *exactly* the lower-frame
  inequality `‖B_a v‖² ≥ μ_a‖v‖²`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the digamma partial-fraction series itself and its rescaling to `(2)`;
- Plancherel and the resolvent operators `(4)`, `(8)`, `(13)`;
- the Paley–Wiener aperture compression and the corrected finite-aperture symbol;
- Yoshida's even Weil criterion and the absence of real nontrivial zeta zeros in `0 < s < 1`.
