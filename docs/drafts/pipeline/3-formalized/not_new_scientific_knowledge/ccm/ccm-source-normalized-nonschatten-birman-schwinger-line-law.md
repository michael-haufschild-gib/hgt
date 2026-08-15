# The CCM Evans line has a canonical non-Schatten Birman--Schwinger normalization

- **ID:** `ccm-source-normalized-nonschatten-birman-schwinger-line-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the polar--Euler frame-minus-level identity, compact-resolvent form comparison, and
  `ccm-weierstrass-stabilized-square-evans-line-law.md`

## Statement

Work in the even subspace at aperture `a>0`. Let `B_a` be the complete positive source feature map
and

```text
mu_a=2sum_(n<=exp(2a))Lambda(n)n^(-1/2)-m(0)>0.          (1)
```

The exact frame identity is

```text
A_a^+ =B_a^*B_a-mu_a I.                                 (2)
```

Put

```text
H_a=B_a^*B_a=A_a^++mu_a I,
R_a=H_a^(-1).                                            (3)
```

Then `H_a` is strictly positive with compact resolvent, `R_a` is positive and compact, and for
every real or complex spectral parameter `lambda`,

```text
A_a^+-lambda I
 =H_a^(1/2)[I-(mu_a+lambda)R_a]H_a^(1/2).                (4)
```

Consequently the intrinsic Evans line has the canonical source normalization

```text
lambda=-mu_a -> I,                                      (5)
```

and its zero divisor is the noninvertibility divisor of the compact Birman--Schwinger pencil

```text
K_a(lambda)=(mu_a+lambda)R_a.                            (6)
```

The positive RH obligation is exactly

```text
mu_a||R_a||<1 for every a>0.                             (7)
```

The normalization can be chosen by one continuous explicit formula in the aperture. Put

```text
bar_mu_a=8a exp(a)-m(0)+1.                               (7a)
```

Then `bar_mu_a>mu_a`, so

```text
bar_H_a=A_a^++bar_mu_a I>0                              (7b)
```

for every aperture, and equivalently

```text
RH
 iff bar_mu_a||bar_H_a^(-1)||<1 for every a>0.           (7c)
```

Moreover,

```text
R_a notin S_p for every finite p>0.                      (8)
```

Thus no ordinary or finite-order regularized Fredholm determinant of `(6)` exists. A successful
CCM determinant must retain either the finite square boundary Evans reduction, the intrinsic
Fredholm determinant line, or an equivalent non-Schatten renormalized carrier.

## 1. Strict positivity of the source frame

The frame-minus-level theorem gives `(2)`. Already one Gamma channel has Fourier multiplier

```text
sqrt(2/lambda_k) xi/(lambda_k^2+xi^2)^(1/2),             (9)
```

which is nonzero for almost every real `xi`. Hence `B_a v=0` implies that the Fourier transform of
the zero-extended `v` vanishes almost everywhere, so `v=0`. Therefore `H_a=B_a^*B_a` has zero
kernel. Since `A_a^+` has compact resolvent, so does `H_a`; zero is consequently outside its
spectrum and

```text
inf spec H_a>0.                                         (10)
```

This proves that `R_a` is bounded, positive, and compact. Equation `(4)` is algebraic on the form
domain and extends to the associated operators.

## 2. Canonical Evans normalization and exact RH bound

The outer factors `H_a^(1/2)` in `(4)` are invertible. They induce a canonical isomorphism between
the determinant line of `A_a^+-lambda I` and that of `I-K_a(lambda)`. At `lambda=-mu_a`, the latter
operator is the identity, giving `(5)` without a characteristic-root basis or a zeta determinant.

At `lambda=0`, positivity of `A_a^+` is equivalent to

```text
I-mu_a R_a>0
 iff mu_a||R_a||<1.                                     (11)
```

Yoshida's even criterion implies RH because zeta has no nontrivial real zero in the critical
strip. Hence `(7)` is equivalent to RH.

## 3. The inverse frame is compact but never Schatten

The corrected Fourier formula and Suzuki's form comparison give, after scaling to a fixed
interval,

```text
q_(H_a)[v]
 =1/(2pi)integral_R log(1+|xi|)|hat v(xi)|^2 dxi
  +O_a(||v||^2).                                        (12)
```

The reference logarithmic Laplacian on a bounded interval has eigenvalues

```text
log n+O_a(1).                                            (13)
```

The min--max principle and the bounded form difference in `(12)` therefore give

```text
h_n(H_a)=log n+O_a(1).                                   (14)
```

Thus the singular values of `R_a` satisfy

```text
s_n(R_a)=1/(log n+O_a(1)).                               (15)
```

For every finite `p>0`, the series

```text
sum_n s_n(R_a)^p
```

diverges, proving `(8)`. Nevertheless `s_n(R_a)->0`, so `R_a` is compact. `QED`

## 4. A continuous explicit lower chamber

For `n<=exp(2a)`, one has

```text
Lambda(n)<=log n<=2a,
sum_(2<=n<=exp(2a))n^(-1/2)<2exp(a).                    (16)
```

Therefore

```text
mu_a
 =2sum_(n<=exp(2a))Lambda(n)n^(-1/2)-m(0)
 <8a exp(a)-m(0)<bar_mu_a.                              (17)
```

Equations `(2)`--`(3)` give

```text
bar_H_a
 =H_a+(bar_mu_a-mu_a)I>0,                               (18)
```

so `-bar_mu_a` lies strictly below the spectrum at every aperture. The function `bar_mu_a` is
continuous and contains no prime-cutoff jump. Replacing `mu_a,H_a,R_a` in `(4)` by
`bar_mu_a,bar_H_a,bar_H_a^(-1)` gives the canonical identity normalization at
`lambda=-bar_mu_a`. Finally,

```text
A_a^+>0
 iff I-bar_mu_a bar_H_a^(-1)>0
 iff bar_mu_a||bar_H_a^(-1)||<1,                        (19)
```

which proves `(7c)`. This selects a coherent source chamber; it does not prove the strict norm
bound.

## Relation to the square Evans determinant

The Weierstrass-stabilized finite maps and `(6)` are two exact reductions of the same Fredholm
family. The determinant-line functor therefore identifies their sections up to a nowhere-zero
factor:

```text
finite square boundary Evans line
 isomorphic to
source-normalized non-Schatten Birman--Schwinger line.    (20)
```

The first gives a finite zero detector after exact logarithmic boundary reconstruction. The second
gives the canonical normalization and the sharp norm target `(7)`. Neither discards the infinite
prime--Gamma carrier.

The all-finite-order theorem
`not_summable_primeLogHerglotzTransportMassOrder_of_pos` is the prime-coordinate counterpart of
`(8)`: finite logarithmic damping cannot convert the critical boundary state into a finite-order
summable determinant carrier.

## Scope and classification

The factorization `(4)`, min--max comparison, and non-Schatten conclusion are standard operator
theory. This is a route bridge, not new scientific knowledge. The formal tree lacks the analytic
restricted-Weil operator and its logarithmic spectral asymptotics, so no faithful Lean theorem is
added.

## Gates

- [x] complete positive source frame isolated in the even sector
- [x] source frame proved injective and bounded below
- [x] canonical Birman--Schwinger normalization constructed
- [x] continuous explicit lower chamber selected for every aperture
- [x] normalized zero divisor identified with the restricted-Weil spectrum
- [x] RH reduced to the sharp source norm bound `mu_a||R_a||<1`
- [x] inverse frame proved compact but outside every finite Schatten class
- [x] square Evans and Birman--Schwinger determinant lines identified
- [ ] prove `mu_a||R_a||<1` for every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no faithful Lean theorem is added" note above.  The analytic
restricted-Weil operator and its logarithmic spectral asymptotics remain cited parents, but the
card's own operator-algebraic and comparison steps are reachable and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCMNonSchattenBirmanSchwinger.lean`
(5 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `birmanSchwinger_factorization` — **equation (4)**: with `H = A + μ` invertible,
  `A − λ = H(1 − (μ+λ)H^{-1})`, the exact factorization through the Birman–Schwinger pencil.
- `birmanSchwinger_identity_at_normalization` — **equation (5)**: at `λ = −μ` the pencil is the
  identity, which is the canonical source normalization requiring no characteristic-root basis.
- `posDef_one_sub_smul` — **equation (11), sufficient direction**: if `μ‖R‖ < 1` then
  `⟪(I − μR)x, x⟫ > 0` for every `x ≠ 0`.  This is the half of the equivalence that does not need
  spectral-radius theory.
- `inv_sqrt_le_telescope` — the exact telescoping estimate `1/√n ≤ 2(√n − √(n−1))` behind the prime
  sum bound `∑_{2 ≤ n ≤ N} n^{-1/2} < 2√N` of `(16)`, hence behind the explicit chamber
  `μ_a < 8a e^{a} − m(0)` of `(17)`.
- `not_summable_of_eventually_inv_nat_le` — **equation (8), comparison core**: a sequence that
  eventually dominates `1/n` is not summable.  Applied to the singular-value law
  `s_n = 1/(log n + O(1))` of `(15)` — for which `s_n^p ≥ 1/n` eventually, for every finite `p` —
  this is exactly the statement that `R_a` lies outside every Schatten class.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the analytic restricted-Weil operator `A_a^+`, its compact resolvent, and the frame identity `(2)`;
- the form comparison `(12)` and the logarithmic eigenvalue asymptotics `(13)`–`(15)`;
- the min–max principle;
- Yoshida's even criterion and the determinant-line identification `(20)`.
