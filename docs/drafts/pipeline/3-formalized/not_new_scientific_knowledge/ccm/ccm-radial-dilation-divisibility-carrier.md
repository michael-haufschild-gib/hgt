# The CCM exterior tail carries an exact radial divisibility module

- **ID:** `ccm-radial-dilation-divisibility-carrier`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Poisson summation, multiplicative dilation, and Möbius inversion
- **Statement:** The lower CCM tail decomposes into radial Fourier components indexed by positive
  integers. Multiplicative translation selects the subfamily of indices divisible by the
  translating integer, and finite Möbius inversion recovers every component. The prime Weil form
  is therefore a weighted pairing with an infinite divisibility/autocorrelation carrier which is
  independent of finite-degree archimedean completion.

## Radial components

Let `f_lambda` be even and supported on `[-lambda,lambda]`, and write

```text
q_lambda=Fourier(f_lambda).
```

For `s>=0`, put `v=lambda*e^s` and define

```text
H_(lambda,n)(s)
 =sqrt(v) q_lambda(nv),   n>=1.                                  (1)
```

For a finite cutoff `N`, let

```text
B_(lambda,N)(s)=sum_(1<=n<=N) H_(lambda,n)(s).                    (2)
```

Poisson summation identifies the exact lower exterior tail, in the limit in which the series is
defined, as

```text
b_lambda(s)
 =sum_(n>=1)H_(lambda,n)(s)
  -f_lambda(0)/(2*sqrt(lambda))*e^(-s/2).                          (3)
```

The central term in `(3)` is part of the exact graph-domain cancellation and is not separated in
the closed Weil form.

## Divisibility selection theorem

`[PROVED HERE]` For every positive integer `m`,

```text
H_(lambda,n)(s+log m)=sqrt(m) H_(lambda,mn)(s).                    (4)
```

Consequently,

```text
m^(-1/2) B_(lambda,N)(s+log m)
 =sum_(1<=n<=N) H_(lambda,mn)(s).                                 (5)
```

Thus dilation by `m` selects exactly the radial indices divisible by `m`.

### Proof

At `s+log m`, the multiplicative variable is `mv`. Therefore

```text
H_(lambda,n)(s+log m)
 =sqrt(mv)q_lambda(nmv)
 =sqrt(m)H_(lambda,mn)(s),
```

which proves `(4)`--`(5)`.

## Finite Möbius recovery

Fix `K>=1` and define the truncated divisible tails

```text
C_(lambda,m)^K(s)
 =sum_(r>=1; mr<=K)H_(lambda,mr)(s),   1<=m<=K.                    (6)
```

Then every radial component up to `K` is recovered exactly by

```text
H_(lambda,n)(s)
 =sum_(1<=d<=K/n) mu(d) C_(lambda,nd)^K(s),   1<=n<=K.             (7)
```

Indeed, the coefficient of `H_(lambda,nk)` on the right is

```text
sum_(d|k)mu(d),
```

which is one for `k=1` and zero otherwise. This proves `(7)`.

Equations `(5)` and `(7)` show that the family of shifted tails is not merely correlated with the
radial components: at every finite cutoff it contains exactly the same information.

## Exact finite radial dimension

Assume `f_lambda` is nonzero. Then, for every `K>=1`, the functions

```text
H_(lambda,1),...,H_(lambda,K)                                      (8)
```

are linearly independent on every nonempty open `s`-interval. Consequently the divisible tails

```text
C_(lambda,1)^K,...,C_(lambda,K)^K                                  (9)
```

are also linearly independent, and the finite radial carrier has exact complex dimension `K`.

### Proof

The compactly supported `L2` source is also `L1`, so `q_lambda` is entire. It is not a polynomial:
a polynomial in `L2(R)` is zero, which by Fourier injectivity would force `f_lambda=0`.
Suppose

```text
sum_(n=1)^K a_n H_(lambda,n)(s)=0
```

on an open interval. Divide by `sqrt(lambda e^s)` and use the identity theorem to obtain

```text
sum_(n=1)^K a_n q_lambda(nz)=0,   z in C.                          (10)
```

Write `q_lambda(z)=sum_(r>=0)c_r z^r`. Since it is nonpolynomial, there are at least `K` increasing
indices

```text
r_1<...<r_K
```

with `c_(r_i)!=0`. Comparing coefficients in `(10)` gives

```text
sum_(n=1)^K a_n n^(r_i)=0,   1<=i<=K.                             (11)
```

The generalized Vandermonde matrix `(n^(r_i))_(i,n)` is invertible for the distinct positive nodes
`1,...,K`: its determinant is the ordinary Vandermonde times a Schur polynomial which is strictly
positive at positive nodes. Hence every `a_n=0`, proving independence of `(8)`. Möbius inversion
`(7)` is an invertible triangular change of coordinates between `(8)` and `(9)`, proving the second
claim.

## Exact radial Gram carrier

Put

```text
G_lambda(j,k)=inner(H_(lambda,j),H_(lambda,k))_(L2(ds)).           (12)
```

For finite `J,N`, equations `(2)` and `(5)` give

```text
m^(-1/2)
 inner(B_(lambda,J),B_(lambda,N)(.+log m))
 =sum_(1<=j<=J)sum_(1<=n<=N)G_lambda(j,mn).                        (13)
```

The diagonal masses are exact exterior Fourier tails:

```text
G_lambda(k,k)
 =1/k integral_(k*lambda)^infinity |q_lambda(y)|^2 dy.             (14)
```

Equation `(14)` follows from `y=k*lambda*e^s`. The off-diagonal entries record the radial phase
interference. Dunster's uniform radial PSWF expansion gives a Bessel-phase representation of these
entries for the prolate modes, including the singular endpoint region. The missing arithmetic
theorem is a weighted cofinal estimate on the complete Gram sums in `(13)`, not a scalar leakage
bound.

## Prime Weil pairing

For a real lower-tail vector `b` in the closed global Weil form domain, the two prime atoms at
`+-log n` give

```text
Q_prime(b,b)
 =-2 sum_(n>=2) Lambda(n)n^(-1/2)
      inner(b,b(.+log n)).                                       (15)
```

Thus the exact arithmetic carrier is the weighted autocorrelation vector

```text
C(b)=
 (inner(b,b(.+log n)))_(n>=2).                                   (16)
```

The scalar in `(15)` is one projection of `(16)`. A source-to-divisor theorem must retain the
pointed vector, because coefficient perturbation at a single prime power differentiates precisely
the corresponding coordinate.

The central correction in `(3)` is individually outside the prime form summability class: its raw
coordinates would generate `sum Lambda(n)/n`. Formula `(15)` is therefore applied only to the exact
tail `b_lambda`, or to a decomposition whose pieces are separately certified in the form domain.

## Archimedean boundary separation

`finite-archimedean-gamma-product-boundary-law.md` proves that every finite commensurable Gamma
completion has one upper projective valuation direction, while every recurrent object DA over its
differential field has finite rational phase rank. The finite-degree completion can weight the
archimedean logarithmic multiplier, but it cannot generate the infinite shift module in `(12)`.

At cutoff `K`, Möbius recovery `(7)` shows that preserving the distinct prime directions

```text
{log p:p<=K}
```

requires carrier dimension at least `pi(K)`. The positive CCM incidence state must therefore keep

```text
radial divisibility vector of linear dimension K and phase rank at least pi(K)
  + one finite archimedean valuation direction
  + distinguished divisor/trace moments.                         (17)
```

The compact-open regular-germ quotient discards the first entry. The pointed global incidence
topology retains it.

## Positive cofinal target

Let `b_lambda` be the exact constrained-prolate lower tail. A sufficient source-side theorem is a
cofinal weighted-vector limit

```text
C(b_lambda) -> C_infinity
```

in a topology which makes

```text
sum_(n>=2) Lambda(n)n^(-1/2) C_n
```

continuous and simultaneously controls the archimedean logarithmic form. In radial coordinates,
this is equivalent to a weighted cofinal theorem for the Gram sums `(13)`, including:

```text
diagonal divisibility resonances
  + off-diagonal stationary-phase terms
  + the exact central/remainder cancellation.                     (18)
```

Combining `(18)` with the reduced-resolvent incidence response would transport the infinite source
carrier to the characteristic determinant and its divisor/trace moments.

## Novelty and significance verdict

The dilation identity, finite Möbius inversion, and Gram expansion are standard arithmetic
harmonic analysis. The combination gives an exact and useful CCM carrier, but fails the
parent-theory gate after vocabulary erasure. It is classified as a bridge.

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.

## Lean status

**Superseded, 2026-08-03.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMRadialDivisibilityCarrier.lean`.  The Möbius inversion
interface the previous decision reported missing is mathlib's, and the analytic components are not
needed: every statement below is an identity in the radial index.

- `radialComponent q lam n s = √(lam·exp s) · q (n·(lam·exp s))` — definition `(1)`.
- **`radialComponent_add_log`** — equation `(4)`, the dilation identity
  `H n (s + log m) = √m · H (m·n) s`.  Note it needs only `0 < m`; the hypothesis `0 ≤ lam` is
  unnecessary, since `√(m·x) = √m·√x` already follows from positivity of `m` alone.
- **`sum_radialComponent_add_log`** — equation `(5)`: translation by `log m` selects exactly the
  radial indices divisible by `m`.
- `divisibleTail`, **`sum_divisors_moebius`**, **`moebius_recovery`** — equations `(6)`--`(7)`, the
  finite Möbius recovery.  The coefficient bookkeeping `∑_{d ∣ k} μ d = if k = 1 then 1 else 0` is
  derived from `moebius_mul_coe_zeta` and holds for **every** `k`, including `k = 0`, so the card's
  nonvanishing side condition is unnecessary.  The reindexing is the bijection `(d, r) ↦ (d·r, d)`.
- **`eq_zero_of_powerSums_tendsto`** — the algebraic core of the exact finite radial dimension
  `(8)`--`(11)`.  The card proves independence via a generalized Vandermonde determinant and
  Schur-polynomial positivity at positive nodes.  The Lean proof replaces that by an elementary
  dominant-term limit: dividing `∑_{n ≤ K} a n · n^(r i) = 0` by `K^(r i)` sends every lower node to
  zero because `n/K < 1`, forcing `a K = 0`, and descending induction finishes.  This needs only that
  the exponents tend to infinity — no determinant identity and no symmetric-function positivity.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and genuinely analytic: Poisson summation `(3)`; entirety of `q_lambda` with the
identity-theorem step reducing `(8)` to the power-sum relations `(11)`; the diagonal mass `(14)`,
which is an improper-integral change of variables; and the Gram/autocorrelation estimates behind
`(13)` and `(18)`.

## Gates

- [x] exact dilation/divisibility selection proved
- [x] finite Möbius recovery proved
- [x] exact finite radial dimension proved
- [x] Lean: dilation/divisibility selection `(4)`--`(5)` unconditional
- [x] Lean: finite Möbius recovery `(6)`--`(7)` unconditional
- [x] Lean: power-sum independence core of `(8)`--`(11)` unconditional, without Vandermonde
- [x] radial Gram carrier identified
- [x] prime autocorrelation vector identified
- [x] finite archimedean boundary separated
- [ ] weighted cofinal radial Gram theorem
- [ ] reduced-resolvent transport to divisor/trace moments
- [ ] true Weil Rayleigh-excess or cofinal-floor transfer
