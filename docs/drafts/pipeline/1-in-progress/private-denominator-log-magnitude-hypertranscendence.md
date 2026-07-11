# Private-Denominator Log-Magnitudes Force Hypertranscendence

- **ID:** `private-denominator-log-magnitude-hypertranscendence`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / GENERAL HT ARITHMETIC-VALUATION LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** An entire full-support series with algebraic unit phases is HT whenever its
  positive rational negative-log magnitudes have asymptotically large private denominator primes.
  Such profiles can approximate any prescribed superlinear log-magnitude sequence arbitrarily
  closely.

## Goal

Replace Archimedean separation by exact arithmetic separation. When polynomial log-magnitudes have
exponent below two, the competitive ADE phase window grows mesoscopically and finite-language
Fourier testing loses dimensional control. A private denominator prime instead marks each Taylor
index inside every finite convolution atom. Lindemann--Weierstrass separates distinct marked
valuation sums, while the private prime proves that the balanced surviving atom has no equal-value
competitor.

## Private-prime exposure

A positive rational sequence `b=(b_n)` has **eventual private-prime exposure** if there are distinct
primes `p_n` tending to infinity such that

```text
v_(p_n)(b_n)<0,
v_(p_n)(b_m)>=0  for every m!=n.                            (PP)
```

Thus `p_n` occurs in the reduced denominator of `b_n` and in no other reduced denominator.

## Theorem `[PROVED HERE]`

Let `(b_n)` be positive rational numbers satisfying

```text
b_n/n -> infinity                                           (1)
```

and `(PP)`. Let `u_n` be arbitrary algebraic complex numbers of modulus one. Then

```text
f(z)=sum_(n>=0) u_n exp(-b_n) z^n                           (2)
```

is entire and hypertranscendental over `C(z)`.

## Proof

Condition (1) gives

```text
|u_n exp(-b_n)|^(1/n)=exp(-b_n/n)->0,
```

so (2) is entire.

Suppose that `f` is DA. Mahler's integer-normalization theorem supplies a nonzero equation

```text
P(z,f,f',...,f^(r))=0,
P in Z[z,Y_0,...,Y_r].                                      (3)
```

Let `D>=1` be the maximal total degree of `P` in the dependent variables. Generic coefficient
extraction and grouping at coefficient index `N` give an exact finite identity

```text
sum_(nu in A_N) c_(N,nu) product_n a_n^(nu_n)=0,             (4)
a_n=u_n exp(-b_n),
```

where:

- every `nu` is a finitely supported multiplicity vector with `sum_n nu_n<=D`;
- distinct `nu` are distinct grouped coefficient monomials; and
- every `c_(N,nu)` is a nonzero integer.

Balanced survival for the top polarization of (3) supplies, for every sufficiently large `N`, a
grouped atom `nu_* in A_N` of total degree `D`, all of whose source indices are

```text
N/D+O_P(1).                                                  (5)
```

In particular, after increasing `N`, every index in the support of `nu_*` lies beyond a tail on
which `p_n>D`.

For an atom `nu`, define its rational valuation

```text
V(nu)=sum_n nu_n b_n in Q.                                  (6)
```

We claim that `nu_*` is the only atom in (4) with valuation `V(nu_*)`. Suppose
`V(mu)=V(nu_*)` and put `d_n=mu_n-nu_*(n)`. Then

```text
sum_n d_n b_n=0,   |d_n|<=D.                                (7)
```

Take any sufficiently large index `n` occurring in the support of either multiplicity vector.
Every term `d_m b_m` with `m!=n` is `p_n`-adically integral by `(PP)`. If `d_n!=0`, then
`|d_n|<=D<p_n`, so `v_(p_n)(d_n)=0`; hence

```text
v_(p_n)(d_n b_n)=v_(p_n)(b_n)<0,
```

contradicting (7), whose remaining side is `p_n`-integral. Therefore `d_n=0` at every tail index.

The atom `nu_*` already has total degree `D` entirely on that tail. Equality of all tail
multiplicities leaves `mu` with the same `D` tail entries. Since every atom has total degree at most
`D`, `mu` has no additional prefix entry and equals `nu_*`. This proves uniqueness.

Substitute the coefficient form into (4) and group atoms by the finitely many distinct rational
numbers `V(nu)`:

```text
sum_V C_V exp(-V)=0,                                        (8)
```

where each

```text
C_V=sum_(nu:V(nu)=V)c_(N,nu) product_n u_n^(nu_n)
```

is algebraic. The Lindemann--Weierstrass theorem says that exponentials of distinct algebraic
numbers are linearly independent over the algebraic numbers. Hence every `C_V` in (8) is zero.

For `V=V(nu_*)`, uniqueness gives

```text
C_V=c_(N,nu_*) product_n u_n^(nu_*(n)) !=0,                 (9)
```

because the integer weight and every phase are nonzero. This contradiction proves that no equation
(3) exists. Thus `f` is HT. `square`

## Arbitrary-profile realization theorem `[PROVED HERE]`

Let `(g_n)` be any positive real sequence with `g_n/n->infinity`, and let `epsilon_n>0` be arbitrary.
There is a positive rational private-prime sequence `(b_n)` satisfying

```text
|b_n-g_n|<epsilon_n.                                        (10)
```

### Construction

Choose distinct primes `p_n` so large that

```text
p_n>n,
3/(2p_n)<epsilon_n.
```

Let `q_n` be a nearest integer to `p_n g_n`. If `p_n` divides `q_n`, replace `q_n` by one of its
neighbors. For all sufficiently large `n`, choose the positive neighbor if needed. Then

```text
b_n=q_n/p_n>0,
|b_n-g_n|<=3/(2p_n)<epsilon_n,
gcd(q_n,p_n)=1.                                             (11)
```

Because the primes are distinct, `p_n` is private to the reduced denominator of `b_n`. Equation
(10) and `g_n/n->infinity` imply (1), after making the finitely many initial choices positive.
This proves the realization theorem. `square`

## Polynomial-profile corollary `[PROVED HERE]`

Fix `B>0` and any real `beta>1`. Taking

```text
g_n=B n^beta,
epsilon_n=exp(-n)                                           (12)
```

produces positive rational `b_n` with

```text
b_n=B n^beta+O(exp(-n)).                                    (13)
```

For every algebraic unit-modulus phase sequence, the resulting entire series is HT. The
perturbation in (13) preserves the leading value, first difference, and second difference
asymptotics of the polynomial profile. In particular this gives a deterministic all-positive
coefficient HT realization by taking `u_n=1`, throughout the previously untreated range
`1<beta<2`.

## Boundary attacks

1. **The phases must be algebraic.** Lindemann--Weierstrass gives linear independence over
   algebraic coefficients. Arbitrary complex phases can encode an exact cancellation and are not
   covered.
2. **Private primes are stronger than distinct denominators.** The proof uses `p_n`-adic
   integrality of every other `b_m`; shared denominator primes would permit bounded relations.
3. **The primes need only outrun each fixed ADE degree.** The condition `p_n->infinity` allows the
   tail to be chosen after the hypothetical finite degree `D` is exposed.
4. **No convexity is used.** Balanced survival is an algebraic property of the generic ADE
   coefficient polynomial. Private-prime exposure, not magnitude minimization, makes its surviving
   atom valuation-unique.
5. **The perturbation can be asymptotically invisible but is not zero.** This theorem does not settle
   the exact smooth profile `b_n=B n^beta` below `beta=2`.
6. **This is not genericity.** Every algebraic phase realization of one private-prime magnitude
   profile is HT, including the completely positive phase choice.

## Parent and novelty status

- Mahler normalization is the arithmetic entry point converting arbitrary complex ADE constants to
  an integer coefficient identity.
- Lindemann--Weierstrass supplies the exponential linear independence. The candidate new mechanism
  is its composition with private-prime recovery of an ADE convolution multiset.
- Popken, Sibuya--Sperber, and Krattenthaler--Rivoal constrain arithmetic Taylor coefficients of DA
  series. Here the Taylor coefficients are transcendental exponentials of rational numbers; their
  rational logarithms, rather than the coefficients, carry the arithmetic code.
- Gokhman's algebraic-independence theorem does not apply: the positive phases may all equal one,
  and no algebraic independence of the Taylor coefficients is assumed or proved.
- Exact literature and rediscovery audits remain required. Scientific novelty is not claimed until
  those gates and independent proof review pass.

## Exact RH-route scope

The theorem proves that coefficient positivity and arbitrarily smooth prescribed magnitude
asymptotics coexist with HT, while a finite ADE cannot erase private arithmetic information hidden
below every asymptotic order. It excludes only RH implementations that compress such a private-log
coefficient model into one finite differential constraint. It supplies no zero localization,
spectral operator, Weil sign, Li positivity, or Nyman--Beurling norm estimate, and therefore does
not categorically exclude the complete literature routes.

## Lean status

No Lean formalization is claimed. Full formalization requires Mahler normalization, generic ADE
coefficient extraction and balanced survival, rational `p`-adic valuations, the private-prime
uniqueness lemma, Lindemann--Weierstrass, the rational approximation construction, and the entire
series convergence argument. The theorem cannot move to stage 3 until the complete unconditional
chain is formalized.

## Gates

- [x] 0 -> 1: private-prime invariant, exact theorem, and attack mechanism stated.
- [x] Complete unconditional paper proof and realization construction written.
- [ ] Parent-theory and exact literature novelty audit.
- [ ] Independent proof audit.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved private-denominator valuation exposure HT and arbitrary superlinear-profile
  realization by private rational approximants.
