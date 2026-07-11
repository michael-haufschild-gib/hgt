# Bounded-Relation Log-Magnitudes Force Hypertranscendence

- **ID:** `bounded-relation-log-magnitude-hypertranscendence`
- **Stage:** 2-fully-proven / needs independent scientific audit
- **Type:** THEOREM CANDIDATE / GENERAL HT ARITHMETIC-VALUATION LAW
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, provisional pending independent
  expert verification of the proof and literature claim.
- **Statement:** An entire full-support series with algebraic unit phases is HT whenever every
  bounded-height additive relation among its algebraic negative-log magnitudes is confined to a
  finite prefix. Positive rational magnitudes with asymptotically large private denominator primes
  satisfy this law, and such profiles can approximate any prescribed superlinear log-magnitude
  sequence arbitrarily closely.

## Goal

Replace Archimedean separation by exact relation-lattice separation. When polynomial log-magnitudes have
exponent below two, the competitive ADE phase window grows mesoscopically and finite-language
Fourier testing loses dimensional control. A finite ADE can compare coefficient monomials only
through bounded-multiplicity additive relations among their negative logarithms. If all such
relations are eventually confined, Lindemann--Weierstrass separates the surviving convolution
atoms. Private denominator primes provide an exact arithmetic realization of this general law.

## Bounded-relation confinement

A sequence `b=(b_n)` of algebraic numbers has **bounded-relation confinement at infinity** if, for
every integer `D>=1`, there is an index `M(D)` such that every finitely supported integer sequence
`d=(d_n)` satisfying

```text
|d_n|<=D  for every n,
sum_n d_n b_n=0                                             (RC)
```

is supported in `{0,...,M(D)-1}`. Equivalently, the relation lattice of coefficient height at most
`D` sees only a finite prefix. The bound `M(D)` may grow arbitrarily rapidly with `D`; no uniform
Diophantine estimate is assumed.

## Private-prime exposure

A positive rational sequence `b=(b_n)` has **eventual private-prime exposure** if there are distinct
primes `p_n` tending to infinity such that

```text
v_(p_n)(b_n)<0,
v_(p_n)(b_m)>=0  for every m!=n.                            (PP)
```

Thus `p_n` occurs in the reduced denominator of `b_n` and in no other reduced denominator. The
private-denominator criterion below proves that `(PP)` implies bounded-relation confinement.

## Theorem `[PROVED HERE]`

Let `(b_n)` be positive real algebraic numbers satisfying bounded-relation confinement and

```text
b_n/n -> infinity                                           (1)
```

Let `u_n` be arbitrary algebraic complex numbers of modulus one. Then

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

Suppose that `f` is DA over `C(z)`. The equation witnessing this uses only finitely many complex
constants `c_1,...,c_h`. Each `c_i` is differentially algebraic over `Q(z)`, since `c_i'=0`.
Differential algebraicity is transitive, so `f` is differentially algebraic over `Q(z)`. Clearing
rational-function denominators and then integer denominators supplies a nonzero equation

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

The balanced-survival lemma below supplies arbitrarily large coefficient indices `N` and a grouped
atom `nu_* in A_N` of total degree `D`, all of whose source indices are

```text
N/D+O_P(1).                                                  (5)
```

In particular, after increasing `N`, every index in the support of `nu_*` lies beyond `M(D)`.

### Balanced-survival lemma

Write the part of `P` of dependent-variable degree `D` as a sum of monomials

```text
c_(ell,k_1,...,k_D) z^ell Y_(k_1)...Y_(k_D),
```

where repetitions among the derivative orders `k_i` are allowed. Attach to such a monomial its
**coefficient shift**

```text
q=ell-(k_1+...+k_D).                                       (BS1)
```

Indeed, if the factor `Y_(k_i)` contributes the source coefficient `a_(j_i)`, then it contributes

```text
(j_i)_(k_i) a_(j_i) z^(j_i-k_i),
```

where `(j)_k=j(j-1)...(j-k+1)`. Thus all top-degree monomials with the same shift `q` contribute at
coefficient index

```text
N=j_1+...+j_D+q.                                           (BS2)
```

For each shift `q`, symmetrizing over the `D` source positions gives a symmetric polynomial

```text
W_q(j_1,...,j_D)
```

whose value is exactly the grouped integer weight of the source multiset
`{j_1,...,j_D}` in coefficient (4), up to the fixed positive multiplicity convention used when
some `j_i` coincide.

At least one `W_q` is nonzero. To see this without a genericity assumption, fix `q` and then group
its differential monomials by total derivative weight `K=k_1+...+k_D`; equation (BS1) fixes
`ell=q+K`. The degree-`K` homogeneous part of the corresponding coefficient polynomial is a linear
combination of the monomial symmetric polynomials attached to the multisets
`{k_1,...,k_D}`. Those polynomials are linearly independent. Since the degree-`D` part of `P` is
nonzero, choose a nonzero shift component and its largest occurring `K`; its top homogeneous part
cannot cancel, so the associated `W_q` is nonzero. Equivalently, this is injectivity of the
polarization map

```text
Y_k |-> (x)_k:
```

the vectors `((x)_0,...,(x)_r)` span `C^(r+1)` by the falling-factorial Vandermonde determinant.

Because `W_q` is a nonzero polynomial, there is an integer offset vector
`delta=(delta_1,...,delta_D)` for which

```text
x |-> W_q(x+delta_1,...,x+delta_D)                         (BS3)
```

is not the zero polynomial. Otherwise `W_q` would vanish on every diagonal-parallel line through
an integer point, hence on `Z^D`, a Zariski-dense subset of `C^D`, and would be zero. We may also
avoid the finitely many hyperplanes `delta_i=delta_j` if desired.

For every sufficiently large integer `x` outside the finite zero set of (BS3), put

```text
j_i=x+delta_i,
N=Dx+(delta_1+...+delta_D)+q.                              (BS4)
```

Then the `j_i` are nonnegative, (BS2) holds, their grouped weight is nonzero, and

```text
j_i=N/D+O_P(1).
```

Lower dependent-variable degrees cannot contribute to this degree-`D` coefficient monomial.
Hence it survives in the fully grouped identity (4). This proves balanced survival. `square`

For an atom `nu`, define its algebraic log-magnitude

```text
V(nu)=sum_n nu_n b_n in Qbar.                               (6)
```

We claim that `nu_*` is the only atom in (4) with valuation `V(nu_*)`. Suppose
`V(mu)=V(nu_*)` and put `d_n=mu_n-nu_*(n)`. Then

```text
sum_n d_n b_n=0,   |d_n|<=D.                                (7)
```

Bounded-relation confinement applied to (7) gives `d_n=0` for every `n>=M(D)`. Thus `mu` and
`nu_*` have identical tail multiplicities.

The atom `nu_*` already has total degree `D` entirely on that tail. Equality of all tail
multiplicities leaves `mu` with the same `D` tail entries. Since every atom has total degree at most
`D`, `mu` has no additional prefix entry and equals `nu_*`. This proves uniqueness.

Substitute the coefficient form into (4) and group atoms by the finitely many distinct algebraic
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

## Private-denominator criterion `[PROVED HERE]`

Every positive rational sequence with eventual private-prime exposure has bounded-relation
confinement.

### Proof

Fix `D` and choose `M(D)` so that `p_n>D` for every `n>=M(D)`. Suppose a relation `(RC)` holds. For
any `n>=M(D)`, every term `d_m b_m` with `m!=n` is `p_n`-adically integral by `(PP)`. If `d_n!=0`,
then `0<|d_n|<=D<p_n`, so `v_(p_n)(d_n)=0` and

```text
v_(p_n)(d_n b_n)=v_(p_n)(b_n)<0.
```

This single negative-valuation term cannot cancel a sum of `p_n`-integral terms, contradicting
`(RC)`. Hence `d_n=0` for every `n>=M(D)`, which is bounded-relation confinement. `square`

Combining this criterion with the theorem proves the private-denominator corollary: if `b_n` are
positive rationals satisfying `(1)` and `(PP)`, then (2) is HT for every algebraic unit-modulus
phase sequence.

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
coefficient HT realization by taking `u_n=1`, throughout the range `1<beta<2` not covered by the
preceding convex-separation mechanisms.

## Boundary attacks

1. **The phases must be algebraic.** Lindemann--Weierstrass gives linear independence over
   algebraic coefficients. Arbitrary complex phases can encode an exact cancellation and are not
   covered.
2. **Relation confinement is the exact hypothesis used.** Private primes are only a sufficient
   arithmetic realization. Shared denominator primes are allowed whenever all bounded-height
   relations remain confined to finite prefixes.
3. **No uniform relation bound is needed.** The tail index `M(D)` is chosen only after the
   hypothetical finite ADE degree `D` is exposed.
4. **No convexity is used.** Balanced survival is an algebraic property of the top ADE coefficient
   polynomial. Relation confinement, not magnitude minimization, makes its surviving atom
   log-magnitude-unique.
5. **The perturbation can be asymptotically invisible but is not zero.** This theorem does not settle
   the exact smooth profile `b_n=B n^beta` below `beta=2`.
6. **This is not genericity.** Every algebraic phase realization of one relation-confined magnitude
   profile is HT, including the completely positive phase choice.

## Parent and novelty audit

- **ADE normalization.** The reduction from `C(z)` to `Q(z)` is differential-algebraic
  transitivity: the finitely many complex constants appearing in an ADE satisfy `c'=0`. Mahler's
  1971 paper *On formal power series as integrals of algebraic differential equations* proves a
  different universal fact, namely the factorial-power upper bound
  `|f_n| <= gamma_1 (n!)^gamma_2` for DA formal series. The present rapidly decaying coefficients
  satisfy that bound trivially, so Mahler's theorem does not imply the result.
- **Mahler 1930 and Loxton--van der Poorten 1977.** Their hypertranscendence classes are organized
  by Mahler-type functional equations such as `f_mu(z)=a_mu f_mu(Omega z)+b_mu(z)`, with algebraic
  coefficient/value hypotheses. The theorem here assumes no functional equation and instead reads
  the bounded relation lattice of coefficient logarithms. The checked announcement and full-paper
  metadata do not state the present criterion or its arbitrary-profile consequence.
- **Arithmetic Taylor-coefficient theory.** Popken and Sibuya--Sperber, and the explicit refinement
  of Krattenthaler--Rivoal, constrain DA series whose Taylor coefficients are algebraic. Here the
  coefficients `u_n exp(-b_n)` are transcendental; the algebraic data live one logarithmic level
  below them. Their denominator and finite-place bounds therefore do not apply.
- **Algebraically independent coefficients.** Gokhman's criterion does not apply: the coefficients
  need not be algebraically independent, and the all-positive specialization has every phase equal
  to one. For rational `b_n`, all magnitudes are algebraic over the one-transcendental field
  `Qbar(e)`, so algebraic-independence genericity is specifically unavailable.
- **Gap theorems.** Lipshitz--Rubel type support-gap criteria do not apply because the series has
  full support.
- **Difference-Galois theory.** Adamczewski--Dreyfus--Hardouin and related results classify
  solutions of imposed shift, `q`-difference, or Mahler equations. No such equation is present.
- **Primary sources checked:** Mahler 1930
  ([EuDML](https://eudml.org/doc/168245)); Mahler 1971
  ([BDIM](https://www.bdim.eu/item?id=RLINA_1971_8_50_2_76_0)); Loxton--van der Poorten 1977
  ([DOI](https://doi.org/10.1007/BF01836423), with the theorem announcement at
  [DOI](https://doi.org/10.1007/BF01837885)); Sibuya--Sperber 1981
  ([Annals](https://annals.math.princeton.edu/1981/113-01/p05)); Krattenthaler--Rivoal
  ([arXiv:2502.09259](https://arxiv.org/abs/2502.09259)); Gokhman 1996
  ([DOI](https://doi.org/10.1080/17476939608814872)); Lipshitz--Rubel
  ([DOI](https://doi.org/10.1007/978-1-4757-4158-2_10)); and
  Adamczewski--Dreyfus--Hardouin
  ([arXiv:1910.01874](https://arxiv.org/abs/1910.01874)).
- **Preliminary exact-search verdict.** Searches for the statement, its relation-lattice
  formulation, the private-prime specialization, and the Lindemann--Weierstrass plus ADE-coefficient
  mechanism found no equivalent or stronger theorem. The combination of balanced ADE survival,
  bounded-relation confinement, and exponential linear independence is the candidate new
  mechanism. Scientific novelty remains provisional until independent experts have checked both
  the proof and the literature.

## Exact RH-route scope

The theorem proves that coefficient positivity and arbitrarily smooth prescribed magnitude
asymptotics coexist with HT, while a finite ADE cannot erase a bounded-relation-confined logarithmic
code hidden below every asymptotic order. It excludes only RH implementations that compress such a
coefficient-log model into one finite differential constraint. It supplies no zero localization,
spectral operator, Weil sign, Li positivity, or Nyman--Beurling norm estimate, and therefore does
not categorically exclude the complete literature routes.

## Lean status

No Lean formalization is claimed. Full formalization requires differential-algebraic transitivity,
generic ADE coefficient extraction and balanced survival, bounded integer-relation confinement,
rational `p`-adic valuations, Lindemann--Weierstrass, the rational approximation construction, and the entire
series convergence argument. The theorem cannot move to stage 3 until the complete unconditional
chain is formalized.

## Gates

- [x] 0 -> 1: bounded-relation invariant, exact theorem, and attack mechanism stated.
- [x] 1 -> 2: complete unconditional paper proof and realization construction written.
- [x] Parent-theory and preliminary exact literature novelty audit.
- [ ] Independent proof audit.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved private-denominator valuation exposure HT and arbitrary superlinear-profile
  realization by private rational approximants.
- 2026-07-11 — Extracted the general bounded-relation confinement law, supplied the missing
  balanced-survival proof, repaired ADE normalization, and completed a preliminary parent/literature
  audit. Promoted provisionally to candidate new scientific knowledge pending independent review.
