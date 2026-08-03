# Airy-tower zero-loop rigidity for ramified Stokes circles

- **Status:** in progress
- **Knowledge label:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Created:** 2026-08-03
- **Area:** irregular nonabelian Hodge theory; Stokes geometry; twisted fission trees
- **Exact open core:** prove the zero-loop/sign theorem below, then derive and audit its global graph, Fourier-resolution, and Stokes-knot consequences.

## 1. Exact frozen claim

Let `I = <q>` be a ramified Stokes circle of ramification order `r > 1`. Write its
characteristic exponents with a common denominator `r` as

```text
beta_1/r > ... > beta_m/r > 0,
```

and its strict characteristic gcd chain as

```text
e_0 = r > e_1 > ... > e_m = 1,
e_i = gcd(r, beta_1, ..., beta_i).
```

The diagonal multiplicity of the core nonabelian Hodge diagram is

```text
B(I,I) = sum_i beta_i (e_(i-1) - e_i) - r^2 + 1.
```

### Main theorem: Airy-tower rigidity

`[CONJECTURE]` The sign of `B(I,I)` is determined by the first index `j` for which

```text
beta_j != e_(j-1) + e_j.
```

It is negative when `beta_j < e_(j-1) + e_j`, positive when the inequality is reversed,
and zero when there is no such index. Consequently,

```text
B(I,I) = 0  <=>  beta_i = e_(i-1) + e_i for every i.
```

Call these zero-loop characteristic data **Airy towers**.

### Global separated-core theorem

`[CONJECTURE]` Suppose `Theta = sum_i I_i` is a finite irregular class whose Stokes
circles are ramified, pairwise have zero common part, and have no diagonal loops. For each
`i`, write

```text
r_i = e_(i,0) > e_(i,1) > ... > e_(i,m_i) = 1
```

for its Airy-tower divisor chain and put `a_i = r_i / e_(i,1)`. Then

```text
B(I_i,I_j) = r_i r_j / min(a_i, a_j)              (i != j).
```

Conversely every finite family of strict divisor chains from `r_i` to `1` is realised by
pairwise separated Stokes circles and has exactly this loopless core graph.

Thus separated loopless twisted cores are classified by ordered multiplicative
factorisations, while their rescaled edge matrix depends only on first factors:

```text
B(I_i,I_j)/(r_i r_j) = 1 / min(a_i,a_j).
```

## 2. Why this would be new and significant

Current literature supplies:

1. exact loop/edge multiplicity formulas for arbitrary Stokes circles;
2. fission trees as sharp classifiers of admissible deformation classes;
3. necessary rescaled-ultrametric inequalities for twisted nonabelian Hodge diagrams;
4. an exact characterisation only in the untwisted case and for simply-laced twisted graphs.

No located source classifies zero-loop ramified Stokes circles, gives the lexicographic sign
law, identifies their characteristic data with divisor chains/ordered factorisations, or
classifies the separated twisted cores above.

If true, the theorem exposes the exact ramified structures invisible to a loopless Cartan
shadow. It also gives explicit families of different Stokes knots/fission trees with the same
nonabelian Hodge graph and a finite arithmetic recognition theorem when ramification data are
fixed.

## 3. Prior-art boundary

Primary sources audited before freezing:

- Biquard--Boalch, *Wild non-abelian Hodge theory on curves* (2004).
- Hiroe, *Ramified irregular singularities of meromorphic connections and plane curve
  singularities* (2017): dual Puiseux characteristics, Milnor/irregularity formulas, local
  Fourier resolution, iterated-torus-knot Stokes topology.
- Boalch--Douçot--Rembado, *Twisted local wild mapping class groups: configuration spaces,
  fission trees and complex braids* (PRIMS 2025): exact fission-tree realisation theorem.
- Boalch, *Counting the fission trees and nonabelian Hodge graphs* (JGP 2025).
- Douçot, *New nonabelian Hodge graphs from twisted irregular connections* (2025): exact
  multiplicity formulas, necessary ultrametric constraints, fission-graph characterisation,
  simple-graph theorem.
- Douçot, *Basic representations of genus zero nonabelian Hodge spaces* (SIGMA 2026):
  enriched trees and explicit statement that diagrams alone lose fission data.
- Douçot, *Fourier transform of irregular connections on P1 and classification of
  Argyres--Douglas theories* (2026).

Exact-phrase and concept searches found no collision as of 2026-08-03. This is a provisional
novelty result, not a publication claim.

## 4. Initial proof mechanism

Set `R = e_(j-1)` and `E = e_j`. The gcd condition implies `beta_j` is a multiple of
`E`, and `gcd(beta_j/E, R/E) = 1`. The canonical value `R + E` is the first allowed value
strictly above `R`.

The loop functional has the recursive defect identity

```text
B_R = (R - E)(beta_j - R - E) + B_E.
```

More decisively:

- if `beta_j < R + E`, coprimality forces `beta_j <= R - E`; since all later
  characteristic exponents are smaller, their full weighted sum is `< R^2 - 1`;
- if `beta_j > R + E`, discreteness forces `beta_j >= R + 2E`, and its first weighted
  term alone is `> R^2 - 1`;
- if `beta_j = R + E`, its contribution is `R^2 - E^2`, leaving the identical problem
  with ramification `E`.

Induction gives the sign and equality classification. Paper proof still needs every inequality,
index convention, and geometric translation checked against source definitions.

## 5. Consequences to prove, not assume

1. Airy towers are in bijection with strict divisor chains `r=e_0>...>e_m=1`, equivalently
   ordered multiplicative factorisations `r=a_1...a_m`, `a_i>=2`.
2. For `r=p^k`, the number of Airy towers is `2^(k-1)`; for squarefree `r` it is the ordered
   Bell/Fubini number on the prime factors.
3. Airy-tower dual Puiseux data satisfy Hiroe's local Fourier-resolution congruences through
   the negative branch `e_(i-1) == -e_i (mod beta_i)`.
4. The associated Stokes links are an explicit iterated-torus-knot family indexed by the same
   ordered factorisations.
5. Pairwise zero-common-part edge multiplicities obey the global formula in section 1.
6. Fixed ramification decoration makes the Stokes-Cartan shadow finite-to-one; the deeper
   divisor-chain fibre is explicit in the separated zero-loop locus.

## 6. Hostile falsification checklist

- [ ] Check whether `B(I,I)` may be zero when the characteristic list contains
  inconsequential exponents; verify they do not enter the invariant.
- [ ] Check all slope regimes, including leading slope below or equal to `1`.
- [ ] Check the strict-exponent bound used when the first characteristic value is subcanonical.
- [ ] Check parity of `B(I,I)` follows from the characteristic formula.
- [ ] Check Airy-tower level data satisfy the increasing-common-denominator axiom.
- [ ] Check edge formula when leading slopes coincide but Galois orbits are separated.
- [ ] Check realisation can choose all leading coefficients simultaneously outside root-of-unity
  collision loci.
- [ ] Search singularity/semigroup literature for the same equality case under a different name.
- [ ] Separate local Fourier resolvability (known criterion) from the new zero-loop equality case.
- [ ] Do not claim diagram equality implies isomorphic wild character varieties or isomonodromy
  systems.

## 7. Lean target

Formalise the exact finite arithmetic model, not a proxy:

1. characteristic gcd chains and admissibility;
2. loop multiplicity as an integer-valued weighted sum;
3. recursive defect and lexicographic sign theorem;
4. zero-loop iff canonical Airy tower;
5. divisor-chain/ordered-factorisation equivalence;
6. separated-core edge formula and rescaled ultrametric law;
7. umbrella imports and formal lint.

All Lean statements must be unconditional. No `sorry`, `admit`, new `axiom`, `opaque`, or
`unsafe` declaration.

## 8. Anti-theatre gate

Current status is only `[CONJECTURE]`: proof mechanism is promising but not audited. No wild
nonabelian Hodge correspondence, Fourier-duality, knot-classification, or journal-level claim is
counted as proved. Stage promotion requires a dependency-closed paper proof and a hostile review
that tries to break both arithmetic and geometric translations.

## 9. Paper proof: arithmetic core

This section fixes the arithmetic conventions and proves the frozen local theorem. Geometric
translations remain under audit.

### 9.1 Characteristic data

A ramified characteristic datum is a tuple

```text
(r; beta_1, ..., beta_m; e_0, ..., e_m)
```

such that

```text
r = e_0 > e_1 > ... > e_m = 1,
beta_1 > ... > beta_m > 0,
e_i = gcd(e_(i-1), beta_i).
```

Induction gives `e_i = gcd(r,beta_1,...,beta_i)` and `e_i | e_(i-1)`. These are exactly
the integer characteristic data obtained by writing the levels of a ramified Stokes circle over
its final common denominator `r`.

Define

```text
S(r,beta,e) = sum_(i=1)^m beta_i (e_(i-1)-e_i),
Loop(r,beta,e) = S(r,beta,e) - r^2 + 1.
```

By the endomorphism-irregularity formula, `S = Irr(End(I))`; by the nonabelian Hodge
diagram formula, `Loop = B(I,I)`.

### 9.2 Threshold lemma

**Lemma 9.1.** Let `R>E>=1`, `E|R`, and `gcd(R,beta)=E`. Then:

1. `beta=R+E` is admissible;
2. if `beta<R+E`, then `beta<=R-E`;
3. if `beta>R+E`, then `beta>=R+2E`.

**Proof.** Write `R=aE` and `beta=cE`. Since `R>E`, `a>=2`, and the gcd
condition gives `gcd(a,c)=1`. The canonical value has `c=a+1`, which is coprime to
`a`. If `c<a+1`, then `c` cannot equal `a`, so `c<=a-1`. If `c>a+1`, integrality
gives `c>=a+2`. Multiplication by `E` proves all claims. `QED`

### 9.3 First-deviation sign lemma

**Lemma 9.2.** Consider a characteristic datum beginning at `R=e_0`, and let
`E=e_1`, `beta=beta_1`.

1. If `beta<R+E`, then `Loop<0`.
2. If `beta>R+E`, then `Loop>0`.
3. If `beta=R+E`, then `Loop` equals the loop functional of the tail datum
   `(E; beta_2,...,beta_m; e_1,...,e_m)`.

**Proof.**

For (1), Lemma 9.1 gives `beta<=R-E`. Every later characteristic exponent is
strictly smaller than `beta`. Since the drops in the gcd chain telescope to `R-1`,

```text
S < beta (R-1) <= (R-E)(R-1) < (R+1)(R-1)=R^2-1.
```

The same conclusion holds when the tail is empty; then the first displayed strict inequality is
replaced by `S=beta(R-1)<R^2-1`. Hence `Loop<0`.

For (2), Lemma 9.1 gives `beta>=R+2E`. As `E|R` and `E<R`, one has
`R>=2E`. The first summand alone satisfies

```text
beta(R-E) >= (R+2E)(R-E)
              = R^2 + E(R-2E)
              >= R^2 > R^2-1.
```

All remaining summands are positive, so `Loop>0`.

For (3), the first summand telescopes exactly:

```text
(R+E)(R-E)=R^2-E^2.
```

Therefore

```text
Loop_R
= (R^2-E^2) + sum_(i>=2) beta_i(e_(i-1)-e_i) - R^2 + 1
= sum_(i>=2) beta_i(e_(i-1)-e_i) - E^2 + 1
= Loop_E.
```

`QED`

### 9.4 Airy-tower sign theorem

**Theorem 9.3 (Airy-tower sign law).** The sign of `B(I,I)` is the sign of the first
difference

```text
beta_j - (e_(j-1)+e_j).
```

If there is no difference, `B(I,I)=0`. In particular,

```text
B(I,I)=0 <=> beta_i=e_(i-1)+e_i for every i.
```

**Proof.** Apply Lemma 9.2 repeatedly while the characteristic value is canonical. Each
canonical step removes the first entry without changing the loop functional. At the first
noncanonical entry, clauses (1) and (2) determine the strict sign. If every entry is canonical,
the recursion reaches the terminal datum of ramification `1`, whose empty sum has loop
`-1+1=0`. `QED`

This proves the frozen local conjecture.

## 10. Divisor chains and Fourier--Euclidean reduction

**Theorem 10.1 (classification).** Airy towers of ramification `r` are in bijection with
strict divisor chains

```text
r=e_0>e_1>...>e_m=1,  e_i | e_(i-1),
```

and hence with ordered multiplicative factorisations

```text
r=a_1...a_m,  a_i>=2.
```

**Proof.** Given the divisor chain, put `beta_i=e_(i-1)+e_i`. Then

```text
beta_i-beta_(i+1)=e_(i-1)-e_(i+1)>0
```

and

```text
gcd(e_(i-1),beta_i)=gcd(e_(i-1),e_i)=e_i.
```

Thus this is a characteristic datum, and Theorem 9.3 gives zero loop. Conversely Theorem 9.3
forces these values from any zero-loop datum. Finally set `a_i=e_(i-1)/e_i`; telescoping
gives `prod_i a_i=r`. The inverse sends an ordered factorisation to
`e_i=r/(a_1...a_i)`. `QED`

**Corollary 10.2 (enumeration).** Let `A(r)` be the number of Airy towers of ramification
`r`.

1. If `r=p^k`, then `A(r)=2^(k-1)`.
2. If `r` is a product of `k` distinct primes, then
   `A(r)=sum_(j=1)^k j! S(k,j)`, the `k`-th ordered Bell number.

**Proof.** Ordered factorisations of `p^k` are compositions of `k`, counted by the choices of
cuts in its `k-1` gaps. For squarefree `r`, an ordered factorisation is exactly an ordered set
partition of its `k` prime factors. `QED`

**Corollary 10.3 (negative Fourier branch).** In Hiroe's dual-Puiseux conventions, every
Airy tower satisfies

```text
e_(i-1) == -e_i (mod beta_i)
```

at each characteristic step. Hence Hiroe's resolution theorem reduces its irreducible formal
connection to rank one by local Fourier transforms and additions. At each rank drop
`e_(i-1) -> e_i`, the diagonal diagram multiplicity remains zero.

**Proof.** The congruence is immediate from `beta_i=e_(i-1)+e_i`. Hiroe's theorem then
applies. Loop preservation is clause (3) of Lemma 9.2. `QED`

The converse needs a size condition: if the negative congruence holds and
`beta_i>e_(i-1)`, then `beta_i` divides `e_(i-1)+e_i` and is greater than half that
number, so it equals the full sum. Thus Airy towers are exactly the all-negative, large-step
Fourier-resolvable characteristic data.

## 11. Separated loopless twisted cores

Let an Airy tower have first quotient and first characteristic slope

```text
a=r/e_1,
k=beta_1/r=(r+e_1)/r=1+1/a.
```

Two Stokes circles are **leading-separated** when their common part is zero. If their leading
slopes agree, this means their leading coefficients lie in distinct root-of-unity orbits.

**Theorem 11.1 (separated-core formula).** Let `I_i,I_j` be leading-separated ramified
zero-loop Stokes circles, with ramification orders `r_i,r_j` and first quotients `a_i,a_j`.
Then

```text
B(I_i,I_j)=r_i r_j/min(a_i,a_j).
```

**Proof.** Suppose `a_i<=a_j`; then `1+1/a_i>=1+1/a_j`. The common part is zero,
so the edge formula has no common-level terms. Its fission exponent is the leading slope of
`I_i`, whose numerator over `r_i` is `beta_(i,1)=r_i+e_(i,1)`. Therefore

```text
B(I_i,I_j)
= r_j(beta_(i,1)-r_i)
= r_j e_(i,1)
= r_i r_j/a_i.
```

The expression is symmetric when the slopes agree. `QED`

**Theorem 11.2 (simultaneous realisation).** Every finite family of strict divisor chains is
realised by pairwise leading-separated Stokes circles, and its diagram is the loopless core of
Theorem 11.1.

**Proof.** For each chain choose

```text
q_i = sum_h c_(i,h) z^((e_(i,h-1)+e_(i,h))/r_i)
```

with all coefficients nonzero. The gcd calculation in Theorem 10.1 shows that its levels are
exactly the prescribed Airy tower. For every fixed first quotient `a`, choose the finitely many
leading coefficients outside each other's finite `mu_a`-orbits. Then equal-slope leading Galois
orbits are distinct; unequal slopes are automatically distinct. Hence every pair has zero common
part. Theorem 9.3 gives zero diagonal and Theorem 11.1 gives every off-diagonal entry. `QED`

**Corollary 11.3 (exact hidden fibre).** Fix the labelled data `(r_i,a_i)` in the separated
zero-loop locus. The diagram forgets every tail factorisation of `r_i/a_i`. Its fibre in labelled
admissible-deformation classes has cardinality

```text
product_i A(r_i/a_i).
```

Distinct points of this fibre have distinct level data, hence distinct fission trees. Via Hiroe's
Stokes-link theorem, distinct dual Puiseux characteristics also give distinct iterated-torus-knot
Stokes types.

## 12. Exact edge spectrum for one-level Airy circles

A **simple Airy circle of ramification `r>1`** has the single level `(r+1)/r`. Adding
unramified terms does not change this level datum or its zero diagonal multiplicity.

**Theorem 12.1 (two-circle spectrum).** Let `I,J` be distinct simple Airy circles of
ramification `r,s>1`. The possible nonnegative edge multiplicities are exactly

```text
{max(r,s)} union rs*N_(>0),                    if r != s,
{0,1,...,r} union r^2*N_(>0),                 if r = s.
```

**Proof.** All exponents above a simple Airy level are positive integers. If the first difference
of `I,J` occurs there, its degree is an integer `d>=2`; the common terms above it have
denominator one and contribute zero to the rescaled formula. Thus

```text
B(I,J)=rs(d-1),
```

giving exactly the positive multiples of `rs`.

Assume no such high unramified difference occurs. If `r!=s`, the two characteristic slopes
`1+1/r` and `1+1/s` differ, so their first difference is the larger slope. The zero-common-part
edge formula gives `max(r,s)`.

If `r=s`, either the leading Galois orbits are distinct, giving edge `r`, or the leading terms
are common. In the latter case the first lower difference may occur exactly at

```text
f=j/r,  1<=j<=r,
```

since these and only these are the admissible exponents below `(r+1)/r`. The common-level
edge formula gives

```text
B(I,J)=r f-1=j-1,
```

which yields `0,...,r-1`.

Every listed value is realised: choose distinct coefficients at the stated first differing
exponent, keeping the single mandatory coefficient nonzero. `QED`

**Corollary 12.2 (new obstruction beyond ultrametricity).** Two ramification-two simple Airy
vertices can have edge multiplicity

```text
0,1,2,4,8,12,...,
```

but never `3`. Rescaled ultrametricity has no content on two vertices, so the 2025 necessary
ultrametric criterion cannot detect this obstruction.

If one circle is unramified and the other is simple Airy of ramification `r`, the identical
argument gives the spectrum `{1} union r*N_(>0)`; two unramified circles realise every
nonnegative edge multiplicity.

## 13. Finite-fibre theorem for decorated diagrams

**Theorem 13.1.** Fix a finite labelled diagram `B` and a ramification order `r_i` at every
vertex. There are only finitely many labelled fission trees whose decorated nonabelian Hodge
diagram is `(B,r)`. The fibre is effectively enumerable.

**Proof.** For vertex `i`, let its characteristic sequence be `beta_(i,h)` and gcd chain
`e_(i,h)`. The diagonal formula fixes

```text
sum_h beta_(i,h)(e_(i,h-1)-e_(i,h)) = B_ii+r_i^2-1.
```

There are finitely many strict divisor chains from `r_i` to `1`. For each chain, every positive
summand is bounded by the fixed right side, so every integer `beta_(i,h)` lies in a finite
interval. Hence each vertex has finitely many possible level data.

Fix one such choice at every vertex. For a pair of leaves, choose the finite common
characteristic prefix and the fission case at their nearest common ancestor. On each resulting
interval of admissible exponents, the edge formula is affine with a strictly positive coefficient
of the fission exponent. Thus the fixed value `B_ij` determines at most one fission exponent
for that choice. Only finitely many pair data remain. Finally, the fission-tree axioms are finite
compatibility checks, and fission data determine a labelled fission tree uniquely. Enumeration
of the preceding finite choices followed by those checks lists the exact fibre. `QED`

Without the ramification decoration the statement is false: the one-vertex zero-loop diagram is
realised by the simple Airy circle of every ramification `r>1`. Thus the decoration is exactly
what restores finite ambiguity.

## 14. Worked diagram twin

Take the Airy towers

```text
r=2:  2>1,       q_1=c_1 z^(3/2),
r=3:  3>1,       q_2=c_2 z^(4/3),
r=4:  4>2>1,     q_3=c_3 z^(3/2)+d_3 z^(3/4).
```

Choose `c_1,c_3` in distinct `mu_2`-orbits. Their first quotients are `2,3,2`, so
Theorem 11.1 gives edge multiplicities

```text
B_12=3, B_13=4, B_23=6.
```

This is the same core multigraph exhibited in the 2025 twisted-graph paper, but that paper's
realisation has ramification decoration `(1,3,2)`, whereas this all-ramified Airy-tower
realisation has `(2,3,4)`. Diagram equality alone must not be promoted to an isomorphism of
the resulting wild character varieties; the proved conclusion is the new Stokes realisation and
the precise difference in fission data.
