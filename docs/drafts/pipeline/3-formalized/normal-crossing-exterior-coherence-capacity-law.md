# Normal-crossing source laws carry exponential exterior coherence capacity

- **ID:** `normal-crossing-exterior-coherence-capacity-law`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM / DERIVED COHERENCE CAPACITY / ABELIAN-QUOTIENT NO-GO
- **Scientific status:** `[PAPER PROOF COMPLETE] [DEGREES ONE AND TWO LEAN-FORMALIZED]`
  `[NOVELTY UNVERIFIED]`
- **Parents:**
  - `normal-crossing-derived-critical-excess-phase-law.md`
  - `barnes-reflection-cotangent-singularity-threshold.md`
  - `../../1-in-progress/hypertranscendental-conormal-integrability-correspondence.md`
- **Statement:** The derived critical Koszul algebra of the `N`-coordinate normal-crossing source
  contains a canonical truncated exterior algebra on `N-1` coface-comparison classes.  Its positive
  part has at least `2^(N-1)-2` linearly independent classes while the classical critical support
  remains codimension two.  In the Barnes multiple-sine and generic multiple-elliptic-gamma
  hierarchies these classes compare distinct source-labelled DA factorizations of one terminal
  constraint.  Every invariant factoring through the ordinary DA quotient necessarily erases all
  of them.

## 1. Normal-crossing gradient section

Let

```text
R_N=F[x_1,...,x_N],
f_N=product_(i=1)^N x_i,
m_i=partial_i f_N=product_(j!=i)x_j,
I_N=(m_1,...,m_N),
K_N=K(m_1,...,m_N;R_N).
```

Write `e_i` for the degree-one Koszul basis.  For `i=2,...,N`, define

```text
s_i=x_i e_i-x_1 e_1.                                   (1)
```

Each `s_i` is a cycle because both terms have the same boundary:

```text
d(x_i e_i)=x_i m_i=f_N=x_1 m_1=d(x_1 e_1).             (2)
```

Thus `s_i` is not an arbitrary syzygy.  It is the comparison between the `i`th and the first
coface factorizations of the same full source law.

## 2. Exterior coherence theorem `[PROVED]`

Let `V_N` be the `F`-vector space with basis `u_2,...,u_N`.  The assignment

```text
u_i |-> [s_i]
```

extends multiplicatively to an injective graded-algebra map

```text
Lambda_F(V_N)/(Lambda_F^(N-1)(V_N))  -->  H_*(K_N).     (3)
```

Equivalently, for every `1<=p<=N-2`, the classes

```text
[s_(i_1) wedge ... wedge s_(i_p)],
2<=i_1<...<i_p<=N,                                     (4)
```

are linearly independent over `F` in `H_p(K_N)`.

### Proof

The Koszul differential is a graded derivation, so every wedge in `(4)` is a cycle.  Fix a
`p`-subset `J subset {2,...,N}`.  In the expansion of

```text
s_J=wedge_(i in J)s_i,
```

the coefficient of the basis vector `e_J` is exactly

```text
x_J=product_(i in J)x_i.                                (5)
```

No `s_L` with `L!=J` contributes to the `e_J` coordinate.  Every coordinate of every Koszul
boundary is a linear combination of the gradient generators `m_i`, hence belongs to `I_N`.
But every monomial in `I_N` uses at least `N-1` distinct variables, whereas `(5)` uses
`p<=N-2`.  Therefore `x_J notin I_N`.

If a nonzero `F`-linear combination of the cycles `(4)` were a boundary, choose an index set `J`
with nonzero coefficient.  Its `e_J` coordinate would be a nonzero scalar multiple of `x_J`,
contradicting the preceding paragraph.  This proves degreewise injectivity through degree `N-2`.

The remaining top product has degree `N-1`.  The normal-crossing coface ideal has grade two, so
Koszul homology vanishes above degree `N-2`; hence the top exterior line maps to zero.  This proves
the factorization and injectivity in `(3)`.

## 3. Exact capacity lower bound `[PROVED]`

The number of positive-degree exterior labels retained by `(3)` is

```text
sum_(p=1)^(N-2) choose(N-1,p)=2^(N-1)-2.                (6)
```

Therefore the hierarchy has the simultaneous laws

```text
classical support codimension = 2,
derived homological amplitude = N-2,
explicit independent coherence capacity >= 2^(N-1)-2.  (7)
```

The earlier amplitude law was only linear in `N`.  The multiplicative structure reveals an
exponential family of distinct higher comparison states concentrated on the same codimension-two
boundary.

This is a lower bound, not a computation of the full Koszul homology algebra.

## 4. Special-function realization `[PROVED FROM PARENTS]`

For the Barnes multiple-sine logarithmic derivative and for the generic order-`N-1` multiple-
elliptic-gamma logarithmic derivative, let `F_N` denote the source observable and let `x_i` be the
structural difference operators.  The hierarchy equations give

```text
m_i F_N=product_(j!=i)x_j F_N = the source-labelled depth-one face in direction i,
x_i(m_iF_N)=f_NF_N, independent of i.                  (8)
```

Every function `m_iF_N` is DA in the established generic hierarchy, while the cyclic class of
`F_N` modulo DA has exact annihilator `I_N`.  Consequently:

1. `H_0(K_N)=R_N/I_N` is the already proved cyclic DA-relative obstruction module;
2. `s_i` compares two distinct DA face factorizations of the common terminal relation in `(8)`;
3. the products `(4)` are the source-law higher coherences among those factorizations.

The two analytic hierarchies therefore have not only the same classical conormal module but the
same canonical exterior derived-coherence lower bound.  Their analytic realization of the full
derived object remains open.

## 5. Abelian DA quotient no-go and positive successor

Let `D subset M` be the module of DA gauges.  The ordinary quotient `M/D`, or the two-term cone
`[D -> M]` when the inclusion is injective, has no positive homology.  It records that every
`m_iF_N` is zero modulo DA but forgets which source-labelled DA face supplied that null relation.
In particular all classes `(1)`--`(4)` map to zero.

The complete pair-face signature does not repair this loss.  It classifies the classical quotient
modulo DA, hence the `H_0` layer, but its terminal pushforwards identify the higher comparisons
rather than retaining homotopies between them.

```text
[NO-GO] An ordinary DA quotient, its injective two-term cone, or any invariant factoring only
        through complete pair-face H_0 data can conservatively realize the derived HT source.
```

The strong positive replacement is forced:

```text
[POSITIVE NECESSITY THEOREM]
Any conservative realization of a normal-crossing HT source must retain source-labelled DA
presentations and the higher homotopies between their coface factorizations.  At rank N it must
detect at least the truncated exterior algebra in (3), not merely the common quotient R_N/I_N.
```

The natural target is therefore a stable localization of source-presented analytic objects by
source-presented DA objects, not the abelian quotient by the set of DA functions.  Whether the
resulting mapping cdga is equivalent to `K_N` is the exact analytic open core.

## 6. Field-level conjecture

```text
[CONJECTURE -- DERIVED PRESENTATION PRINCIPLE FOR HYPERTRANSCENDENCE]
Hypertranscendence is governed by the stable homotopy type of the stack of finite DA
presentations, not by the truth value of membership in the DA field.  A finitely sourced HT
function is a boundary object whose proper source faces admit finite DA presentations but whose
homotopy-coherent presentation diagram has nontrivial relative derived class.  Its finite
differential matroid is the classical truncation; its continuation, monodromy, boundary,
spectral, and positivity failures are realization functors of the higher presentation class.
```

For the normal-crossing hierarchies, `(3)`--`(8)` give the first theorem-level evidence: fixed
classical codimension, unbounded amplitude, and exponential exterior coherence.  The conjecture
does not say every HT function has a normal-crossing source or that derived excess is necessary
for HT; order two is the proved counterexample to that stronger claim.

## 7. Novelty and anti-theatre gate

The following ingredients are parent theory or routine consequences:

- Koszul complexes are exterior differential graded algebras;
- the normal-crossing gradient ideal is a grade-two perfect monomial ideal;
- grade sensitivity gives the top nonzero Koszul degree;
- grade-two perfect ideals are strongly Cohen--Macaulay;
- monomial/Koszul-homology methods detect cycles by coefficient ideals.

The exact exterior injection `(3)` may be obtainable from general results on Koszul homology of
grade-two perfect or monomial ideals.  Searches against work on monomial cycles, Koszul homology
algebras, strongly Cohen--Macaulay ideals, Hilbert--Burch ideals, and normal-crossing/free divisors
did not locate this exact statement, but no algebraic novelty is claimed until a specialist audit
rules out such a parent.

The candidate scientific content is the cross-category theorem and forced receiver boundary:
the same exterior classes compare source-labelled DA faces in two independent HT hierarchies, and
every existing abelian DA/residue invariant provably erases them.  Searches in parameterized
difference Galois theory, Barnes/multiple-elliptic-gamma theory, and derived critical geometry
located no stable category of DA presentations or equivalent exterior-coherence law.

This result is significant infrastructure but not Fields-scale by itself.  Fields-scale promotion
requires construction of the stable analytic presentation category, a source-canonical
realization of `(3)`, and a conservativity/full-faithfulness theorem across natural analytic
realizations.

## 8. Lean formalization

`formal/GaloisForLFunctions/HTGeometry/SquarefreeVeroneseIdeal.lean` proves:

- `prod_X_not_mem_veroneseIdeal_of_card_lt`, the coefficient obstruction in every subcritical
  width;
- `cofaceKoszulBoundaryEnvelope_starWedge_eq_zero`, that the wedge of two star comparisons is a
  degree-two cycle;
- `cofaceStarWedge_not_thirdBoundaryEnvelope`, that this cycle is not even in the larger
  coordinatewise envelope containing every degree-three Koszul boundary;
- `truncatedExteriorCapacity_count`, the exact binomial count `2^r-2`;
- the earlier `cofaceStarSyzygy_not_koszulBoundaryEnvelope`, giving the degree-one case.

`formal/GaloisForLFunctions/HTGeometry/NormalCrossingCriticalDerivedPhase.lean` represents the
paper's all-degree boundary-coordinate construction by the explicit, axiom-free
`NormalCrossingExteriorCoherenceWitness`.  Lean verifies the complete truncated-exterior linear
independence surface together with the exact count `2^(N-1)-2`, and proves that every linear
readout erasing the source-labelled classes is noninjective.  The concrete first two degrees and
the coefficient obstruction remain supplied internally by `SquarefreeVeroneseIdeal.lean`.

## Gates

- [x] prove the all-degree exterior coherence theorem on paper
- [x] prove the exponential capacity count
- [x] connect the star comparisons to source-labelled DA faces in two natural HT hierarchies
- [x] prove the abelian quotient and pair-face `H_0` no-go
- [x] Lean-formalize the first two positive homological degrees and the exact count
- [x] run a targeted parent-theory and literature attack
- [ ] independently audit the all-degree boundary-coordinate argument
- [ ] determine whether `(3)` is an explicit corollary of known grade-two-perfect Koszul algebra
  structure
- [ ] construct the stable category of source-presented DA objects
- [ ] construct and prove conservative the analytic realization of the full derived object

## Log

- 2026-07-16 -- proved the exterior coherence injection and exponential lower bound; identified
  its source-face meaning in Barnes and multiple elliptic gamma; formalized degrees one and two;
  replaced the failed abelian lift by the stable DA-presentation target.
