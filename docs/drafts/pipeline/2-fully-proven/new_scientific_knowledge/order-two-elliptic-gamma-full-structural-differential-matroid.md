# The order-two elliptic-gamma structural orbit has no hidden nonlinear relations

- **ID:** `order-two-elliptic-gamma-full-structural-differential-matroid`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / COMPLETE DIFFERENTIAL-ALGEBRAIC MATROID
- **Date:** 2026-07-10
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` -- conditional on the independently
  unaudited order-one elliptic-gamma atomic theorem and still requiring an independent specialist
  priority check. The squarefree structural annihilator was already proved; the new result below
  upgrades it from a classification of DA linear combinations to an exact classification of every
  nonlinear differential dependence among finite structural translates.
- **Parents:**
  `multiple-elliptic-gamma-transverse-constraint-depth`;
  `atomic-defect-full-orbit-differential-matroid`;
  `elliptic-gamma-rank-three-da-spectrum`
- **Statement:** For the generic order-two multiple elliptic-gamma logarithmic derivative, the
  differential transcendence degree of any finite family of constant-coefficient
  differential-translation combinations is the linear rank of their classes in the localized
  Stanley--Reisner module

  ```text
  C(delta)[t_0^(+-1),t_1^(+-1),t_2^(+-1)]
    /( (t_0-1)(t_1-1), (t_0-1)(t_2-1), (t_1-1)(t_2-1) ).
  ```

  Thus the known squarefree face relations generate all differential-algebraic dependence; no
  additional nonlinear relations exist.

## Goal

The exact annihilator theorem proves

```text
P(T)Psi_2 is DA iff P belongs to I_2.
```

That is only a one-function test. It does not exclude a nonlinear differential polynomial relation
among several non-DA translates whose individual classes are linearly independent modulo `I_2`.
The goal is to compute the entire differential-algebraic matroid of the structural orbit.

The mechanism is not another hierarchy descent. Each first structural difference is an order-one
elliptic-gamma atom. Its missing parameter acts as an external translation and produces a free
differential orbit. The other structural directions act DA-trivially on that orbit. Replicating a
hypothetical dependence into arbitrarily many disjoint orbit blocks then exceeds the finite
differential transcendence budget of its coefficient field.

## Setup

Let `tau_0,tau_1,tau_2 in H` and assume

```text
1,tau_0,tau_1,tau_2
```

are linearly independent over `Q`. Put

```text
F=Psi_2(z;tau_0,tau_1,tau_2),
T_i=T_(tau_i),
x_i=T_i-1.
```

For `{i,j,k}={0,1,2}`, define the order-one face atom

```text
A_i=x_iF=Psi_1(z;tau_j,tau_k)                              (1)
```

up to the harmless DA normalization used in the hierarchy. Its DA translation subgroup is

```text
H_i=Z+Z tau_j+Z tau_k.
```

The missing parameter `tau_i` has infinite order modulo `H_i`. Conditional on the order-one atomic
theorem and `atomic-defect-full-orbit-differential-matroid`, the orbit

```text
{T_i^n A_i:n in Z}                                         (2)
```

is differentially algebraically independent over `C(z)`.

For `i!=j`, the translation `T_j` acts DA-trivially on the entire `i`-branch:

```text
T_j(T_i^nA_i)-T_i^nA_i=T_i^n(x_jA_i) is DA,                (3)
```

because `tau_j` is a structural parameter of the order-one face `A_i` and its difference is a theta
logarithmic derivative.

## Relative orbit replication lemma `[PROVED HERE]`

Let `k` be a differential field, let `sigma` commute with its derivation, and let

```text
...,sigma^(-1)x,x,sigma x,...
```

be differentially algebraically independent over `k`. Let `K` be a differential field extension of
finite differential transcendence degree

```text
d=dtrdeg_k K<infinity.
```

Assume that, for every integer `n`, the field `sigma^n(K)` is differentially algebraic over `K`
inside a common overfield. Then the full `sigma`-orbit of `x` remains differentially algebraically
independent over `K`.

### Proof

Suppose a finite orbit block indexed by `S subset Z`, `card(S)=s`, is differentially dependent over
`K`. Choose integers `N_1,...,N_M` such that the sets `S+N_j` are pairwise disjoint. Translating the
dependence by `sigma^(N_j)` makes every corresponding block dependent over `sigma^(N_j)(K)`.

Let `K_*` be the compositum of `K` and these finitely many translated coefficient fields. By the
hypothesis, `K_*/K` is differentially algebraic, so

```text
dtrdeg_k K_*=d.
```

Every translated block contributes differential transcendence degree at most `s-1` over `K_*`.
Consequently their union has degree at most

```text
d+M(s-1)
```

over `k`. But the blocks are disjoint subsets of the independent orbit, so the same field contains
`Ms` differentially independent elements. Hence

```text
Ms <= d+M(s-1),
```

or `M<=d`. Choosing `M>d` is a contradiction. `QED`

## Joint independence of the three face branches `[PROVED HERE]`

For arbitrary finite sets `S_0,S_1,S_2 subset Z`, the family

```text
{T_i^nA_i : i in {0,1,2}, n in S_i}                        (4)
```

is differentially algebraically independent over `C(z)`.

### Proof

The `0`-branch is independent by (2). Let `K_0` be the field generated by a finite part of that
branch. Equation (3) shows that every `T_1^n(K_0)` is DA over `K_0`. The relative replication lemma,
applied to the independent `T_1`-orbit of `A_1`, shows that the full `1`-branch remains independent
over `K_0`.

Let `K_01` be generated by finite parts of the first two branches. Translation `T_2` acts DA-trivially
on both of them by (3). Apply the replication lemma to the independent `T_2`-orbit of `A_2`. This
proves joint independence of all three finite branch families. `QED`

The argument is triangular only in its presentation. Any ordering of the three branches works: the
missing direction of the branch being added is structural for every earlier face.

## The order-two primitive is independent from all face branches `[PROVED HERE]`

The family

```text
{F} union {T_i^nA_i:i in {0,1,2}, n in Z}                  (5)
```

is differentially algebraically independent over `C(z)` in the sense that every finite subfamily is
independent.

### Proof

Fix finite index sets `S_i` and let `K` be generated by the corresponding branch elements. Suppose
that `F` is DA over `K`.

Choose a positive integer `N` so large that

```text
J={0,...,N-1}\(S_0 union (S_0+N))
```

is nonempty. Translate the assumed differential relation by `T_0^N`. The `0`-branch indices shift
from `S_0` to `S_0+N`; the `1`- and `2`-branch generators change only by DA functions because `T_0`
is structural on those faces. Therefore `T_0^NF` is DA over the field generated by the branch
coordinates with indices

```text
S_0 union (S_0+N), S_1, S_2
```

and finitely many DA corrections. The original `F` is DA over the same enlarged field. Their
difference is consequently DA there.

Adjoining the finitely many DA corrections does not weaken independence. Differential-algebraic
base change preserves differential transcendence degree: if `L/k` is DA, then `L<Y>/L` and
`k<Y>/k` have the same differential transcendence degree. This follows from additivity in the
towers `k subset L subset L<Y>` and `k subset k<Y> subset L<Y>`.

The hierarchy relation (1) gives the exact telescoping identity

```text
T_0^NF-F=sum_(n=0)^(N-1) T_0^nA_0.                         (6)
```

Subtract from (6) the terms whose indices already belong to `S_0 union (S_0+N)`. The remaining
nonempty sum

```text
sum_(n in J)T_0^nA_0
```

would be DA over the field generated by all complementary branch coordinates. This contradicts
the joint differential independence proved in (4). Hence `F` is differentially transcendental over
every finite branch field, proving (5). `QED`

The use of a long translation is essential. One step gives `T_0F-F=A_0`, which already belongs to
the face field and yields no contradiction. A long finite interval necessarily contains an
intermediate orbit coordinate invisible at both endpoint supports.

## Squarefree structural module

Let

```text
S=C[delta],
R=S[t_0^(+-1),t_1^(+-1),t_2^(+-1)],
I_2=(x_0x_1,x_0x_2,x_1x_2),  x_i=t_i-1.
```

The parent exact annihilator theorem gives the scalar-coefficient case, and the hierarchy gives the
inclusion

```text
I_2 subset Ann_R(F modulo DA).                             (7)
```

Every class in `R/I_2` has a unique decomposition

```text
L(delta)+x_0Q_0(delta,t_0)+x_1Q_1(delta,t_1)
        +x_2Q_2(delta,t_2).                               (8)
```

For every integer `a`, the Laurent polynomial `t_i^a-1` is divisible by `t_i-1`. Moreover, modulo
`I_2`,

```text
t_0^a t_1^b t_2^c
  =1+(t_0^a-1)+(t_1^b-1)+(t_2^c-1),
```

because the difference consists of products `(t_i^a-1)(t_j^b-1)`, each divisible by `x_ix_j`.
This proves existence for positive and negative exponents without an infinite binomial expansion.
For uniqueness, first specialize all three variables to `1`, which gives `L=0`. Then, for each
`i`, specialize the other two variables to `1`. The surviving equation is `x_iQ_i=0` in the domain
`S[t_i^(+-1)]`, so every `Q_i` vanishes.

Acting on `F`, (8) becomes, modulo DA functions,

```text
L(delta)F+sum_i Q_i(delta,T_i)A_i.                         (9)
```

The coordinates in (9) belong to the differentially independent family (5).

It follows at once that (7) is an equality even with differential-operator coefficients. If a class
in `R/I_2` is nonzero, its unique expression (8) acts as a nonzero constant-coefficient
differential-linear form in the independent coordinates (5), so its value cannot be DA. Thus

```text
Ann_R(F modulo DA)=I_2.
```

## Complete structural differential-matroid theorem `[PROVED HERE]`

For arbitrary `P_1,...,P_m in R`, let `Pbar_j` be their classes in `R/I_2`. Then

```text
dtrdeg_(C(z)) C(z)<P_1(T)F,...,P_m(T)F>_delta
  = dim_(C(delta)) span{Pbar_1,...,Pbar_m}                 (10)
```

inside

```text
C(delta) tensor_(C[delta]) (R/I_2).
```

### Proof

For the finite family, only finitely many coordinates from (5) occur in the decompositions (9).
They are differentially algebraically independent. The coefficient change from `Pbar_j` to the
coordinates in (9) is the unique module decomposition (8), hence preserves rank after localization
to `C(delta)`.

Apply the differential-linear rank lemma: for a matrix over the PID `C[delta]` acting on differential
indeterminates, the differential transcendence degree of its outputs is its rank over `C(delta)`.
This follows from Smith normal form and the triangular leading-jet form of every nonzero
constant-coefficient differential operator. DA normalization terms do not change differential
transcendence degree. This proves (10). `QED`

## Lean formalization of the replication and gluing lemmas

The relative orbit replication lemma and the joint independence of the three face branches are
formalized axiom-clean in `GaloisForLFunctions.DifferentialMatroidGluing` as the abstract theorems
`Rank.freeBlock` and `Rank.crossNeutral_iUnion_indep`. The genuine differential matroid now supplies
the rank, differential automorphisms preserve it, integer orbit heights supply free translates,
and packetwise DA supplies `CrossNeutral`. Thus the remaining special-function inputs are the
actual branch differential independence and off-face packetwise DA theorems. The complete
structural-matroid theorem additionally uses the differential-linear rank lemma. Its nonlinear core
is formalized in `DifferentialOperatorToeplitzRank.lean` as
`differentialIndependent_differentialOperatorRows_iff`: output differential independence is exactly
polynomial operator-row independence. `DifferentialOperatorMatroid.lean` now supplies the missing
dependent-family packaging. It constructs the ordinary row matroid over `Frac(C[delta])` and proves

```text
differentialFamilyMatroid_differentialOperatorRows_eq
```

so the genuine differential-family matroid of every finite operator-output packet equals that row
matroid. The corollaries `differentialOperatorRows_eRk_eq_finrank_span` and
`differentialOperatorRows_matroidRank_eq_finrank_span` identify that rank explicitly with the
`Frac(C[delta])`-dimension of the localized row span for arbitrary dependent families. Thus the
remaining inputs are analytic and special-function-specific: the actual three-branch
differential-independence theorem, the off-face packetwise DA statements, and the hierarchy
identification of the concrete order-two outputs with these operator rows.

## Consequences

### No nonlinear dependence beyond the face ideal

A finite family `P_j(T)F` is differentially algebraically dependent exactly when its operator
classes are linearly dependent over `C(delta)` modulo `I_2`. After clearing denominators, every
dependence is therefore witnessed by a constant-coefficient differential-linear combination landing
in the known squarefree annihilator ideal. Nonlinear differential polynomials create no additional
dependence locus.

### Exact matroid of structural translates

For exponent vectors `n^(1),...,n^(m) in Z^3`,

```text
dtrdeg(T^(n^(1))F,...,T^(n^(m))F)
```

is the ordinary linear rank of the Laurent monomials `t^(n^(j))` in `C[t_0^(+-1),t_1^(+-1),t_2^(+-1)]/I_2`.

For example, the four vertices

```text
F, T_0F, T_1F, T_0T_1F
```

have differential transcendence degree `3`, not `4`, because their only dependence is the DA square
face

```text
(T_0-1)(T_1-1)F=Psi_0,
```

while every three corresponding quotient classes are independent. The theorem asserts that no
additional nonlinear differential relation lowers this degree further.

### Multiplicative order-two elliptic-gamma products

For `E_j in Z[t_0^(+-1),t_1^(+-1),t_2^(+-1)]`, define

```text
G_(2,E_j)(z)=product_n G_2(z+n_0tau_0+n_1tau_1+n_2tau_2)^(c_(j,n)).
```

Then

```text
dtrdeg(G_(2,E_1),...,G_(2,E_m))
  = dim_C span{Ebar_1,...,Ebar_m}                           (11)
```

in the complex vector space `C[t_0^(+-1),t_1^(+-1),t_2^(+-1)]/I_2`.

The lower bound follows because the logarithmic derivatives are `E_j(T)F` and (10) computes their
rank. For the upper bound, the integral quotient module is torsion-free with basis consisting of
`1` and the one-direction augmentation monomials. Hence complex linear relations among integral
classes have a rational basis. Choose a basis among the displayed integral classes. For every
remaining class, clear denominators in its rational expression modulo `I_2`; the corresponding
integer power of `G_(2,E_j)` differs from an integer monomial in the basis products by a DA
function. Thus `G_(2,E_j)` is algebraic over the differential field generated by the basis products
and DA functions. Only the displayed rank many products can contribute differential
transcendence.

## What this does not prove

1. The theorem concerns the structural parameter-translation module generated by `Psi_2`. The full
   universal class `Q_3/DA isomorphic to Comp_3` allows arbitrary complex-support face divisors and
   is larger.
2. Arbitrary complex translations of `Psi_2` are not classified here.
3. The theorem inherits the order-one atomic theorem. The exact annihilator alone is insufficient;
   the proof uses full differential independence of every order-one external orbit.
4. The order-`r>=3` structural module has genuine multi-direction faces of support up to `r-1`.
   Extending the replication and long-interval argument requires a face-filtration induction, not a
   formal repetition of the order-two proof.

## Novelty and parent-theory attack

The relative replication lemma is elementary differential-transcendence bookkeeping once an entire
independent orbit and DA-stability are given. Smith normal form is standard. The nonroutine content
is their interaction with the multiple elliptic-gamma hierarchy:

- the squarefree ideal supplies three branches rather than a free regular orbit;
- each missing parameter produces an external atomic orbit on one lower face while acting
  DA-trivially on the other faces;
- a long structural translation proves that the order-two primitive contributes one additional
  differential dimension beyond every finite face field.

Hardouin's 2008 diagonal-system theorem and Ogawara's results for classical Vigneras multiple gamma
functions are serious parent threats. Hardouin gives criteria for algebraic independence of all
derivatives of solutions of diagonal one-operator difference systems, reducing the question to
linear algebra on divisors of a torus or elliptic curve. That is a genuine parent for the principle
that linear divisor data can control nonlinear differential dependence, but it does not treat the
nondiagonal squarefree hierarchy with three commuting structural translations.

Ogawara's Proposition 4.1 and Corollary 4.2 prove algebraic independence of the classical Vigneras
functions `G_2,G_3,...` together with every derivative of the Euler gamma function under the one
common shift `z -> z+1`. They neither compute differential transcendence degrees of structural
translate families nor classify their differential-algebraic relations by a Stanley--Reisner
module. Kato proves DA for rational multiple-elliptic-gamma period tuples and states explicitly that
the non-rational DA/HT question is unknown; no translate-family matroid appears there.

Exact, stronger, equivalent, and mechanism searches through 2026 located no theorem asserting
(10), (11), the relative-orbit replication lemma in this squarefree face setting, or the claim that
the known face ideal generates every nonlinear differential relation. The abstract slogan has
strong parents; the concrete order-two module theorem was not located. The priority verdict is
therefore provisionally positive, not certified.

## Significance gate

Conditional on the order-one parent, the theorem upgrades the known classification in a way that
cannot be read from the annihilator alone. It determines the differential transcendence degree of
every finite family, proves that all dependence is generated by the squarefree face constraints,
and supplies the first higher-order case where the constraint complex itself is shown to be the
complete nonlinear differential invariant.

## Gates

- [x] 0 -> 1: exact family-matroid target and face-branch decomposition isolated
- [x] relative orbit replication lemma proved
- [x] joint independence of all finite face-branch families proved
- [x] order-two primitive independence proved by a long-interval translation
- [x] unique squarefree module decomposition proved
- [x] complete additive structural differential matroid proved
- [x] multiplicative finite-product matroid derived
- [x] arbitrary dependent operator-row matroid and rank law formalized unconditionally in Lean
- [ ] independent proof audit
- [x] exact/stronger/equivalent literature audit completed provisionally through 2026
- [ ] independent audit of the order-one atomic parent
- [ ] 2 -> 3: formalization only after the analytic parent is formalized

## Log

- 2026-07-10 -- Rejected the insufficient one-step isolation argument and replaced it by replicated
  orbit blocks over DA-stable face fields.
- 2026-07-10 -- Proved joint independence of the three order-one face branches.
- 2026-07-10 -- Used a long structural translation to expose an intermediate face-orbit coordinate
  and prove independence of the order-two primitive.
- 2026-07-10 -- Computed the full nonlinear differential matroid of the squarefree structural module
  and its multiplicative translate-product companion.
- 2026-07-10 -- Audited Hardouin's diagonal hyperindependence theorem, Ogawara's Vigneras hierarchy,
  and Kato's rational-period theorem; found no equivalent squarefree structural family matroid and
  promoted the result provisionally to candidate new scientific knowledge.
