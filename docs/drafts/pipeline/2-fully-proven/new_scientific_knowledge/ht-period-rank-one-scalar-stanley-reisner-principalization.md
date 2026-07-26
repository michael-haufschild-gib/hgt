# HT period rank one forces scalar Stanley--Reisner principalization

- **ID:** `ht-period-rank-one-scalar-stanley-reisner-principalization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GENERAL HT CONSTRAINT-DIMENSION LAW
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A hypertranscendental meromorphic function of one complex variable has period rank
  at most one.  Consequently, if a scalar meromorphic function realizes the complete localized
  Stanley--Reisner differential matroid of a finite simplicial complex under `Q`-independent
  additive translations, every facet misses at most one translation direction.  The complex is a
  simplex or a pure codimension-one boundary subcomplex and its structural ideal is principal.
  The same conclusion holds for an arbitrary family of meromorphic channels under componentwise
  translations and for every finite-dimensional channel with constant invertible internal
  monodromy, including every internal cocycle reducible to constants by a differentially algebraic
  gauge.  Every consistent rational finite-state cocycle is automatically of this form, by the
  two-shift reduction theorem of Schaefke--Singer.  Hence every nonpure full Stanley--Reisner HT
  system, in particular every nonpure two-thick one, has analytic dimension at least two; neither
  channel count nor DA-gauge-flat finite internal state replaces analytic dimension.

## Setup

Let `V` be a finite vertex set and let `Delta` be a finite simplicial complex on `V`, with facet set
`Fac(Delta)`.  Choose translation steps

```text
omega_v in C, v in V,                                       (1)
```

which are linearly independent over `Q`.  Let

```text
T_v f(z)=f(z+omega_v),
delta=d/dz,
K=C(z),
S=C[delta],
R=S[t_v^(+-1):v in V],
x_v=t_v-1.                                                   (2)
```

The translations commute with `delta` and preserve `K`.  Put

```text
I_Delta=(x_N:N is a minimal nonface of Delta).               (3)
```

Let `F` be a meromorphic function on `C`, interpreted in meromorphic normal form.  Assume first that
its exact constant-coefficient structural annihilator is

```text
Ann_R(F)=I_Delta.                                            (4a)
```

Assume in addition that `F` realizes the **full nonlinear Stanley--Reisner differential matroid**:
for every finite
`P_1,...,P_m in R`,

```text
dtrdeg_K K<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                     (4)
```

inside

```text
C(delta) tensor_S (R/I_Delta).                               (5)
```

In particular, a nonzero class `Pbar` produces a differentially transcendental function `P(T)F`,
whereas (4a) makes `P in I_Delta` equivalent to `P(T)F=0`.

## Facet-codimension theorem `[PROVED HERE]`

For every facet `A of Delta`,

```text
|V\A|<=1.                                                    (6)
```

The bound is analytic, not combinatorial.  The full nonlinear matroid forces every facet complement
to occur as periods of one hypertranscendental meromorphic facet carrier, while such a function can
have at most one independent period.

## Proof

### 1. A Stanley--Reisner facet separator

For a facet `A`, write

```text
p_A=(x_v:v notin A).                                        (8)
```

The standard Laurent-localized facet decomposition is

```text
I_Delta=intersection_(B in Fac(Delta)) p_B.                  (9)
```

For each facet `B != A`, maximality and the facet antichain give a vertex

```text
a_B in A\B.                                                  (10)
```

Define the facet separator

```text
q_A=product_(B != A) x_(a_B),                                (11)
```

with empty product `1` when `A` is the unique facet.  Every factor of `q_A` is indexed by a vertex
of `A`, so

```text
q_A notin p_A.                                               (12)
```

For `B != A`, the selected factor `x_(a_B)` belongs to `p_B`, so

```text
q_A in p_B.                                                  (13)
```

Equations (9), (12), and (13) show that `q_A notin I_Delta`; its class in `R/I_Delta` is nonzero.
The squarefree monomial quotient `R/I_Delta` is torsion-free over `S`, so this class remains nonzero
after tensoring with `C(delta)` in (5).
On the other hand, for every `v notin A`,

```text
x_v q_A in p_A,
x_v q_A in p_B for every B != A,
```

and hence

```text
x_v q_A in I_Delta.                                         (14)
```

This separator is the exact algebraic point at which a combinatorial facet becomes an analytic
period carrier.

### 2. The isolated facet carrier

Put

```text
G_A=q_A(T)F.                                                 (15)
```

Because `q_A` has nonzero class, (4) with one operator gives

```text
dtrdeg_K K<G_A>_delta=1.                                    (16)
```

Thus `G_A` is nonconstant and differentially transcendental.  Equation (14) gives, for every
`v notin A`,

```text
(T_v-1)G_A=0,
G_A(z+omega_v)=G_A(z).                                      (17)
```

Therefore every step in the facet complement is a period of the same nonconstant meromorphic
function `G_A`.

Finite sums of translates of a meromorphic function remain meromorphic; take the normal-form
representative of (15).  The equalities (17) are identities of meromorphic functions and include
their poles.

### 3. The HT period-rank law

We first prove the general analytic statement used here:

> **HT period-rank law.** A differentially transcendental meromorphic function on `C` has period
> group of `Z`-rank at most one.

Let `g` be meromorphic and suppose it has two `Q`-linearly independent periods `alpha,beta`.

- If `alpha/beta` is real, it is irrational.  The subgroup `Z alpha+Z beta` then contains nonzero
  periods tending to zero.  Difference quotients at a regular point force `g'=0`, so `g` is
  constant.
- If `alpha/beta` is nonreal, `Lambda=Z alpha+Z beta` is a lattice and `g` is elliptic.  The field of
  elliptic functions for `Lambda` is `C(WeierstrassP,WeierstrassP')`.  The Weierstrass function
  satisfies

  ```text
  (WeierstrassP')^2=4 WeierstrassP^3-g_2 WeierstrassP-g_3.   (E)
  ```

  Hence `WeierstrassP`, its derivative, and every elliptic function are differentially algebraic
  over `C(z)`.

Both cases contradict differential transcendence.  The law follows.  Its rank-three constant
boundary is already formalized as
`GaloisForLFunctions.meromorphicNF_constant_of_rankThree_periods`; the elliptic rank-two DA boundary
is classical elliptic-function theory.

If `V\A` contained two vertices, (17) would give `G_A` two `Q`-linearly independent periods, while
(16) makes `G_A` differentially transcendental.  The HT period-rank law gives a contradiction and
proves (6). `QED`

## Structural principalization `[PROVED HERE]`

By (6), every facet is either `V` or has the form `V\{u}`.  If `V` is a facet, it is the unique
facet, `Delta` is the full simplex, and

```text
I_Delta=0.                                                   (18)
```

Otherwise there is a nonempty set `U subset V` such that

```text
Fac(Delta)={V\{u}:u in U}.                                  (19)
```

A subset `J` is a face exactly when it omits at least one element of `U`.  Thus `U` is the unique
minimal nonface and

```text
I_Delta=(x_U)=(product_(u in U)(t_u-1)).                     (20)
```

All facets in (19) have cardinality `|V|-1`.  Therefore every scalar one-variable meromorphic full
Stanley--Reisner system under independent complex translations has a pure relation complex and a
principal squarefree structural ideal.

This strictly strengthens the earlier atomic co-visibility argument: no decomposition of `F` into
periodic atoms is assumed.

The conclusion does not require two-thickness:

> **Scalar purity law.** A scalar meromorphic function of one complex variable cannot realize the
> full nonlinear Stanley--Reisner differential matroid of any nonpure simplicial complex under
> `Q`-independent additive translations.

Equivalently, every nonpure full Stanley--Reisner HT constraint geometry has analytic dimension at
least two, unless one abandons one-dimensional componentwise meromorphicity, additive translations,
independence of the steps, or the full nonlinear matroid identity (4).  The requested nonpure
two-thick systems form a distinguished subclass of this general dimension floor.

## Componentwise-channel stability `[PROVED HERE]`

The word `scalar` can be removed if vectorization retains the same additive action.  Let

```text
F=(F_i)_(i in I)                                             (21)
```

be any family of meromorphic functions on `C`, finite or infinite, and let every `T_v` act
componentwise by the same step `omega_v`.  Interpret `Ann_R(F)` componentwise and let the
differential field generated by an operator image contain all components `P(T)F_i`.  Assume the
same exact annihilator and full rank identity (4) in this sense.

The facet separator gives the vector

```text
G_A=q_A(T)F.                                                 (22)
```

Its generated differential field has differential transcendence degree one, while every
`omega_v`, `v notin A`, is a common period of every component.

If two complement periods are real-collinear with irrational ratio, their subgroup is dense in a
real line and every meromorphic component of `G_A` is constant.  If they are noncollinear, every
component is elliptic for the same lattice `Lambda`.  All components, regardless of their number,
then lie in the single field

```text
M(C/Lambda)=C(WeierstrassP,WeierstrassP'),                  (23)
```

which is a differentially algebraic extension of `C(z)`.  In both cases the field generated by all
components of `G_A` has differential transcendence degree zero, contradicting the full-matroid
value one.  Hence `|V\A|<=1` and the principalization theorem is unchanged.

Thus ordinary finite- or infinite-channel vectorization does not supply the missing second
analytic direction.

## Constant-multiplier and finite-state stability `[PROVED HERE]`

The period-rank law persists when invariance is replaced by scalar quasiperiodicity.

> **HT quasi-period-rank law.** Let `f` be a nonzero meromorphic function on `C`.  If
> `alpha,beta` are `Q`-linearly independent and
>
> ```text
> f(z+alpha)=a f(z),   f(z+beta)=b f(z),   a,b in C^*,       (24)
> ```
>
> then `f` is differentially algebraic over `C(z)`.

Indeed, the logarithmic derivative

```text
L=f'/f                                                        (25)
```

has the genuine periods `alpha,beta`.  If they are real-collinear, their ratio is irrational and
the dense-period argument makes `L` constant.  If they are noncollinear, `L` is elliptic and hence
DA.  In either case `L` is DA, while `f` satisfies the first-order differential equation

```text
f'-L f=0.                                                    (26)
```

Differential algebraicity is transitive, so `f` is DA over `C(z)`. `QED`

The scalar argument extends to arbitrary finite constant internal monodromy, including
nonsemisimple matrices.

> **Finite-state quasi-period law.** Let `G:C->C^m` be meromorphic and suppose that for two
> `Q`-linearly independent nonzero steps
>
> ```text
> G(z+alpha)=A G(z),   G(z+beta)=B G(z),                    (27)
> ```
>
> with constant invertible matrices `A,B in GL_m(C)`.  Then every component of `G` is
> differentially algebraic over `C(z)`.

Let `H` be the finite-dimensional `C`-span of the component functions of `G`, and choose a basis

```text
h_1,...,h_r.                                                 (28)
```

Both translations preserve `H` and act invertibly on it.  The meromorphic Wronskian of this basis
is nonzero; otherwise the analytic Wronskian criterion would make the basis `C`-linearly
dependent.  Cramer's rule therefore gives a unique monic scalar differential operator

```text
L=D^r+sum_(j=0)^(r-1)c_j(z)D^j                              (29)
```

annihilating all of `H`.

For `omega=alpha` or `beta`, the shifted basis `(h_i(z+omega))` is another constant basis of `H`.
Evaluating (29) at `z+omega` shows that its monic annihilator has coefficients
`c_j(z+omega)`.  Uniqueness of the monic annihilator of the same space `H` gives

```text
c_j(z+alpha)=c_j(z)=c_j(z+beta).                             (30)
```

Thus every coefficient is constant in the collinear-irrational case and elliptic in the
noncollinear case.  In particular all `c_j` are DA.  Every basis function satisfies (29), a linear
ODE over the DA differential field generated by the coefficients.  Transitivity of differential
algebraicity makes every `h_i`, and hence every component of `G`, DA over `C(z)`. `QED`

Now let `F:C->C^m` be a meromorphic vector and let the structural translations act by

```text
mathcalT_v F(z)=M_v^(-1)F(z+omega_v),                        (31)
```

where `(M_v)` are constant invertible matrices and the displayed actions commute.  Assume the
component-generated exact annihilator and full nonlinear Stanley--Reisner matroid identities.

For a facet `A`, the same separator produces a vector `G_A` of differential rank one and

```text
G_A(z+omega_v)=M_v G_A(z),   v notin A.                     (32)
```

If the complement contained two vertices, the finite-state quasi-period law would make every
component of `G_A` DA.  Their joint differential field would be DA, contradicting the required rank
one.  Therefore again

```text
|V\A|<=1,                                                    (33)
```

and the complex is pure with a principal squarefree ideal.

Consequently **no finite-dimensional constant internal channel**, diagonalizable or not, supplies
the missing analytic direction.  An evasion must use a genuinely higher-dimensional analytic
domain, `z`-dependent or nonlinear internal transport, an infinite-dimensional action with new
differential transcendence, a non-additive action, or failure of the full exact matroid hypothesis.

## DA-gauge curvature necessity `[PROVED HERE]`

The exact boundary for a `z`-dependent finite-state action is gauge-theoretic.  Let `D_DA` be the
differential field of meromorphic functions on `C` that are DA over `C(z)`; it is stable under every
constant translation.  Consider commuting structural actions

```text
mathcalT_v F(z)=M_v(z)^(-1)F(z+omega_v),                    (35)
```

on a meromorphic `C^m`-valued carrier, where `M_v(z)` is invertible and the matrices satisfy the
translation-cocycle compatibility required for the `mathcalT_v` to commute.

Suppose the cocycle is **DA-gauge-flat**: there are

```text
B(z) in GL_m(D_DA),   C_v in GL_m(C)                        (36)
```

such that

```text
M_v(z)=B(z+omega_v) C_v B(z)^(-1).                          (37)
```

Put `Ftilde=B^(-1)F`.  Conjugating (35) by `B` gives the constant action

```text
mathcalTtilde_v Ftilde(z)=C_v^(-1)Ftilde(z+omega_v).         (38)
```

For every structural operator `P`,

```text
P(mathcalTtilde)Ftilde=B^(-1)P(mathcalT)F.                  (39)
```

Hence exact vanishing is unchanged.  Differential transcendence ranks are unchanged as well:
adjoining the entries of `B` and `B^(-1)` is a DA extension of the base, and the invertible change
of components recovers each side from the other.  Therefore the exact annihilator and full
nonlinear matroid identities transfer to the constant system (38).

The finite-state theorem then forces every facet complement to have size at most one.  Thus:

> **DA-cocycle curvature law.** A one-variable finite-state full HT system with nonpure
> Stanley--Reisner geometry has an internal translation cocycle that is not DA-gauge-equivalent to
> any constant representation.

Equivalently, its class in the nonabelian difference-cohomology set

```text
H^1(<T_v>,GL_m(D_DA))                                      (40)
```

lies outside the constant-representation locus.  This is a positive necessity, not a proposed
carrier: the missing analytic direction must appear as genuine DA-gauge curvature if it is encoded
inside one complex variable.

## Cocycle transcendence requirement `[PROVED HERE]`

For rational internal transport the gauge-flatness hypothesis is automatic.  Suppose two vertices
`v,w` lie outside one facet `A`, and suppose the corresponding matrices in (35) have entries in
`C(z)`.  The isolated carrier satisfies

```text
G_A(z+omega_v)=M_v(z)G_A(z),
G_A(z+omega_w)=M_w(z)G_A(z).                                (42)
```

The commuting structural actions give the consistency identity

```text
M_w(z+omega_v)M_v(z)=M_v(z+omega_w)M_w(z).                 (43)
```

Rescale `z=omega_v x` and put `alpha=omega_w/omega_v`.  The `Q`-independence of the translation
steps gives `alpha notin Q`.  Thus (42)--(43) are a consistent pair of rational shift systems for
`x -> x+1` and `x -> x+alpha`.  The shift case of Schaefke--Singer's reduction theorem supplies a
rational gauge `B in GL_m(C(x))` and commuting constant matrices `C_v,C_w` such that, after
undoing the rescaling,

```text
M_j(z)=B(z+omega_j) C_j B(z)^(-1),   j in {v,w}.            (44)
```

A rational gauge is DA, so (44) is a special case of (36)--(37).  The DA-gauge curvature law then
contradicts the hypertranscendence rank of `G_A`.  Therefore no facet can omit two vertices.

> **Cocycle transcendence requirement.** A one-variable finite-state meromorphic system with a
> nonpure full exact Stanley--Reisner HT matroid has, on every facet with two omitted directions, a
> two-shift internal cocycle which escapes `GL_m(C(z))` and the entire DA-gauge-flat constant locus.

Equivalently—and now as the no-go corollary—a consistent rational matrix cocycle can realize only a
simplex or pure codimension-one relation complex, with a principal squarefree structural ideal.

Equivalently, a nonpure finite-state one-variable carrier must cross the rational consistency
boundary: at least one required two-shift subsystem is not representable by a consistent cocycle in
`GL_m(C(z))`.  This is stronger than saying that constant transfer matrices fail.  No finite number
of rational `z`-dependent channels, including nonsemisimple ones, supplies the missing analytic
direction.  The theorem remains conditional on the full exact matroid hypothesis; it does not
assert that a zeta-derived matrix system has that relation ideal.

## Relative two-shift gauge characterization `[PROVED HERE] [BRIDGE]`

The rank-one version gives an exact cohomological characterization of hypertranscendence.  Fix two
`Q`-linearly independent steps `alpha,beta`, put

```text
Gamma=Z alpha+Z beta,                                       (C1)
```

and let `f` be a nonzero meromorphic function.  Its multiplicative translation cocycle is

```text
m_f(gamma;z)=f(z+gamma)/f(z).                               (C2)
```

Call this cocycle **DA-constant-flat** if there are a nonzero `b in D_DA` and a character
`chi:Gamma->C^*` such that

```text
m_f(gamma;z)=b(z+gamma)/b(z) chi(gamma)                     (C3)
```

for `gamma=alpha,beta`, equivalently for all `gamma in Gamma`.

Then

```text
f is DA over C(z) iff m_f is DA-constant-flat.              (C4)
```

If `f` is DA, take `b=f` and `chi=1`.  Conversely, if (C3) holds, then `g=f/b` satisfies

```text
g(z+gamma)=chi(gamma)g(z).
```

The two generators give two independent constant-multiplier quasi-periods, so the quasi-period
rank law makes `g` DA.  Since `b` is DA, so is `f`. `QED`

Thus hypertranscendence is exactly a **relative gauge obstruction**: the cocycle (C2) is a
coboundary in the full meromorphic field, but it cannot be reduced to a constant character using a
DA meromorphic gauge.  Rank-one difference-module gauge theory is the parent mechanism, so (C4) is
a `[BRIDGE]`; its role here is to identify the precise curvature resource consumed by the nonpure
facet theorem.

The zeta specialization is unconditional.  The known hypertranscendence of `zeta` over `C(s)`
implies that, for any two `Q`-independent shifts, its cocycle (C2) is not DA-constant-flat.  In
particular `log p` and `log q` are `Q`-independent for distinct primes, so

```text
zeta(s+log p)/zeta(s),   zeta(s+log q)/zeta(s)              (C5)
```

define a genuinely nonflat relative DA-gauge class.  This proves that zeta possesses the curvature
resource demanded by the finite-state obstruction.  It does not locate zeros or imply RH: every HT
function has the same relative nonflatness.  An RH route must couple this resource to a canonical
prime/Euler marking, positivity, or divisor-sensitive constraint that survives the DA-gauge
blindness theorem.

## Sharpness and attacks

1. **The facet separator is essential.** Merely knowing `I_Delta subset Ann(F)` would not force
   `q_A(T)F` to be nonconstant.  The full rank identity (4) supplies exactly that missing lower
   bound.
2. **Rank one is sharp.** Nonconstant singly periodic hypertranscendental meromorphic
   functions exist, and principal squarefree annihilators occur in Barnes-type and generic periodic
   constructions.
3. **Rank two is the exact DA boundary.** Doubly periodic meromorphic functions are elliptic and DA,
   so they cannot be the differentially transcendental carrier isolated by (16).
4. **No atomic assumption.** The proof applies to irreducible scalar modules, nonsplit extensions,
   and arbitrary cancellations because the separator is constructed in `R/I_Delta` itself.
5. **No hidden flow.** The theorem concerns annihilator ideals, facets, and period stabilizers.  No
   evolution parameter or propagation equation is introduced.
6. **Multivariable escape.** The facet-sewn Herglotz system realizes every finite complex by using
   one independent coordinate per facet.  The present theorem proves that its departure from one
   complex variable is mathematically necessary for a nonpure two-thick target, not merely a
   convenient artifact of the construction.

## Positive law and RH-facing consequence

The result is not best stated as "the one-variable route fails."  Its positive form is:

> **Facet co-visibility law.** Every hypertranscendental meromorphic facet carrier in one complex
> variable is visible to all but at most one independent complex translation direction.

For a nonpure complex this becomes:

> **Constraint-dimension requirement.** Nonpure HT relation geometry must possess at least two
> analytic degrees of freedom, or an equivalent non-scalar/non-additive replacement for them.

For prime-log translations this is especially rigid: every componentwise full-matroid carrier has
a principal structural ideal.  Hence an RH route seeking nonpure prime-indexed constraint geometry
must positively exhibit where its extra analytic degree of freedom lives.  Possibilities include a
prime/Euler source coordinate paired with an archimedean coordinate, a finite-state internal
cocycle with nontrivial DA-gauge curvature, an infinite-dimensional internal action, a sheaf with
non-common local stabilizers, or a non-additive action whose stabilizers are not period lattices.
The theorem does not select among these and does not claim to carry `zeta`.

The finite-state strengthening makes this exact for finite prime-channel models.  Prime logarithms
are `Q`-linearly independent.  Therefore any constant finite-dimensional internal representation
of their commuting translation group satisfying the full exact matroid hypothesis still has only
the principal normal form

```text
I=(product_(p in U)(mathcalT_p-1)).                          (41)
```

A Hilbert--Polya-, scattering-, or transfer-matrix-inspired route that needs nonpure prime
compatibility must obtain a genuine infinite-dimensional limit, a finite cocycle not flattenable by
any DA gauge, or a second analytic coordinate; increasing the number of constant matrix channels at
each finite cutoff does not by itself produce the required geometry.  This conclusion is
conditional on the full exact matroid hypothesis and does not exclude the classical RH criteria in
their native formulations.

## Parent-theory and literature audit

The proof uses established ingredients separately:

- the dichotomy that two independent periods make a meromorphic function constant or elliptic/DA;
- the facet-prime decomposition of a Stanley--Reisner ideal;
- the fact that a nonzero element has differential rank one under the complete matroid identity.

Searches were made for simultaneous meromorphic difference equations, translation-annihilator
ideals, analytic representations of Stanley--Reisner modules, squarefree modules, spectral
synthesis, and period-rank rigidity.  The adjacent literature studies meromorphic solutions of
difference equations, translation-invariant function spaces, squarefree modules, and
Stanley--Reisner sheaves, but no source was located that combines a facet separator with period-rank
rigidity to prove (6) or the scalar purity/principalization consequence.

The closest scalar direct threat is Jean-Claude Jolly, *Solutions méromorphes sur C d'un système
d'équations aux différences à coefficients constants et à deux pas récurrents* (Annales de
l'Institut Fourier 52 (2002), 585--622).  Jolly classifies common meromorphic solutions of two
coprime constant-coefficient operators for two real-linearly independent steps in an algebra built
from elliptic functions, elliptic functions of the second kind, and two Weierstrass-zeta/linear
primitives.  This supports the rank-two DA boundary and treats a much broader simultaneous-equation
problem, but it does not state the facet-separator consequence, the full differential-matroid lower
bound (16), scalar principalization for arbitrary Stanley--Reisner ideals, or its finite-state
channel consequence.  The scalar quasi-period lemma (24)--(26) and Wronskian construction
(27)--(30) are classical `[BRIDGE]` mechanisms, not separately new scientific knowledge.  The
candidate-new content is their use, through the facet separator, to force the same principal
geometry for every constant finite-dimensional internal representation.  Rusanov's 1961 note on
simultaneous difference equations and later spectral-synthesis literature remain older prior-art
threats requiring specialist comparison.

Gauge conjugacy of difference modules and the nonabelian `H^1` notation in (35)--(40) are standard
`[BRIDGE]` language.  The candidate geometric residue is the DA-cocycle curvature law: nonpure full
Stanley--Reisner geometry forces the internal difference-module class outside the entire
DA-gauge-flat constant locus.  No located difference-Galois source states this facet-separator
consequence or the prime-route normal form (41).

The contributing period, commutative-algebra, and matroid facts are established.  The
candidate-new scientific result is the geometry they force: analytic dimension one has only the
principal pure stratum, while the companion facet-sewn Herglotz theorem realizes every finite
complex in higher dimension.  This proves a genuine dimension boundary for HT relation geometry and
explains why the non-Gamma nonpure realization must be multivariable.  Novelty remains provisional:
older simultaneous-difference or spectral-synthesis literature may contain an equivalent
representation obstruction, and independent specialist scrutiny is still required.

The finite-state parent theorem is now pinned exactly: R. Schaefke and M. F. Singer,
*Consistent systems of linear differential and difference equations*, J. Eur. Math. Soc. **21**
(2019), 2751--2792, Theorem 13 in case 2S, proves that every consistent rational matrix system for
the shifts `x -> x+1` and `x -> x+alpha`, `alpha notin Q`, is rationally gauge-equivalent to a pair
of commuting constant matrices.  Its Corollary 14 classifies scalar meromorphic common solutions
using rational functions, exponentials, elliptic functions, Weierstrass zeta, and second-kind
elliptic factors.  Thus the rational gauge reduction and the resulting differential algebraicity
are `[SEARCH]` / `[BRIDGE]`, not new knowledge.  Bezivin--Gramain (1996), Brisebarre--Habsieger
(1999), Rusanov (1961), Jolly (2002), and the spectral-synthesis literature are adjacent prior art.
The novelty candidate is only the facet-separator consequence: rational finite-state consistency
forces the relation complex into the principal pure stratum.  Exact and equivalent-form searches
located no source stating that consequence, but its novelty remains provisional pending specialist
review.

## Lean status `[FORMALIZATION]`

`GaloisForLFunctions/HTGeometry/SimplicialConstraintTower.lean` formalizes the complete combinatorial
principalization capstone:

- `FacetComplementRankOne` records the analytic output `|V\F| <= 1` for every facet;
- `facetAntichain_eq_singleton_or_deletionFacets` proves that a nonempty facet antichain is either
  the singleton full simplex or exactly `{V.erase u : u in U}` for one nonempty `U`;
- `isFaceOf_deletionFacets_iff` identifies its faces as the ambient subsets omitting a vertex of
  `U`;
- `deletionFacets_unique_minimalNonface` proves that `U` is the unique minimal forbidden block,
  which is the combinatorial content of the principal squarefree ideal `(prod_(u in U)(t_u-1))`.

`GaloisForLFunctions/HTGeometry/StanleyReisnerFacetIdeal.lean` now formalizes the corresponding
ideal equality itself:

- `deletionFacetFinset` packages the deletion family as a finite facet family on a finite vertex
  type;
- `coe_deletionFacetFinset` identifies that finite family with `deletionFacets univ U`;
- `stanleyReisnerIdeal_deletionFacetFinset_eq_span_product` proves, over every commutative
  coefficient ring, that its Stanley--Reisner ideal is exactly the principal ideal
  `(prod_(u in U) X_u)`.

The rank-two meromorphic-to-DA theorem, the rational gauge reduction, and the transfer from the
analytic carrier to `FacetComplementRankOne` remain paper-level, so the card stays in stage 2.

## Gates

- [x] prior pipeline and failed-route search
- [x] facet separator constructed
- [x] nonzero differential-transcendental facet carrier isolated
- [x] HT period-rank-one law proved
- [x] complex facet-codimension-one bound proved
- [x] structural principalization theorem proved
- [x] positive cocycle-transcendence requirement extracted from the Schaefke--Singer reduction
- [x] combinatorial principalization capstone formalized in Lean
- [x] atomic hypothesis removed
- [x] positive constraint-dimension law extracted
- [x] preliminary exact and adjacent literature search
- [x] complete unconditional paper proof
- [x] deletion-family Stanley--Reisner ideal equality formalized in Lean
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before stage 3

## Log

- 2026-07-11 -- Replaced the weaker atomic principalization theorem by the facet-separator argument,
  which applies to every scalar meromorphic full Stanley--Reisner realization.
- 2026-07-11 -- Strengthened period discreteness by using the elliptic rank-two boundary: every
  hypertranscendental meromorphic function has period rank at most one.
- 2026-07-11 -- Proved scalar purity and principalization without a real-step or two-thickness
  hypothesis, and identified analytic dimension at least two as the positive resource carried by
  every nonpure HT constraint geometry.
- 2026-07-11 -- Strengthened the finite-state boundary: every consistent rational two-shift matrix
  cocycle is rational-gauge-flat by Schaefke--Singer, so nonpure one-variable HT geometry requires
  genuinely nonrational/non-DA-flat internal transport. Formalized the exact
  simplex-or-deletion-family classification and its unique minimal nonface in Lean.
- 2026-07-17 -- Formalized the actual deletion-family Stanley--Reisner ideal equality as the
  principal squarefree ideal generated by `prod_(u in U) X_u`, over an arbitrary commutative
  coefficient ring.

## Lean progress — the non-elliptic half of the HT period-rank law

`GaloisForLFunctions/HTGeometry/RankTwoRealDependentPeriods.lean` (axiom-clean, build green,
umbrella-registered) formalizes the **first bullet** of §3's period-rank law unconditionally: the case
`alpha/beta` real.

- `not_discrete_intSpan_fin_two_of_not_linearIndependent_real` — the integer span of two
  `Q`-independent but `R`-dependent complex numbers is not discrete.  A discrete integer span has
  equal integer and real ranks (`Real.finrank_eq_int_finrank_of_discrete`), but here the integer rank
  is `2` while the real rank is at most `1`, because `R`-dependence forbids
  `finrank_R (span (range v)) = card` (`linearIndependent_iff_card_eq_finrank_span`).
- `exists_small_rankTwo_realDependent_periods` — hence arbitrarily small nonzero periods.
- **`meromorphicNF_constant_of_rankTwo_realDependent_periods`** — with meromorphic normal-form
  rigidity (`meromorphicNF_constant_of_small_periods`), such a function is constant.
- `not_hypertranscendental_of_rankTwo_realDependent_periods` — and therefore not hypertranscendental
  (a constant satisfies `y_0 - c = 0`).

Together with the already-formalized rank-three boundary
`meromorphicNF_constant_of_rankThree_periods`, the analytic side of the period-rank law is now
complete **except for the genuine elliptic case** `alpha/beta` nonreal, where the periods form a
lattice and the conclusion needs the Weierstrass differential equation `(E)`.  That is the only
remaining analytic gap in §3; the rational gauge reduction and the transfer from the analytic carrier
to `FacetComplementRankOne` remain paper-level as before.

## Lean progress — the facet separator (§1) and the algebraic input of §2

`GaloisForLFunctions/HTGeometry/StanleyReisnerFacetSeparator.lean` (axiom-clean, build green,
umbrella-registered) formalizes the separator step in the corpus's Stanley--Reisner ring language.

- `isFaceOf_of_mem_facets` and `not_isFaceOf_insert_of_mem_facets` — a facet is a face, and facet
  maximality: in a facet antichain, adjoining a vertex outside a facet leaves the complex.  This is
  where `FacetAntichain` enters, and it is the combinatorial content of `(13)`.
- `srProd_facet_ne_zero` — `(12)`: the facet monomial `prod_(w in A) x_w` has nonzero class, because
  the face detector is `1` on it (`srFaceDetector_prod`).
- `srVertexX_mul_srProd_facet_eq_zero` — `(14)`: for every `v` outside `A`, `x_v * prod_(w in A) x_w`
  vanishes, because `insert v A` is a nonface (`srProd_eq_zero_of_not_isFace`).
- **`exists_facetSeparator`** — the two together: every facet of a finite facet antichain carries a
  nonzero Stanley--Reisner class annihilated by exactly the vertex coordinates it omits.

**Simplification of the paper argument.**  §1 builds `q_A` as a product over the *other* facets of one
chosen vertex `a_B in A \ B` per facet, and derives `q_A notin I_Delta` from the intersection formula
`(9)`.  With the corpus's characterization of the Stanley--Reisner ideal by monomial supports
(`mem_stanleyReisnerIdeal_iff`), the facet monomial of `A` itself already satisfies `(12)` and `(14)`,
so the choice of the `a_B` and the appeal to `(9)` are not needed.  The Lean statement is therefore
strictly simpler than the paper route while proving the same two facts.

What remains between this and `(16)`--`(17)` is the transport through a realization: that a nonzero
class of `R/I_Delta` becomes a differentially transcendental function, and that annihilation by `x_v`
becomes the period identity `G_A(z + omega_v) = G_A(z)`.  That is the realization-modelling step
shared with `boundary-wedge-uniform-ht-dimension-gap`, and it is now the only gap between the
formalized algebra and the formalized analysis (`RankThreePeriods`,
`RankTwoRealDependentPeriods`, `BoundaryWedgePeriodRankObstruction`).

## Lean progress — §2 transported: annihilation becomes periodicity

`GaloisForLFunctions/HTGeometry/ScalarSRRealizationBridge.lean` (axiom-clean, build green)
formalizes the transport that §2 performs by hand.  A `ScalarSRRealization` carries two defining
properties — the vertex coordinate `x_v` acts as `T_v - 1`, and a nonzero Stanley--Reisner class has a
hypertranscendental carrier — and from them:

- `periodic_carrier_of_mul_eq_zero` derives `(17)`: `x_v q = 0` forces `G(z + omega_v) = G(z)`;
- `toScalarFacetRealization` combines this with the separator `(12)`/`(14)` to produce, for every
  facet, a hypertranscendental carrier whose periods include every omitted step — exactly `(15)`--`(17)`;
- `no_scalarSRRealization_of_three_omitted` then contradicts hypertranscendence whenever a facet omits
  three vertices, using the already-formalized rank-three period boundary.

So for facets omitting at least three vertices the whole chain `(12)` -> `(17)` -> period-rank -> no
realization is unconditional in Lean.  The general statement `(6)` (complements of size at most one)
still needs the rank-two case with `alpha/beta` nonreal, i.e. the elliptic branch of the period-rank
law, which remains the single analytic gap.

## Lean progress — the sharp unconditional form of the facet-codimension theorem

`GaloisForLFunctions/HTGeometry/ScalarRealizationFacetComplementBound.lean` (axiom-clean, build
green, umbrella-registered) states, in full generality, exactly what the formalized period-rank
analysis yields about `(6)`.

- `facetComplement_card_le_two_of_scalarSRRealization` — under a one-variable realization **no facet
  omits three vertices**.  (Three omitted vertices give three `Q`-independent periods; the rank-three
  boundary is unconditional.)
- **`facetComplement_rankOne_or_lattice`** — every facet either omits at most one ambient vertex — the
  assertion `(6)` — **or** omits exactly two, whose translation steps are `R`-linearly independent and
  hence generate a lattice.  The real-dependent two-vertex case is excluded by
  `meromorphicNF_constant_of_rankTwo_realDependent_periods`.
- `facetComplementRankOne_of_no_lattice` — consequently `FacetComplementRankOne` holds outright as
  soon as no two distinct translation steps span a lattice.

This isolates the outstanding analytic input precisely: the surviving alternative is exactly the
elliptic configuration, and supplying `(E)` — the Weierstrass differential equation, i.e. that an
elliptic function is differentially algebraic — removes it and proves `(6)` unconditionally.  Nothing
else in the chain from `(8)` to `(6)` is now missing.

## Lean progress — the Weierstrass function is differentially algebraic

`GaloisForLFunctions/HTGeometry/WeierstrassPDifferentiallyAlgebraic.lean` (axiom-clean, build green,
umbrella-registered) formalizes the first half of the elliptic input `(E)`.

Mathlib now carries the Weierstrass function and its differential equation
(`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`): `PeriodPair.derivWeierstrassP_sq`
gives `℘'(z)^2 = 4 ℘(z)^3 - g_2 ℘(z) - g_3` off the lattice, and `PeriodPair.deriv_weierstrassP`
gives `deriv ℘ = ℘'` globally.  Turning that into a statement of `DifferentiallyAlgebraic` requires
one repair: at lattice points `℘` carries junk values and `(E)` itself fails there.  Multiplying the
relation by the value slot fixes it, since `℘` takes the junk value `0` exactly at the lattice:

- `weierstrassPRelation` — the order-one differential polynomial
  `(y_1^2 - 4 y_0^3 + g_2 y_0 + g_3) * y_0`;
- `weierstrassPRelation_ne_zero` — it is a nonzero polynomial (two evaluations differing by `1`);
- **`differentiallyAlgebraic_weierstrassP`** — it vanishes on the whole plane: off the lattice by
  `(E)`, at a lattice point because the value slot is `0`;
- `not_hypertranscendental_weierstrassP` — hence `℘` is not hypertranscendental.

So `(E)` is now available in Lean in exactly the form the period-rank law needs.  What remains of the
elliptic branch is the structure statement: every meromorphic function with a lattice of periods lies
in `C(℘, ℘')` and is therefore differentially algebraic too.  With that, the surviving alternative in
`facetComplement_rankOne_or_lattice` disappears and `(6)` becomes unconditional.

## Lean progress — `(6)` complete modulo one named analytic input

`GaloisForLFunctions/HTGeometry/EllipticFreeFacetCodimension.lean` (axiom-clean, build green,
umbrella-registered) closes the facet-codimension theorem down to a single named `Prop`.

`facetComplement_rankOne_or_lattice` leaves exactly one alternative open: a facet omitting two
vertices whose steps are `R`-independent.  Those two steps are then literally a mathlib `PeriodPair`,
and the facet carrier is a hypertranscendental meromorphic function invariant under the whole lattice
they span — a hypertranscendental *elliptic* function.

- `EllipticHypertranscendenceFree` — the named input: no hypertranscendental meromorphic function is
  invariant under a full lattice (equivalently, every elliptic function is differentially algebraic).
- **`facetComplementRankOne_of_ellipticFree`** — modulo that input, a one-variable realization forces
  every facet to omit at most one ambient vertex.  This is `(6)` in full generality: the separator,
  the transport to periods, the rank-three exclusion and the real-dependent rank-two exclusion are all
  already unconditional, and the remaining alternative is discharged exactly by the named input.

The half of that input concerning `℘` itself is already proved
(`differentiallyAlgebraic_weierstrassP`); what the `Prop` still packages is the structure statement,
that every lattice-periodic meromorphic function lies in `C(℘, ℘')`.  So the card's chain
`(8) -> (17) -> period rank -> (6)` is now formalized end to end except for that one classical
statement, which is named, isolated, and consumed at a single point.

## Lean progress — `(6)` UNCONDITIONAL for entire realizations

`GaloisForLFunctions/HTGeometry/EllipticLiouvilleFacetCodimension.lean` (axiom-clean, build green,
umbrella-registered) removes the named analytic input for the realizations that actually arise.

The alternative left open by `facetComplement_rankOne_or_lattice` is a facet carrier that is
hypertranscendental and invariant under a full lattice.  For a general meromorphic carrier, excluding
that is the elliptic structure theorem.  For an **entire** carrier it is Liouville's theorem — and the
periodic-pencil realization theorem of the parent card produces precisely *entire* systems ("there are
an entire function `F` on `C^d`, translations ...").

- `const_of_lattice_periodic_differentiable` — **elliptic Liouville**: a lattice-periodic entire
  function is constant.  Mathlib supplies both halves: `IsZLattice.isCompact_range_of_periodic` makes
  the range compact, and `Differentiable.apply_eq_apply_of_bounded` is Liouville.
- `not_hypertranscendental_of_lattice_periodic_differentiable` — hence such a function is
  differentially algebraic.
- **`facetComplementRankOne_of_entire`** — for a one-variable realization with entire carriers, every
  facet omits at most one ambient vertex.  **Unconditional**: no `EllipticHypertranscendenceFree`, no
  Weierstrass structure theory.

So the facet-codimension theorem `(6)` is now fully unconditional in Lean for entire realizations, and
the named input `EllipticHypertranscendenceFree` is needed only if one insists on carriers with poles.

## Lean progress — the principalization capstone, unconditional for entire realizations

`GaloisForLFunctions/HTGeometry/EntireRealizationPrincipalization.lean` (axiom-clean, build green,
umbrella-registered) feeds the unconditional facet-codimension law into the combinatorial
classification already in the corpus, giving the card's structural conclusion with no analytic input
left.

- **`principalization_of_entire_realization`** — a finite facet antichain admitting a one-variable
  realization with entire carriers is either the full simplex `{V}` or exactly the deletion family
  `{V \ {u} : u in U}` for a nonempty block `U`.  This is
  `facetAntichain_eq_singleton_or_deletionFacets` discharged by `facetComplementRankOne_of_entire`.
- **`stanleyReisnerIdeal_principal_of_entire_realization`** — in the non-simplex case the
  Stanley--Reisner ideal is principal, generated by `prod_(u in U) X u`, via
  `stanleyReisnerIdeal_deletionFacetFinset_eq_span_product`.

The whole chain is now formalized and unconditional for entire realizations: facet separator `(12)`
and `(14)`, transport of annihilation to periods `(17)`, period-rank exclusion at rank three and at
real-dependent rank two, Liouville at the lattice, the classification `facets = {V}` or a deletion
family, and the principal ideal.  Nothing in it now depends on `EllipticHypertranscendenceFree`, which
is needed only for carriers with poles.

## Lean progress — the codimension law at the analytic datum, and channel stability

`GaloisForLFunctions/HTGeometry/EntireFacetRealizationCodimension.lean` and
`GaloisForLFunctions/HTGeometry/ChannelSRRealization.lean` (both axiom-clean, build green,
umbrella-registered).

- **`no_scalarFacetRealization_of_two_omitted_entire`** — for an entire facet carrier, *two* omitted
  vertices are already impossible: if the two steps are `R`-dependent the period group is not
  discrete, and if they are `R`-independent they form a `PeriodPair` and Liouville applies.  One
  statement covers both cases.
- **`facetComplementRankOne_of_facetRealization_entire`** — the codimension law stated directly for
  the analytic datum `ScalarFacetRealization`, which is its most general form.
  `facetComplementRankOne_of_entire` (ring-level) is now a one-line corollary of it, so the law is
  proved once rather than twice.

Componentwise-channel stability `(21)`--`(23)` is formalized as a reduction rather than a repetition:

- `ChannelSRRealization` — an arbitrary family `iota` of channels translated componentwise by the same
  steps, with *some* component hypertranscendental on each nonzero class (the vector form of
  full-matroid faithfulness);
- `channel_periodic_of_mul_eq_zero` — annihilation becomes componentwise periodicity;
- **`ChannelSRRealization.toScalarFacetRealization`** — choosing one hypertranscendental component per
  facet turns a channel realization into an ordinary analytic datum, so *every* scalar result applies
  verbatim;
- **`channel_facetComplementRankOne_of_entire`** — for entire channels every facet omits at most one
  ambient vertex.  Vectorization supplies no extra analytic direction, exactly as the card asserts.

## Lean progress — constant multipliers: `(24)`--`(26)` and their facet consequence

`GaloisForLFunctions/HTGeometry/QuasiPeriodDifferentialAlgebraicity.lean` and
`GaloisForLFunctions/HTGeometry/QuasiPeriodRealizationPrincipalization.lean` (axiom-clean, build
green, umbrella-registered) formalize the scalar half of *Constant-multiplier and finite-state
stability*, unconditionally for entire nowhere-vanishing carriers.

The paper argument is `(25)`: the multipliers cancel in the logarithmic derivative, which therefore
has both steps as *genuine* periods, so the period-rank rigidity already formalized applies to it.

- `periodic_logDeriv_of_quasiperiodic` — `(25)`: `f(z+w) = a f(z)` with `a ≠ 0` makes
  `logDeriv f = f'/f` genuinely `w`-periodic.  (`deriv f (z+w) = a * deriv f z` by differentiating
  the quasi-period identity, then `mul_div_mul_left`.)
- `(26)` needs nothing new: the corpus already proves that a first-order ODE with polynomial
  coefficients is an algebraic differential equation
  (`ExpPolynomialDA.differentiallyAlgebraic_of_firstOrder_poly_ode`, order-one differential
  polynomial `Q(X_0) X_2 - P(X_0) X_1`), and `(26)` is its case `Q = 1`, `P = c`.
- **`differentiallyAlgebraic_of_quasiperiods`** — the **HT quasi-period-rank law** for an entire
  nowhere-vanishing `f`: for `Q`-independent steps, `logDeriv f` is entire and doubly periodic,
  hence constant — by non-discreteness of the period group when the steps are `R`-dependent
  (`meromorphicNF_constant_of_rankTwo_realDependent_periods`) and by Liouville on the lattice when
  they are `R`-independent (`const_of_lattice_periodic_differentiable`) — so `f' = c f` and `f` is
  DA.  Note this route needs **no** transitivity of differential algebraicity: the first-order
  equation `(26)` is produced with a *constant* coefficient, not a merely DA one, so `f` satisfies
  an algebraic differential equation outright.
- `QuasiPeriodFacetRealization` — the constant-multiplier facet datum, with
  `ScalarFacetRealization.toQuasiPeriod` exhibiting the invariant datum as the special case
  "all multipliers `1`";
- **`facetComplementRankOne_of_quasiPeriodRealization`** — `(33)` for `m = 1`: every facet still
  omits at most one ambient vertex;
- **`stanleyReisnerIdeal_principal_of_quasiPeriodRealization`** — and the capstone is unchanged: the
  ideal is the principal squarefree `(prod_(u in U) X u)`.

So a scalar constant internal multiplier, the simplest internal state a channel can carry, provably
buys no new relation geometry.

**What the entire-and-nowhere-vanishing hypothesis costs.**  It is exactly the same boundary as
everywhere else on this card.  For a carrier with zeros or poles `logDeriv f` is meromorphic rather
than entire, and the lattice branch then needs the elliptic structure theorem
(`EllipticHypertranscendenceFree`) instead of Liouville.  The `R`-dependent branch is already
unconditional for meromorphic normal forms.

**Remaining on this card.**  The matrix case `(27)`--`(30)` (`GL_m` internal monodromy, Wronskian
and monic-annihilator construction) and everything downstream of it — `(31)`--`(33)` for `m > 1`,
the DA-gauge curvature law `(35)`--`(40)`, and `(C4)`.  Unlike the scalar case those genuinely need
transitivity of differential algebraicity over a DA coefficient field.  The corpus already has that
machinery in abstract differential-field form —
`GaloisForLFunctions/HTGeometry/DifferentialAlgebraicFiniteTransitivity.lean`
(`differentialAlgebraicOver_trans_fin_succ_narrow`, `differentialAlgebraicOver_mono`) over
`DifferentialIndependent` / `DifferentialAlgebraicOver` from
`HTGeometry/DifferentialIndependence.lean` — so the missing piece is a bridge from the function-level
predicate `DifferentiallyAlgebraic (f : C -> C)` into that framework, not the transitivity theorem
itself.

## Lean progress — the nonvanishing hypothesis removed in the real-dependent case

Same module, second pass.  The quasi-period law above assumed the carrier nowhere zero, so that
`logDeriv f` is entire.  When the two steps are `R`-dependent that hypothesis is **automatic**.

- **`eq_zero_iff_of_mem_span_range`** — a nonzero multiplier can neither create nor destroy a zero,
  and the property `f(z+p) = 0 <-> f(z) = 0` is stable under sums, negation and integer multiples;
  so the zero set of a quasi-periodic function is invariant under the whole integer span of the
  steps.  (The multiplicative analogue of `periodic_of_mem_span_range`; the `zsmul` branch runs by
  `Int.induction_on` through the additive and negation branches.)
- **`ne_zero_of_quasiperiods_realDependent`** — for `R`-dependent steps the span is not discrete
  (`exists_small_rankTwo_realDependent_periods`), so a single zero `z_0` would be an accumulation
  point of zeros `z_0 + p_n`, and the identity theorem
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`) would force `f = 0` identically.
  Hence a not-identically-zero entire quasi-periodic carrier with `R`-dependent steps has **no zeros
  at all**.
- **`differentiallyAlgebraic_of_quasiperiods_realDependent`** and
  `not_hypertranscendental_of_quasiperiods_realDependent` — the law with *no* nonvanishing
  hypothesis: either `f` vanishes identically, and is constant, or it has no zeros and the general
  law applies.

So on the `R`-dependent branch `(24)`--`(26)` is now proved in the same generality as the paper
states it, for entire carriers.  The nonvanishing hypothesis survives only on the lattice branch,
where it is genuinely needed: there `logDeriv f` would be elliptic rather than entire, which is the
same `EllipticHypertranscendenceFree` boundary that bounds every other analytic step of this card.

## Lean progress — the FINITE-STATE law `(27)`--`(33)`, without Wronskians

`GaloisForLFunctions/HTGeometry/SmallTranslationDerivInvariance.lean` and
`GaloisForLFunctions/HTGeometry/MatrixFacetCodimension.lean` (axiom-clean, build green,
umbrella-registered).  This replaces the paper's route to `(27)`--`(30)` by a shorter one that is
unconditional.

**The paper route and why it is not the one formalized.**  §"Finite-state quasi-period law" builds
the monic annihilator `(29)` from a Wronskian, then observes `(30)` that its coefficients are
periodic, hence elliptic in the lattice case, hence DA, and finally invokes *transitivity* of
differential algebraicity.  Two of those steps are heavy: the Wronskian nonvanishing criterion, and
transitivity over a DA coefficient field.  In the lattice case the coefficients are elliptic, so
that route also needs `EllipticHypertranscendenceFree`.

**The route formalized.**  Let `H` be the `C`-span of the components of the carrier -- finite
dimensional, and stable under each structural translation because the internal matrix has constant
entries.  When the integer span of the steps is **not discrete**, `H` is stable under translation by
arbitrarily small nonzero steps `p_n -> 0`.  The difference quotients `(g(. + p_n) - g)/p_n` then lie
in `H`, converge *pointwise* to `g'`, and a finite-dimensional subspace is closed in the topology of
pointwise convergence.  Hence `H` is stable under `d/dz`, and the corpus's finite observable-model
boundary (`HTGeometry.differentiallyAlgebraic_of_mem_derivInvariantObservableSpace`, from
`FiniteObservableKoopmanBoundary`) gives every member a nonzero **constant-coefficient** annihilator.

- `derivInvariantObservableSpace_of_small_translations` — the analytic step just described;
- `translationStable_neg` — a translation mapping a finite-dimensional space into itself is
  automatically invertible on it (injective endomorphism of a finite-dimensional space), so the
  internal matrices need **not** be assumed invertible, unlike `(27)`;
- `translationStable_of_mem_span_range` — the whole step group acts;
- **`differentiallyAlgebraic_of_translationStable_of_not_discrete`** — the general law, with the two
  specializations for three `Q`-independent steps and for two `Q`-independent `R`-dependent steps;
- **`differentiallyAlgebraic_component_of_matrix_monodromy`** — `(27)`--`(30)`: for
  `G(z+w_k) = M_k G(z)` with constant `M_k` and non-discrete step span, *every component* of `G` is
  differentially algebraic.  No Wronskian, no transitivity, no elliptic input.

`MatrixFacetCodimension` then repeats the scalar facet chain verbatim for finite internal state:

- `MatrixFacetRealization` — the datum of `(31)`: entire `C^m`-valued facet carriers, each omitted
  translation reproducing the carrier up to a constant matrix, some component hypertranscendental;
- `no_matrixFacetRealization_of_three_omitted` and
  `no_matrixFacetRealization_of_two_omitted_realDependent`;
- **`matrixFacetComplement_rankOne_or_lattice`** — `(33)` up to the single surviving alternative:
  every facet omits at most one ambient vertex, or exactly two whose steps are `R`-independent and
  span a lattice;
- `matrix_facetComplementRankOne_of_no_lattice`.

So the finite-state section of the card is now formalized to exactly the same frontier as the scalar
section, and by a strictly weaker hypothesis set.  The surviving gap is the same one everywhere on
this card: two omitted steps spanning a genuine lattice.

**Deduplication.**  `differentiallyAlgebraic_of_quasiperiods_realDependent` is now the
one-dimensional case of `differentiallyAlgebraic_of_quasiperiods_of_not_discrete` rather than a
separate `logDeriv` argument, and in that form it needs neither nonvanishing nor nonzero multipliers.
The `logDeriv` route is kept only where it yields something the span route does not: the structural
fact `ne_zero_of_quasiperiods_realDependent` that such a carrier has no zeros at all, and the lattice
branch of `differentiallyAlgebraic_of_quasiperiods`.

## Lean progress — attacking the lattice branch: exponential type

The one alternative still open everywhere on this card is a facet omitting two vertices whose steps
are `R`-independent, i.e. span a genuine lattice.  For an **entire** carrier that case is not
elliptic-function theory at all: it is a growth-versus-zero-counting statement.

If `f` is entire with `f(z+w_1) = a f(z)`, `f(z+w_2) = b f(z)` for a lattice, and `f` has a zero
`z_0`, then the zero set contains the whole coset `z_0 + Lambda`, whose counting function grows like
`r^2`.  But the multiplier relations bound `f` by an exponential of `|z|`, and Jensen's inequality
bounds the zero count of such a function linearly in `r`.  Contradiction: an entire carrier with
constant multipliers over a lattice has **no zeros**, and then the already-formalized
`differentiallyAlgebraic_of_quasiperiods` applies.  Mathlib now carries the required inequality
(`AnalyticOnNhd.sum_divisor_le` in `Mathlib/Analysis/Complex/JensenFormula.lean`).

`GaloisForLFunctions/HTGeometry/QuasiPeriodEntireGrowth.lean` (axiom-clean, build green,
umbrella-registered) supplies the growth half:

- `quasiPeriodic_zsmul` — a constant-multiplier quasi-period iterates over `Z` (`Int.induction_on`,
  the backward step using `a != 0`);
- `quasiPeriodic_lattice` — `f(z + m w_1 + n w_2) = a^m b^n f(z)`;
- `stepBasis` and `exists_bound_stepBasis_repr` — two `R`-independent complex numbers are an
  `R`-basis of `C`, and its coordinate functionals are bounded by a multiple of the norm (they are
  linear maps on a finite-dimensional space, hence continuous);
- **`exists_exp_growth_bound_of_quasiperiods`** — `||f z|| <= K exp(c ||z||)`: subtract the integer
  parts of the two coordinates to land in the compact fundamental parallelogram, bound `f` there by
  compactness, and pay `max(|a|,|a|^-1)` and `max(|b|,|b|^-1)` per lattice step.

Remaining for this branch: the lattice-point count `#{(m,n) : ||z_0 + m w_1 + n w_2 - c|| <= r} >>
r^2`, and the Jensen comparison that contradicts it.

### The counting half

`GaloisForLFunctions/HTGeometry/QuasiPeriodLatticeZeros.lean` (axiom-clean, build green,
umbrella-registered) supplies the other estimate.

- `latticeBox z_0 w_1 w_2 N` — the coordinate box `{z_0 + m w_1 + n w_2 : |m|,|n| <= N}` as a
  `Finset C`;
- `latticeBox_injOn` and **`card_latticeBox`** — it has exactly `(2N+1)^2` elements, because
  `R`-independent steps are `Z`-independent (`LinearIndependent.restrict_scalars'`);
- `norm_sub_le_of_mem_latticeBox` — it lies in the ball of radius
  `||z_0 - c|| + N(||w_1|| + ||w_2||)` about any centre, so a ball of radius `r` contains a box with
  `N` proportional to `r`, hence `~ r^2` points;
- **`eq_zero_of_mem_latticeBox`** — a quasi-periodic function vanishing at `z_0` vanishes on the
  whole box.

What is left for the lattice branch is only the comparison itself: feed a bound `M` on the sphere of
radius `2r` from `exists_exp_growth_bound_of_quasiperiods` into `AnalyticOnNhd.sum_divisor_le`, which
gives `#zeros in the ball of radius r <= log(M/||f c||)/log 2 = O(r)`, and contradict it with the
`(2N+1)^2` zeros just produced.
