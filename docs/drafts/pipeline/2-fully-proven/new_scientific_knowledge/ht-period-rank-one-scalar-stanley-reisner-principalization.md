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
