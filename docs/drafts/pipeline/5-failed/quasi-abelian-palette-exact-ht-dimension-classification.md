# Quasi-Abelian palettes classify finite full HT constraint geometry

- **ID:** `quasi-abelian-palette-exact-ht-dimension-classification`
- **Stage:** 5-failed
- **Type:** FALSIFIED CONJECTURE / MISSING ACTION-RELATIVE SELECTOR
- **Scientific status:** `[FALSIFIED] [POSITIVE REPLACEMENT EXTRACTED]`
- **Statement:** Ambient noncompact quasi-Abelian geometry does not suffice for a completely free
  structural orbit.  A facet lattice trapped in a compact Abelian factor has finite capacity for
  every individual observable, even when the total meromorphic field has unbounded complexity.

## Terminal verdict

The equality `htDim=qaDim` and the quasi-Abelian full-orbit theorem stated below are false.
Take

```text
X=E x C*,
H=Z a subset E,
```

with `E` elliptic and `a` nontorsion.  The group `X` is noncompact and satisfies the relevant
generalized Riemann geometry, while `H` is faithful in `X`.  Nevertheless relative rationality
along the projective elliptic fibre makes every `g in Mer(X)` a rational Abelian function with only
finitely many meromorphic `C*`-coefficient functions.  Compact translation changes the Abelian
coordinate but creates no new coefficient functions.  Hence every cyclic `H`-orbit has finite
differential transcendence degree.

The no-go has a strong positive residue: every prescribed finite orbit capacity occurs, so the
capacity supremum is infinite but is not attained by one observable.  The exact theorem and proof
are isolated in
`../2-fully-proven/new_scientific_knowledge/elliptic-shadow-ht-capacity-nonattainment.md`.

The corrected classification must require the structural lattice to remain faithful after
quotienting by the maximal compact complex subtorus.  That route continues in
`../1-in-progress/active-quasi-abelian-palette-exact-ht-dimension-classification.md`.

## The gap this theorem would close

Finite constraint universality shows that every finite simplicial complex occurs.  It does not say
which analytic dimensions can carry a given complex, and the present necessary and sufficient
invariants leave the gap

```text
peDim(Delta) <= htDim(Delta) <= ppDim(Delta).                (1)
```

The left invariant remembers only noncompactness of each facet period quotient.  This is too weak:
not every discrete period lattice supports a nondegenerate meromorphic function.  The right
invariant insists that each quotient be the one-dimensional cylinder `C/Z`.  This is too special:
the exact classical existence class is the family of quasi-Abelian quotients satisfying the
generalized Riemann relations.

The proposed invariant inserts that exact meromorphic-existence geometry between the two bounds.

## Quasi-Abelian palette dimension

Let `Delta` be a finite simplicial complex on a nonempty essential finite vertex set `V`.  A
**quasi-Abelian palette separation in ambient dimension `d`** consists of `Q`-linearly independent
translation vectors

```text
a_v in C^d,  v in V,                                       (2)
```

and, for every facet `A`, a closed additive subgroup `P_A subset C^d` such that:

1. the identity component `E_A=P_A^0` is a complex-linear subspace;
2. after choosing a complex-linear complement and writing

   ```text
   W_A=C^d/E_A,   Gamma_A=P_A/E_A subset W_A,               (3)
   ```

   the group `Gamma_A` is discrete;
3. `X_A=W_A/Gamma_A` is noncompact;
4. incidence is exact:

   ```text
   a_v in P_A iff v notin A;                                (4)
   ```

5. the integral facet lattice survives faithfully:

   ```text
   Z^A -> X_A,
   n   |-> sum_(v in A)n_v a_v mod P_A                      (5)
   ```

   is injective;
6. `Gamma_A` satisfies the generalized Riemann relations: there is a positive-definite Hermitian
   form `H_A` on `W_A` whose imaginary part is integral on `Gamma_A times Gamma_A`.

Define

```text
qaDim(Delta)=min{d:a quasi-Abelian palette separation exists}.            (6)
```

By Capocasa--Catanese, condition 6 is equivalent to the existence of a nondegenerate
`Gamma_A`-periodic meromorphic function.  Noncompactness is added because a differentially
transcendental carrier cannot descend to a compact complex torus.

Every periodic-pencil separation gives `P_A=ker(C^d -> C/Z)`, so

```text
peDim(Delta)<=qaDim(Delta)<=ppDim(Delta).                   (7)
```

The first inequality forgets the generalized Riemann relation and lattice-faithfulness data.

## Exact classification theorem `[CONJECTURE]`

For every finite essential simplicial complex,

```text
htDim(Delta)=qaDim(Delta).                                  (8)
```

This would sharpen the dimension hierarchy to

```text
peDim(Delta) <= htDim(Delta)=qaDim(Delta)
                              <= ppDim(Delta) <= ffsDim(Delta).            (9)
```

The equality is a constraint theorem: it says the analytic cost of a full HT geometry is fixed by
the meromorphic period quotients its facets are allowed to possess.

## Necessity `[PROOF PROGRAM; PARENT INPUT IDENTIFIED]`

Let `F` be a meromorphic realization on `C^d` of the exact full localized Stanley--Reisner
differential matroid.  For each facet `A`, the established facet separator gives

```text
G_A=q_A(T)F.                                                (10)
```

The existing exact-kernel and full-matroid argument proves:

- `G_A` is differentially transcendental;
- `a_v` is a period of `G_A` exactly for `v notin A`;
- the functions `T^n G_A`, `n in Z^A`, are jointly differentially algebraically independent.

Take the full closed period group

```text
P_A=Per(G_A).                                               (11)
```

Its identity component is complex-linear.  The noncompact period-quotient theorem gives condition
3.  Exact periods give condition 4.  If a nonzero `n in Z^A` mapped to zero in `X_A`, then
`T^nG_A=G_A`, contradicting the two-element case of the full orbit matroid; hence condition 5.

The descended function on `X_A` has trivial period group and is therefore nondegenerate in the
sense of periodic meromorphic-function theory.  The main theorem of Capocasa--Catanese then gives
the generalized Riemann relations in condition 6.  Thus the anticipated necessity theorem is

```text
qaDim(Delta)<=htDim(Delta).                                 (12)
```

The new work in (12) is the simultaneous facet extraction and lattice-faithfulness conclusion;
the generalized Riemann relation itself is a parent theorem and must remain labelled `[SEARCH]`.

## Sufficiency `[OPEN CORE]`

The decisive theorem is the following.

> **Quasi-Abelian full-orbit theorem `[CONJECTURE]`.** Let
> `X_j=W_j/Gamma_j` be finitely many noncompact quasi-Abelian groups satisfying the generalized
> Riemann relations, and let `H_j subset X_j` be finitely generated free Abelian subgroups.  There
> exist meromorphic functions `g_j on X_j` such that all distinct translates
> `g_j(x+h)`, jointly over every `j` and `h in H_j`, are differentially algebraically independent
> after pullback to a common affine cover and differentiation in a generic constant direction.

Applied to the groups and facet lattices in (3)--(5), define

```text
Y_A(z)=g_A(z mod P_A),
F(z)=sum_(A in Fac(Delta))Y_A(z).                            (13)
```

The complement steps fix `Y_A`; condition 5 makes its facet orbit faithful.  The full-orbit theorem
makes all facet orbits jointly free.  The already formalized facet restriction, localization, and
differential-operator matroid laws then give the exact Stanley--Reisner annihilator and full
nonlinear differential matroid.  This proves

```text
htDim(Delta)<=qaDim(Delta).                                 (14)
```

### Required analytic mechanism

Capocasa--Catanese prove existence of one nondegenerate meromorphic function, not differential
freeness of an entire countable translation orbit.  Their Remmert--Morimoto decomposition and
line-bundle reduction show where the missing freedom lives.  On a noncompact quasi-torus the
meromorphic field is either constant or has infinite transcendence degree; for a fixed tame line
bundle, quotients of sections of its powers may already have uncountable transcendence degree.

Neither fact alone implies orbit freeness.  The required proof must establish coefficient-uniform
finite-jet avoidance under the translation action.  A plausible route is:

1. choose a positive tame line bundle supplied by the generalized Riemann relations;
2. place its global sections and the sections of its powers in their natural Frechet topologies;
3. prove finite translated jet interpolation for pairs of relatively prime sections;
4. express every rational-coefficient differential relation as a determinant defect on one finite
   translated jet packet;
5. prove each defect locus closed and nowhere dense;
6. take a countable Baire intersection and descend the resulting ratios to the quotient.

The exact missing lemma is **all-order finite translated jet interpolation in one fixed section
space**.  Abe proves finite point separation and tangent separation for automorphic forms of an
ample factor on a torusless quasi-Abelian variety.  His Poincare-series proof is strong enough to
suggest an all-order extension, but the published theorem stops at first jets.  Very ampleness is
not enough: products of separating sections interpolate higher jets in increasing tensor powers,
whereas the Baire construction needs one fixed Frechet space from which a single ratio is chosen.

This distinction leads to a stronger general law on the companion card
`affine-jet-packet-collision-completeness.md`: whenever a carrier has one section/function space
which interpolates every finite jet packet, a residual set of functions has a completely
differentially free orbit under every countable faithful affine action.  Thus the quasi-Abelian
converse reduces to a geometric property of the carrier, not to a special-function construction:

```text
all-order packet interpolation  ==>  complete HT orbit freedom.             (15a)
```

For the present equality, the remaining quasi-Abelian question is therefore exact: does every
noncompact generalized-Riemann quotient admit a fixed automorphic-factor space with all-order
finite jet interpolation?  Uncountable transcendence degree and very ampleness do not answer it.

### Divisor-valuation alternative `[PARTIALLY PROVED]`

There is a second route which may avoid arbitrary jet interpolation.  Choose infinitely many
irreducible aperiodic pole divisors in distinct orbits of the free subgroup `H_j`, with prescribed
pole orders tending through infinitely many integers.  At a private divisor where one translate
has a pole of order `m`, its `r`-th derivative has order `m+r` and leading coefficient containing
the rising factorial

```text
(m)^(rising r)=m(m+1)...(m+r-1).                            (15)
```

For a differential monomial with finite jet-exponent vector
`beta=(beta_0,...,beta_N)`, its leading rising-factor product is

```text
R_beta(m)=product_(r=0)^N ((m)^(rising r))^(beta_r)
          =product_(k=0)^(N-1)(m+k)^(sum_(r>k) beta_r).     (16)
```

Hence total degree together with `R_beta` determines every `beta_r`: unique factorization gives
all suffix sums `sum_(r>k)beta_r`, successive differences recover `beta_r` for `r>=1`, and total
degree recovers `beta_0`.  The finite injectivity core is formalized unconditionally as
`HTGeometry.jetPoleFingerprint_injective`.

What remains is genuinely analytic: construct one meromorphic function on every noncompact
quasi-Abelian quotient with a locally finite family of such aperiodic divisor orbits and enough
independent principal-part freedom to prevent cancellation by the regular translated factors.
The generalized Lefschetz theory supplies global generation, point separation, and immersion by
sections.  It does **not** supply an aperiodic divisor for every positive line bundle: Capocasa and
Catanese explicitly left that issue open, and the later linear-systems paper records it as Problem
2.9.  The divisor route is therefore stronger than the packet-interpolation route and may cross an
unnecessary open problem.

## Attacks and boundary cases

1. `[RETIRED]` Stein-palette classification.  Cousin quasi-tori may have nondegenerate meromorphic
   functions and enormous meromorphic fields, so Stein reduction discards legitimate carriers.
2. `[COMPACT BOUNDARY]` If `X_A` is compact, its meromorphic field has finite transcendence degree
   and is stable under invariant differentiation.  Every meromorphic function is differentially
   algebraic; compact facets cannot carry HT orbit freedom.
3. `[ONE-DIMENSIONAL BOUNDARY]` A noncompact one-dimensional quasi-Abelian quotient is `C` or
   `C*`.  Exact incidence therefore recovers the established simplex-or-pure-principal phase.
4. `[LIVE ATTACK]` Infinite transcendence degree need not be generated by one translation orbit.
   A counterexample quasi-Abelian group/action for which every cyclic orbit has finite differential
   transcendence degree would falsify (8).
5. `[LIVE COMPARISON]` It is unknown whether `qaDim<ppDim` occurs.  A strict example would exhibit
   genuinely higher-rank quasi-Abelian facet geometry.  A collapse theorem `qaDim=ppDim` would be
   equally significant, because it would upgrade periodic pencils from a construction to the exact
   classification.
6. `[LIVE ATTACK]` Extend Abe's Poincare-series separation theorem from values and first
   derivatives to arbitrary finite jets without changing the automorphic factor.  Exponential
   damping survives any fixed number of differentiations; the unresolved point is uniform
   Hermite interpolation with the subquadratic growth required by the series.

## RH-facing consequence `[CONJECTURE]`

If (8) holds, every finite prime/Euler HT route has a canonical minimum carrier dimension computed
from facetwise quasi-Abelian period data.  A one-coordinate route is forced into the pure-principal
phase.  Any nonpure exact relation geometry must expose at least two intrinsic noncompact
quasi-Abelian escape directions, and its Euler/functional-equation marking must sew those minimal
quotients rather than arbitrary auxiliary coordinates.

This does not assert that zeta realizes a finite Stanley--Reisner complex and does not prove RH.  It
would instead classify the analytic carrier geometries that an RH route of this type is allowed to
use.

## Parent-theory boundary

The generalized Riemann relation and existence of nondegenerate periodic meromorphic functions are
`[SEARCH]`, from F. Capocasa and F. Catanese, *Periodic meromorphic functions*, Acta Math. **166**
(1991), 27--68, DOI `10.1007/BF02398883`.  Remmert--Morimoto decomposition, tame line bundles, and
quasi-Abelian reduction are also parent inputs.  They do not state differential-algebraic freeness
of a countable translation orbit, simultaneous facet realization, Stanley--Reisner annihilator
geometry, or equality (8).

The exact published interpolation boundary used here is Y. Abe, *Construction of automorphic forms
for ample factors of quasi-Abelian varieties*, Kyushu J. Math. **57** (2003), 51--85, DOI
`10.2206/kyushujm.57.51`: Theorem 8.1 separates arbitrary finite point packets and Theorem 9.1
separates one tangent direction, but no all-order jet theorem is stated.

The candidate-new residue is precisely the quasi-Abelian full-orbit theorem and its conversion of
the parent period classification into the exact HT constraint-dimension law (8).

## Significance target

This route reaches a credible score near 65 only after:

- the quasi-Abelian full-orbit theorem is proved unconditionally;
- necessity and sufficiency are assembled into equality (8);
- `qaDim` is separated from `peDim` and compared decisively with `ppDim`;
- exact and equivalent formulations are audited across periodic meromorphic functions,
  quasi-Abelian varieties, difference algebra, and differential Galois theory;
- the complete promoted statement, including every analytic input it claims rather than assumes,
  is formalized unconditionally in Lean.

Until then the score is below 65 and the card remains `[CONJECTURE]`.

## Gates

- [x] Stein misclassification falsified and retired
- [x] exact quasi-Abelian palette invariant stated
- [x] necessity reduced to existing facet extraction plus the generalized Riemann relation
- [x] sufficiency localized to one named full-orbit theorem
- [x] compact and one-dimensional boundaries classified
- [ ] prove finite translated jet interpolation for quasi-Abelian line-bundle sections
- [x] isolate all-order packet interpolation as the exact geometric sufficiency condition
- [ ] prove or refute the quasi-Abelian full-orbit theorem
- [ ] prove `htDim=qaDim`
- [ ] decide the comparison with `ppDim`
- [ ] complete parent-theory and primary-literature audit
- [ ] complete unconditional Lean formalization before Stage 3
