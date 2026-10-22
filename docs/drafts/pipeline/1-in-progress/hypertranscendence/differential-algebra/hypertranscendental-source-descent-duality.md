# Hypertranscendental source-descent duality

- **ID:** `hypertranscendental-source-descent-duality`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CLASSIFICATION CONJECTURE / POSITIVE-DEGREE CONSTRAINT THEORY
- **Scientific status:** `[CONJECTURE] [FIELDS-MEDAL-SCALE OPEN CORE] [FLAT RANK-ONE SEED LEAN-FORMALIZED] [NOVELTY OPEN]`
- **Parents:**
  - `curved-tannakian-source-envelope-spectrum.md`
  - `ht-source-riemann-hilbert-correspondence.md`
  - `source-logarithmic-boundary-matroid.md`
- **Statement:** A regular source-minimal constrained hypertranscendental germ has no local
  differential-algebraic constraint, but it has a canonical positive-simplicial-degree source
  constraint.  The complete positive-degree source object reconstructs the germ and every valid
  analytic obstruction realization.

## The proposed founding displacement

Let `(K,D)` be a differential field and let `x` be one observable.  Its local clock algebra is the
image of

```text
K{X} -> K<x>,       D^n X |-> D^n x.                       (1)
```

The kernel is the degree-zero or **vertical constraint ideal** `I_vert(x)`.  By definition,

```text
x is hypertranscendental over K  <=>  I_vert(x)=0.          (2)
```

Now retain the independently given source operations.  Their arrows compare jets at different
source points.  A functional equation does not cut out a subvariety in one copy of the jet fibre;
it cuts out a correspondence in a product of source fibres.  Its prolongations form a simplicial
relation object over the source nerve.

Write `R_bullet(x)` for the minimal differential-algebraic source relation groupoid of `x`.  Its
relative cotangent object splits conceptually into

```text
vertical/local conormal       in simplicial degree 0,
horizontal/source conormal    in positive simplicial degrees.       (3)
```

Equation `(2)` kills the first term, not the second.

> **[CONJECTURE — HYPERTRANSCENDENTAL DEGREE SHIFT]** For every regular source-minimal constrained
> HT germ, the vertical conormal is zero and the complete source constraint is represented by a
> nonzero perfect horizontal conormal object `B_x` in positive simplicial degree.  Conversely, a
> regular source object with free vertex clock algebra and nonzero admissible horizontal conormal
> has hypertranscendental vertex observables.

This is the literal proposed meaning of

```text
hypertranscendence = infinite algebraic clock capacity
                     concentrated on a thin constraint boundary.    (4)
```

The capacity is the free vertex algebra.  The thin boundary is the finitely source-generated
horizontal conormal.  Constraint has not vanished; it has moved from equations to descent data.

## Exact flat seed

Suppose a family of source automorphisms satisfies

```text
tau_i(x)=b_i x.                                             (5)
```

Put `u=D(x)/x` and `omega_i=D(b_i)/b_i`.  Then

```text
tau_i(D^n u)-D^n u = D^n omega_i.                          (6)
```

For an arbitrary selected finite-resolution packet `D^(order j)u`, the project now proves the
exact equivalence

```text
the bulk packet is algebraically independent over K
<=>
no nonzero finite C-linear combination of the matching D^(order j)omega_i
is one simultaneous source coboundary tau_i(k)-k.          (7)
```

Thus the complete algebraic matroid of the nonlinear bulk packet is represented by a linear
matroid in the horizontal source boundary.  This holds for arbitrary, possibly noncommuting,
source families.  The arbitrary-packet equivalence is Lean-formalized as
`automorphismFamily_logarithmicJet_algebraicIndependent_iff`.

Equation `(7)` is not the classification conjecture.  It is the rank-one flat theorem forcing its
shape: local nonlinear algebraic dependence is exactly the shadow of a horizontal source
conormal relation.

## The complete object cannot be only a cotangent complex

A unary conormal sees only first-order source geometry.  Distinct nonlinear source germs can have
the same linearization.  Therefore the proposed boundary object must retain the normalized
relative source nerve with its multiplication, composition, and higher coherence operations.
One model is the reduced relative bar object

```text
B_x = N_red O(R_bullet(x)),                                (8)
```

viewed with its differential-clock action, affine marked point, source composition coproduct,
and all higher operations.  The linear horizontal conormal is its first infinitesimal shadow.
No novelty is claimed for bar constructions, cotangent complexes, or groupoid nerves.

> **[CONJECTURE — SOURCE-DESCENT RECONSTRUCTION]** On a regular finite-source class, the assignment
>
> ```text
> x |-> (free clock algebra K{X}, B_x, affine marking)       (9)
> ```
>
> is fully faithful modulo differential-birational source equivalence and Morita equivalence of
> source presentations.  Its essential image is characterized by finite source generation,
> clock compatibility, Segal composition, analytic growth, and effectivity conditions.

Full faithfulness says that the positive-degree boundary reconstructs both the observable and its
nonlocal source germ.  Essential surjectivity says which abstract thin boundaries actually come
from hypertranscendental functions.  Together they are the proposed **source-descent duality**.

### Falsifiers

1. Two source-minimal HT germs have equivalent complete objects `(9)` but are not
   differential-birationally source equivalent.
2. Morita-equivalent source presentations produce inequivalent marked bar objects.
3. A boundary object satisfying the proposed intrinsic image conditions has no HT realization.
4. The rank-one flat theorem `(7)` cannot be recovered functorially as the first linear shadow of
   `(9)`.

## Constraint depth

The positive-degree object has a Morita-invariant Postnikov filtration.  Define the
**source-constraint depth** of a regular HT germ to be the least positive degree in which its
minimal reduced source object has nonzero homotopy or cotangent data.

> **[CONJECTURE — CONSTRAINT-DEPTH STRATIFICATION]** Constraint depth is an invariant of the HT
> source germ.  Rank-one shift, `q`-difference, and Mahler equations have depth one.  Higher depth
> detects source syzygies that cannot be removed by logarithmic, affine, or finite Tannakian
> linearization.  The depth filtration is strict: source-minimal HT germs occur at arbitrarily
> large finite depth and at infinite depth.

This predicts a new hierarchy invisible to differential transcendence degree: two observables can
both have maximal clock capacity while their constraints live in different categorical degrees.

**Falsifier.** Every regular finite-source HT germ is Morita-equivalent to a depth-one difference
groupoid, or the proposed depth changes under a source-equivalent resolution.

## Source realization theorem

Let `Real_R(B_x)` be the realization of `(8)` in an analytic category `R` retaining its domain,
closure, affine calibration, reflection, and source composition.

> **[CONJECTURE — REALIZATION CONSERVATIVITY]** There is a source category of admissible
> realizations for which the family `Real_R` is jointly conservative on `B_x`: a morphism of HT
> boundaries is an equivalence exactly when every admissible realization is an equivalence.
> Moreover, continuation failure, boundary-condition ambiguity, monodromy, spectral
> incompleteness, and positivity failure are respectively extension, component, holonomy,
> homology, and polarization defects of realizations of this one object.

The statement is deliberately stronger than equality of spectra or determinants.  It requires
comparison functors preserving the source nerve, clock action, affine point, and reflection.

## Self-dual spectrum

For a reflected parameter family, suppose the source boundary has a coherent duality

```text
B_(s^vee) ~= B_s^vee.                                     (10)
```

> **[CONJECTURE — POLARIZED SOURCE SPECTRUM]** A source-canonical polarization of an admissible
> realization defines a perfect comparison complex `C_s`.  Its degeneracy locus is independent of
> the realization and is the common source spectrum.  Duality gives paired degeneracies;
> positivity is the additional theorem needed to force degeneracy onto the fixed locus.

This separates the common object, self-duality, and positivity.  None implies either of the other
two.

## RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A completed-zeta source object, if it exists, must be constructed
from the prime--archimedean source nerve before its zero divisor.  The different RH proof chains
represent one interval only if their comparison complexes are conservative realizations of the
same `B_zeta`.  The critical zeros would then be the common self-dual degeneracy spectrum of that
object.  RH would require the separate polarized fixed-locus theorem.

No zero, zero-indexed operator, or RH-equivalent positivity criterion may be used to define
`B_zeta`.

## Parent-theory attack

The following are established parent languages and are not novelty claims:

1. Hardouin--Singer parameterized difference Galois theory measures differential relations among
   solutions of linear difference equations.
2. Malgrange--Granier `D`-groupoids encode differential equations and nonlinear difference
   dynamics in jet groupoids.
3. Tannakian reconstruction, groupoid nerves, bar--cobar duality, cotangent complexes, descent,
   and Morita invariance are classical frameworks.
4. Difference Riemann--Hilbert correspondences, monodromy, Stokes data, boundary triples, and
   determinant lines are established in important classes.

Therefore “put the functional equation in a groupoid” is a no-go as new mathematics.

**Positive survivor.** The candidate-new theorem is the conjunction of four assertions not
supplied by those parents:

1. the invariant degree shift forced by hypertranscendence;
2. reconstruction of a nonlinear HT source germ from its complete positive-degree boundary;
3. an intrinsic essential-image theorem classifying which thin boundaries are realizable;
4. conservative comparison across genuinely different analytic obstruction categories.

Removing any one item collapses the program to a parent theory or a change of vocabulary.

## Why this is the Fields-medal-scale claim

The rank-one matroid theorem is a paper-level base case.  The medal-scale result would be the
classification theorem `(9)` together with realization conservativity: it would replace the
current negative definition of hypertranscendence by a positive dual category, reconstruct
nonlocal constraints from their thin boundaries, and prove that analytic obstruction theories
now treated separately are realizations of one invariant.

The claim is not promoted.  It earns that scale only after full faithfulness, essential image,
one nonlinear nonabelian example, and two genuinely different analytic realizations are proved.

## Gates

- [x] degree-zero local ideal identified exactly with differential algebraicity
- [x] arbitrary-packet flat multiplicative boundary equivalence Lean-formalized
- [x] groupoid-only novelty killed by Malgrange--Granier and parameterized Galois parents
- [x] unary cotangent reconstruction killed by nonlinear tangent blindness
- [ ] minimal source nerve and complete marked boundary object constructed in one nonlinear class
- [ ] Morita invariance proved for two inequivalent source presentations
- [ ] full faithfulness proved in a nontrivial class
- [ ] intrinsic essential-image criterion proved
- [ ] constraint depth proved invariant and shown nonconstant
- [ ] two genuinely different analytic realizations proved jointly conservative
- [ ] self-dual polarized comparison constructed away from RH
- [ ] independent specialist novelty and significance verdict
