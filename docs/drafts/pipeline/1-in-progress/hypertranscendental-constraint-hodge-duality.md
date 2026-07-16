# Hypertranscendental constraint-Hodge duality

- **ID:** `hypertranscendental-constraint-hodge-duality`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CLASSIFICATION CONJECTURE / BIFILTERED SOURCE THEORY
- **Scientific status:** `[CONJECTURE] [NORMAL-CROSSING SEED LEAN-FORMALIZED]`
  `[FIELDS-MEDAL-SCALE OPEN CORE] [NOVELTY OPEN] [NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-source-descent-duality.md`
  - `hypertranscendental-conormal-integrability-correspondence.md`
  - `../3-formalized/normal-crossing-derived-critical-base-change-defect.md`

## Founding claim

Hypertranscendence kills the degree-zero differential constraint ideal.  It does not kill
constraints comparing different source fibres.  A source-minimal constrained HT object should
therefore have two irreducible homological coordinates:

```text
p = internal derived/conormal excess,
q = source-face/descent depth.
```

These coordinates are not two clocks and are not two choices of presentation.  They distinguish
how much derived constraint is visible from how many source comparisons are required to expose it.

> **[CONJECTURE -- HT CONSTRAINT-HODGE DUALITY]** The category of regular source-minimal self-dual
> constrained hypertranscendental germs is equivalent, modulo differential-birational source
> equivalence, to a category of pointed source-effective polarized constraint-Hodge objects
> `C_x^(p,q)` satisfying:
>
> 1. the vertex algebra in source degree zero is differentially free;
> 2. all nontrivial conormal constraint data occur in positive source degree;
> 3. elementary source restriction has quasi-smooth exterior excess, so `C_x^(p,q)=0` outside
>    `0 <= p <= q` after source minimalization;
> 4. fixed-source-degree duality pairs `p` with `q-p`;
> 5. the pointed bifiltered object, its source composition, affine calibration, analytic growth,
>    and polarization reconstruct the HT source germ;
> 6. analytic continuation, monodromy, spectral, boundary, and Hermitian realizations are jointly
>    conservative.

This is a proposed positive dual category for a class currently defined negatively by the absence
of differential equations.  It constrains hypertranscendental functions themselves: only source
boundaries satisfying effectivity, the constraint cone, duality, and analytic realization may
occur in the self-dual geometric class.

## Exact normal-crossing constraint diamond `[PROVED + LEAN]`

For an `N`-direction normal-crossing source, a codimension-`q` face has a rank-`q` exterior
critical base-change defect.  There are `binom(N,q)` such faces, and its internal degree-`p`
exterior multiplicity is `binom(q,p)`.  Hence

```text
h_N^(p,q) = binom(N,q) binom(q,p).                         (1)
```

The exact consequences are

```text
h_N^(p,q)=0 unless 0 <= p <= q <= N,                       (2)
h_N^(p,q)=h_N^(q-p,q),                                    (3)
sum_(p,q) h_N^(p,q)=3^N,                                  (4)
H_N(u,v)=sum_(p,q) h_N^(p,q)u^p v^q=(1+v+uv)^N.           (5)
```

The three states in `(4)`--`(5)` are: a structural direction is absent, belongs to the source
face only, or belongs to both the source face and its derived excess.  Equation `(3)` is exterior
Poincare duality inside one fixed source face.

Lean formalizes `(1)`--`(4)`, the containment model `excess subset source`, and its duality
involution in

```text
formal/GaloisForLFunctions/HTGeometry/NormalCrossingConstraintHodgeDiamond.lean
```

with capstones:

- `normalCrossingConstraintMultiplicity_eq_zero_of_source_lt_excess`;
- `normalCrossingConstraintMultiplicity_eq_zero_of_rank_lt_source`;
- `normalCrossingConstraintMultiplicity_duality`;
- `sum_normalCrossingConstraintMultiplicity`;
- `NormalCrossingConstraintLabel.excessDegree_le_sourceDepth`;
- `NormalCrossingConstraintLabel.dual_dual`;
- `NormalCrossingConstraintLabel.dual_excessDegree`.

This exact diamond is a seed and a falsifier for the conjectural category.  Its binomial identities
are elementary consequences of exterior excess intersection and are not claimed as new general
mathematics.

## One-parameter totalization no-go `[PROVED + LEAN]`

Any additive scalar grading of the two degrees is a monoid homomorphism

```text
phi : N^2 -> N.
```

No such homomorphism is injective.  If the weights are positive `a,b`, the pure bidegrees `(b,0)`
and `(0,a)` already collide.  Therefore no one-parameter totalization, master clock, or scalar
spectral parameter can be a faithful invariant of an unbounded constraint-Hodge object.

This is formalized in

```text
formal/GaloisForLFunctions/HTGeometry/BifilteredScalarizationNoGo.lean
```

by `natProd_addMonoidHom_not_injective` and
`scalarTotalDegree_pureAxis_collision`.

> **[POSITIVE SUCCESSOR]** The minimal faithful grading receiver is rank two: a bifiltered or
> two-variable Rees object retaining the full source/internal cone.  Scalar totalizations remain
> useful realization functors, but cannot define the source object.

There is also an exact positive joint-conservativity theorem:

```text
(p,q) |-> (p+q, p+2q)                                    (6)
```

is injective.  Thus no single scalar proof chain can retain the full bidegree, while two
nonparallel scalar observations reconstruct it exactly when comparison data identifies their
values on the same class.  Lean formalizes `(6)` as `transverseScalarDegrees_injective`.

The pairing clause is load-bearing.  The two distinct packets

```text
{(1,1),(2,1)}    and    {(0,2),(3,0)}
```

have the same separate `(1,1)`-weighted and `(1,2)`-weighted scalar spectra after different
matchings.  Therefore two unpaired proof-chain spectra still do not reconstruct the unified
object.  Lean formalizes this exact marginal ambiguity as
`transverseScalarMarginal_pairing_ambiguity`.

This is the first rigorous form of the working hypothesis that distinct obstruction chains may be
different representations of one object.  At the grading level, “different” must mean transverse:
duplicating the same scalarization adds no information, two independent slopes separate every
bidegree, and an actual comparison map is required to align their classes.

> **[POSITIVE SUCCESSOR TO THE MARGINAL NO-GO]** The unified field must contain cross-realization
> comparison data, not merely a list of spectra.  Joint conservativity is a theorem about a coupled
> family of functors over one source object; it cannot be inferred from agreement of unpaired
> spectral sets.

## Unbounded source height is forced `[PROVED + LEAN]`

The source degree cannot have a universal finite ceiling.  For a cyclic HT source class `q` over
an augmented source-operator algebra `(A,m)`, define the augmentation-adic onset

```text
ht_src(q)=min{total m-degree of 0 != P in Ann_A(q)}.
```

The generic order-`r` multiple-elliptic-gamma hierarchy has exact DA annihilator the squarefree
coface ideal `I_r`.  Therefore `ht_src(q_r)=r`.  More strongly, for every cutoff `H`, the object
with `r=H+1` has no nonzero annihilator polynomial of total augmentation degree at most `H`, but
does have one in degree `H+1`.

This is proved algebraically and formalized in

```text
formal/GaloisForLFunctions/HTGeometry/SourceConstraintHeight.lean
```

by `totalDegree_lt_constraintHeight_not_mem_veroneseIdeal` and
`boundedSourceDepth_misses_next_normalCrossingConstraint`; the special-function interpretation
uses the separately proved all-order exact-annihilator theorem.

> **[THEOREM — NO UNIFORM FINITE CONSTRAINT HEIGHT]** No fixed source-degree truncation is
> conservative on natural constrained HT functions.
>
> **[POSITIVE SUCCESSOR]** The constraint-Hodge category must retain the unbounded augmentation
> filtration.  The stronger identification of its onset with the first nonzero source-Postnikov
> layer is part of the classification conjecture.  Finite diamonds are objects or local charts
> inside the theory, not a uniform bound on the theory itself.

For the normal-crossing purity class, exact source height is one more than exact derived-critical
amplitude:

```text
ht_src(q_r)=r=(r-1)+1=derivedAmplitude(dCrit(f_r))+1.
```

This equality is not proposed for arbitrary ideals.  Its role is to identify the first
associated-graded source layer with the top internal excess in one substantive essential-image
class.  The general classification must determine the allowed height/amplitude profiles rather
than force every source onto this pure ray.  See
`../3-formalized/unbounded-hypertranscendental-source-constraint-height.md`.

There is also an exact positive reconstruction theorem.  For every `r>=2`,

```text
P in I_r  <=>  x_i P in I_r for every immediate source face i.
```

Hence the joint map `[P] |-> ([x_iP])_i` out of `A_r/I_r` is injective.  The source height is
unbounded across objects, yet every individual normal-crossing structural class is separated by
its complete family of one-step-lower faces.  Lean formalizes this as
`mem_veroneseIdeal_iff_all_X_mul_mem`.

This is the first exact local-to-global law for the constraint-Hodge proposal.  The `r=1`
threshold explains why the triptic base case needs a pointed residue/calibration: all immediate
augmentation multiplications kill its constant quotient class.  From height two onward, joint
coface descent is already faithful on the algebraic structural quotient.

## Height-one realization correspondence `[PROVED ON PAPER]`

The triptic mixed-constraint class supplies the first nontrivial positive converse.  For
`1,tau,sigma` rationally independent, let

```text
Q={F meromorphic and 1-periodic:Delta_tau Delta_sigma F is constant}.
```

Taking labelled orbital principal parts of `Delta_sigma F` on
`C/(Z+Z tau)` defines `R_tau(F)`.  Reversing the roles of `tau` and `sigma` defines
`R_sigma(F)` on a different elliptic curve.  The triptic orbit-residue theorem proves

```text
R_tau(F)=R_sigma(F)=R_trip(F),
ker R_trip=Q intersect Mer_DA,
R_trip:Q/(Q intersect Mer_DA) ~= C[delta][C/(Z+Z tau+Z sigma)].
```

Thus two genuinely different analytic boundary functors are not merely jointly conservative on
this class: each reconstructs the complete DA-quotient object, and reciprocity identifies their
outputs canonically.  This is the first literal theorem-level instance of “different obstruction
chains are realizations of one object.”  It is recorded in
`../2-fully-proven/new_scientific_knowledge/triptic-orbit-residue-reciprocity.md`.

The boundary is exact.  This theorem reconstructs the mixed-constraint class modulo DA, not the
full analytic germ; it is abelian and height one; and its completeness uses the separately audited
elliptic-gamma atomic theorem.  It does not prove the general constraint-Hodge correspondence.

> **[CONJECTURE — HIGHER ORBIT-RESIDUE DESCENT]** For every height `r`, a regular source-minimal
> meromorphic HT constraint class has a source-native residue/Cousin complex on its rank-`r`
> face nerve.  Its first nonzero cohomology occurs at the augmentation onset, its higher
> reciprocity equations are the cocycle condition, and its DA quotient is reconstructed by the
> corresponding labelled cohomology object.  The triptic theorem is the height-one equivalence;
> the all-order coface annihilator and normal-crossing derived excess are respectively the
> associated-graded and derived shadows of the higher equivalence.

This is stronger than extrapolating one residue formula.  It predicts the target category, the
degree in which it first appears, an intrinsic essential-image condition, and a reconstruction
theorem.  Failure at height two would be equally significant: it would prove that residue data
must be enlarged by a new analytic component beyond source height, derived excess, growth, and
polarization.

## Why bare differential modules cannot be the object

If `x` is hypertranscendental over `K`, its derivative family is algebraically and hence linearly
independent over `K`.  Every nonzero finite linear differential operator acts nontrivially on `x`.
Thus its cyclic vertical operator orbit is free, and bare vertical annihilator data cannot
distinguish one HT source from another.

> **[NO-GO]** A holonomic, finite-rank, or unpointed vertical `D`-module cannot be a conservative
> receiver for hypertranscendental identity.
>
> **[POSITIVE SUCCESSOR]** Identity lives in the pointed source realization: the free vertical
> orbit together with its positive-source-degree relation object, comparison maps, growth, and
> polarization.

This is compatible with parameterized difference Galois theory, where prolongations of a finite
source equation can have unbounded differential transcendence.  The claim is not that prolongation
or differential Tannakian theory is new; it is that a complete self-dual HT object must retain the
source/vertical bidegree and its non-holonomic pointed realization.

## Realization dictionary `[CONJECTURE, NOT IDENTIFICATIONS]`

For a constraint-Hodge object `C_x`, the candidate obstruction readings are:

```text
continuation failure     = non-effectivity in source degree q,
monodromy                = holonomy of source-face comparison maps,
spectral incompleteness  = surviving internal classes in degree p,
boundary noncanonicity   = inequivalent completions/totalizations of the bifiltration,
positivity failure       = failure of a compatible positive real polarization.
```

The conjecture requires these to be conservative realizations of one object.  Similar vocabulary
does not prove that two obstructions are the same.  A proof must construct comparison functors and
show that joint vanishing detects equivalence.

## Parent-theory and novelty gate

The following are established and are not novelty claims:

1. bifiltered and multi-Rees `D`-modules, including order and `V` filtrations;
2. mixed Hodge modules and polarized regular or wild twistor `D`-modules;
3. cohomological descent and spectral sequences of cosimplicial objects;
4. derived critical loci, exterior excess bundles, and shifted symplectic duality;
5. differential Tannakian categories, parameterized difference Galois groups, and prolongation
   functors;
6. regular and irregular Riemann--Hilbert correspondences for holonomic `D`-modules.

Therefore “use two filtrations,” “take a Rees module,” “add a polarization,” and the diamond
formula `(1)` all fail the novelty gate by themselves.

The candidate-new residue is the conjunction:

1. hypertranscendence forces degree-zero vertical freeness and moves every effective constraint
   to positive source degree;
2. the resulting source/internal cone and polarization characterize an essential image rather
   than decorate an arbitrary complex;
3. the complete pointed bifiltered object reconstructs a non-holonomic HT source germ;
4. genuinely different analytic obstruction categories are jointly conservative realizations of
   that object.

No checked source states this equivalence or essential-image theorem.  This remains a provisional
search result, not a novelty certificate.  Independent specialists in differential algebra,
derived geometry, and twistor/Hodge modules must audit it.

## Anti-theatre gate

The program fails if any of the following occurs:

1. the constraint cone `p<=q` is only an indexing convention and excludes no realizable source
   object;
2. the proposed category is merely an Ind-completion of mixed or wild twistor `D`-modules with no
   new essential-image or reconstruction theorem;
3. source minimalization is not Morita invariant;
4. two inequivalent source-minimal HT germs have the same complete pointed polarized object;
5. the five obstruction realizations are compared only by analogy, without conservative functors;
6. analytic growth and boundary data can be deleted without changing realizability.

For each failure the positive target is explicit: prove a strict essential-image condition, add
the missing source pointing or analytic growth datum, or retire the proposed invariant.

## Fields-scale theorem target

The normal-crossing diamond and scalarization no-go are not Fields-scale.  The Fields-scale result
would be the full equivalence above, including:

1. construction and Morita invariance of `C_x` for a nonlinear nonabelian HT source class;
2. identification of augmentation-adic source height with the first nonzero source-Postnikov
   layer, including its forced unboundedness across the category;
3. an intrinsic essential-image theorem with the constraint cone and polarization as substantive
   restrictions;
4. reconstruction of the analytic source germ;
5. two genuinely different realization functors proved jointly conservative;
6. a new analytic theorem obtained from the constraint-Hodge object that neither parent theory
   proves alone.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` If a completed-zeta source object exists independently of its zero
divisor, different RH proof chains may be scalar or completed realizations of its constraint-Hodge
object.  Critical zeros would be a common self-dual degeneracy spectrum only after realization
conservativity is proved.  RH would still require a separate positive fixed-locus theorem.  Neither
zeta, its zeros, nor an RH-equivalent positivity condition may define the object.

## Gates

- [x] exact normal-crossing constraint diamond proved on paper
- [x] support cone, exterior duality, and total capacity Lean-formalized
- [x] all scalar additive totalizations proved nonfaithful in Lean
- [x] unbounded source-constraint height and every fixed-depth truncation no-go proved in Lean
- [x] joint immediate-coface reconstruction proved for every normal-crossing height at least two
- [x] two noncommensurable boundary-residue realizations proved conservative on the height-one
  triptic DA-quotient class
- [x] collided Rees, Hodge, twistor, derived-critical, and parameterized-Galois vocabulary with
  parent theory
- [ ] construct the pointed bifiltered object in one nonlinear nonabelian HT class
- [ ] prove source-presentation Morita invariance
- [ ] prove the cone is a strict essential-image restriction
- [ ] reconstruct one analytic HT source from the complete object
- [ ] prove two realization functors jointly conservative
- [ ] derive a new analytic consequence
- [ ] obtain an independent specialist novelty and significance verdict
