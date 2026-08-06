# Commutative D-group source-boundary universality

- **ID:** `commutative-d-group-source-boundary-universality`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / abstract formal core open
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Formal status:** `[FORMALIZED]` — Theorems A and B and the sharp-kernel corollary are
  unconditional in Lean 4, axiom-clean; the algebraic `D`-group layer is built in the corpus
- **Statement:** Every finite family of observables valued in a finite-dimensional commutative
  algebraic `D`-group and translated by an arbitrary, possibly noncommuting source family has a
  completely linear source-boundary differential polymatroid.  The sharp kernel carries no hidden
  hypertranscendental rank.

## Setup

Let `C -> K -> L` be a tower of ordinary differential fields of characteristic zero, with `C` a
field of differential constants.  Let

```text
tau_i   : K ~= K,
sigma_i : L ~= L                                      (i in I)
```

be compatible differential-field automorphisms.  Assume that every `sigma_i` fixes `C` and that
the common fixed field in `L` is exactly `C`.  No multiplication law or pairwise commutativity is
assumed for the source family.

Let `(G,s)` be a connected commutative algebraic `D`-group of dimension `d` over `C`, with
algebraic logarithmic derivative

```text
ell_s : G(L) -> Lie(G)(L).
```

Choose a `C`-basis of `Lie(G)`.  Let `g_a in G(L)` and `a_(i,a) in G(K)` satisfy

```text
sigma_i(g_a) = a_(i,a) * g_a.                          (1)
```

Write

```text
z_(a,j)       = coordinate_j(ell_s(g_a)),
omega_(i,a,j) = coordinate_j(ell_s(a_(i,a))).          (2)
```

The logarithmic derivative is a differential-rational group homomorphism because `G` is
commutative.  Equivariance and (1) therefore give

```text
sigma_i(z_(a,j)) = z_(a,j) + omega_(i,a,j).             (3)
```

Define the simultaneous source boundary

```text
Q_Sigma(K) = K^I / {(tau_i(k)-k)_i : k in K},
V_Sigma(K) = Q_Sigma(K) tensor_(C[D]) C(D).             (4)
```

## Theorem A: logarithmic linearization preserves all differential rank

For every finite set `S` of observable labels, let

```text
F_S = K<coordinates of g_a : a in S>_D,
E_S = K<z_(a,j) : a in S, 1 <= j <= d>_D.
```

Then

```text
dtrdeg_K F_S = dtrdeg_K E_S.                            (5)
```

### Proof

Every coordinate of `ell_s(g_a)` is differential rational in the coordinates of `g_a`, so
`E_S subset F_S`.  Conversely, each `g_a` is a solution over `E_S` of the first-order algebraic
differential system

```text
ell_s(Y) = ell_s(g_a).                                  (6)
```

Thus every coordinate of `g_a` is differentially algebraic over `E_S`; hence `F_S/E_S` is
differentially algebraic and (5) follows.  This argument is independent of genericity of the
points.

## Theorem B: complete source-boundary rank formula

For every finite `S`,

```text
dtrdeg_K F_S
  = dim_(C(D)) span{[omega_(a,j)] : a in S, 1 <= j <= d}
      in V_Sigma(K).                                    (7)
```

Equivalently, the full coordinate family of the `g_a`, `a in S`, is differentially dependent
beyond rank `r` exactly to the extent that the boundary classes in (7) have linear rank `r`.
In particular, it is differentially dependent if and only if there are operators

```text
P_(a,j)(D) in C[D], not all zero,
```

and one `k in K` such that for every source direction `i`,

```text
tau_i(k)-k
  = sum_(a,j) P_(a,j)(D) omega_(i,a,j).                 (8)
```

### Proof

Equation (3) places the scalar coordinate family `z_(a,j)` under the arbitrary-family additive
Ostrowski theorem.  That theorem identifies every differential dependence among the `z_(a,j)`
with exactly one simultaneous coboundary relation (8), and identifies every subfamily rank with
the dimension of the corresponding span in (4).  Theorem A transfers that rank, subset by
subset, from the logarithmic coordinates back to the `G`-valued points.  This proves (7) and (8).

Changing the `C`-basis of `Lie(G)` applies an invertible constant matrix to all coordinates, so
the rank in (7) is intrinsic.

## Corollary: the sharp kernel is not a hidden HT reservoir

Let

```text
G^sharp = ker(ell_s).
```

Every point of `G^sharp` satisfies the first-order algebraic differential equation
`ell_s(Y)=0`, hence is differentially algebraic over the field of definition.  More generally,
every fibre of `ell_s` is a differential-algebraic torsor under `G^sharp` and has differential
transcendence degree zero over its image point.  Therefore:

```text
all hypertranscendental rank of a commutative D-group source primitive
is visible in its logarithmic source boundary; none is stored in G^sharp. (9)
```

The sharp kernel may retain finite-rank model-theoretic, isogeny, or embedding information.  It
cannot supply an additional hypertranscendental-capacity term.

## Linearization-horizon dichotomy

The theorem gives a sharp boundary for the proposed unified theory.

`[NO-GO]` A finite-dimensional commutative algebraic `D`-group cannot produce genuinely nonlinear
hidden hypertranscendence.  Its nonlinear group geometry and sharp fibres are
differential-algebraic decoration over a complete linear source-boundary invariant.

`[POSITIVE THEOREM]` This is not merely a failure: every such presentation admits an exact and
intrinsic nonlinear-to-linear collapse (7), for arbitrary noncommuting source families and every
finite subfamily simultaneously.

Consequently, any hypertranscendental phenomenon not classified by (7) must cross at least one
of the following horizons:

1. no faithful finite-dimensional commutative `D`-group presentation exists;
2. the logarithmic derivative has nontrivial adjoint twisting because the group is
   noncommutative;
3. the correct envelope is genuinely infinite-dimensional or pro-algebraic;
4. the source action is not by base-field increments.

This locates the next unknown object: it is not a mysterious extra radical inside the
commutative theory, but the obstruction to commutative finite-dimensional logarithmic
linearization itself.

## First curved theorem: the flat-holonomy case is proved and formalized

`[PROVED HERE] [FORMALIZED]` The successor conjecture's flat case is now a theorem, not a
conjecture.  Model the noncommutative logarithmic source law as an **affine source local system**

```text
sigma_i(z_p) = sum_q M_(i,pq) z_q + omega_(i,p),      M_(i,pq), omega_(i,p) in K,   (31a)
```

whose linear part is the adjoint action.  Call the local system **trivializable** when the
cocycle equation

```text
sum_r tau_i(P_(pr)) M_(i,rq) = P_(pq)                                              (31b)
```

has an invertible base-valued solution `P` — that is, when the adjoint holonomy is trivial.

Then `formal/GaloisForLFunctions/HTGeometry/TwistedSourceBoundary.lean` proves,
unconditionally and axiom-clean:

- **`gauge_shift`** — the gauge transform `P z` of a trivializable affine family satisfies the
  *flat* additive source law with increments `tau_i(P) omega_i`;
- `gaugeFamily_mem_adjoin`, `eq_gauge_combination`, `mem_adjoin_gaugeFamily` and
  **`differentialAdjoin_gaugeFamily`** — an invertible base gauge generates the same differential
  field, so **`eRk_gaugeFamily`**: it does not move the differential rank;
- **`twisted_differentialIndependent_iff`** — the curved source-boundary criterion in the flat
  case: the gauged family is differentially independent exactly when the boundary classes of the
  gauged increments are independent over `C[D]`;
- **`twisted_eRk_eq_rank_span_boundaryClass`** — the curved rank law in the flat case: the
  differential rank of the *original* affine family equals the rank of the span of the boundary
  classes of its gauged increments;
- `flat_shift_of_identity`, `identity_cocycle` — the commutative theory is exactly the identity
  gauge of the curved one, which is the card's claim that the commutative theorem is the flat
  trivial-adjoint case.

### The gauge groupoid and the diagonal reduction

`formal/GaloisForLFunctions/HTGeometry/TwistedGaugeAction.lean` puts the flat theorem inside the
gauge groupoid of the local system.  A base-valued invertible `P` acts on the datum by

```text
z |-> P z,     omega_i |-> tau_i(P) omega_i,     M_i |-> tau_i(P) M_i Q,   Q = P^(-1).   (31c)
```

- **`gaugeLinearPart`**, **`gauge_shift_general`** — the gauge transform of an affine family is
  again affine, with linear part the twisted conjugate `(31c)` and increment the source translate.
  The proof rewrites the observables through the inverse gauge, so the new linear part appears as
  `tau_i(P) M_i Q` rather than as a formal conjugation;
- **`gaugeLinearPart_eq_one_of_cocycle`** — a gauge solving `(31b)` is exactly one carrying the
  local system to the identity: the flat case is the gauge orbit of the trivial local system;
- **`gauge_shift_scalar_of_diagonal`** — if a gauge carries the local system to a *diagonal* one,
  every gauged coordinate satisfies a scalar affine source law
  `sigma_i(y_p) = m_(i,p) y_p + omega'_(i,p)`.  So for a diagonalizable adjoint local system the
  curved rank problem is the rank-one twisted problem, one coordinate at a time;
- `gauge_shift_flat_of_cocycle` — the flat law again, now as the unit-diagonal case.

### Homogeneous diagonal twists are flat after logarithmic differentiation

`formal/GaloisForLFunctions/HTGeometry/TwistedScalarLogDerivative.lean` closes the diagonal case
when the affine part vanishes.  For a homogeneous scalar twisted observable
`sigma_i(y) = m_i y`, the logarithmic derivative shifts *additively*:

```text
sigma_i(y'/y) = y'/y + (m_i)'/m_i.                                              (31d)
```

- **`logDerivFamily`**, **`logDerivTwist`**, **`logDerivFamily_shift`** — `(31d)` for a whole
  family, from the corpus lemma `ringEquiv_deriv_div_self_of_mul`.  No cocycle equation and no
  diagonalizability of a nonconstant local system is needed: the twist is absorbed by the
  logarithm;
- **`differentialClosure_logDerivFamily`**, **`eRk_logDerivFamily`** — the passage costs no
  differential rank, because an element and its logarithmic derivative are mutually differentially
  algebraic (`raw_logCoordinate_mutuallyDifferentialAlgebraic`), so the two families have the same
  differential closure and the same matroid rank;
- **`twistedDiagonal_differentialIndependent_iff`** — the curved source-boundary criterion for a
  homogeneous diagonal family: differential independence of the family is linear independence over
  `C[D]` of the boundary classes of the *logarithmic derivatives of the twists*;
- **`twistedDiagonal_eRk_eq_rank_span_boundaryClass`** — the curved rank law for the same class:
  the differential rank of the family itself equals the `C[D]`-rank of the span of those classes.

So the boundary data of a homogeneous diagonal curved family is `ell(m_(i,p))`, and the entire
flat theory computes its rank verbatim.

### Inhomogeneous diagonal data with a base particular solution

`formal/GaloisForLFunctions/HTGeometry/TwistedInhomogeneousReduction.lean` removes the affine part
whenever the affine law has a solution in the base field.  If `b_p` in `K` satisfies the same
scalar law, `tau_i(b_p) = m_(i,p) b_p + omega_(i,p)`, then

```text
y_p - b_p   transforms by   sigma_i(y_p - b_p) = m_(i,p) (y_p - b_p).                (31e)
```

- **`baseTranslate`**, **`baseTranslate_shift`** — `(31e)`;
- **`differentialAdjoin_baseTranslate`**, `differentialClosure_baseTranslate`,
  **`eRk_baseTranslate`** — subtracting base elements changes neither the generated differential
  field nor the matroid rank, because all jets of a base element are base elements
  (`differentialAdjoin_addOfJetsInBase`);
- `base_solution_zero`, `base_solution_one_iff` — the homogeneous case is `omega = 0`, and for the
  unit twist the base equation is exactly the flat coboundary condition `tau_i(b_p) - b_p =
  omega_(i,p)`, so `(31e)` contains the flat statement;
- **`twistedInhomogeneous_differentialIndependent_iff`**,
  **`twistedInhomogeneous_eRk_eq_rank_span_boundaryClass`** — the criterion and the rank law for
  an inhomogeneous diagonal family, stated for the original family `y`.

### The assembled curved rank law for a diagonalizable local system

`formal/GaloisForLFunctions/HTGeometry/DiagonalizableCurvedRankLaw.lean` composes the three
reductions — gauge, base translation, logarithmic derivative — each of which preserves the
differential matroid rank (`eRk_gaugeFamily`, `eRk_baseTranslate`, `eRk_logDerivFamily`):

- **`diagonalizableCurved_eRk_eq_rank_span_boundaryClass`** — if a base gauge `P` diagonalizes the
  adjoint local system with entries `m_(i,p)`, and the gauged increments `gaugeIncrement` have a
  base particular solution, then the differential rank of the *original* observables `z` equals the
  `C[D]`-rank of the span of the boundary classes of `ell(m_(i,p))`;
- **`diagonalizableCurved_differentialIndependent_iff`** — the matching independence criterion.

### Blocks, base change, and the first non-diagonalizable case

`formal/GaloisForLFunctions/HTGeometry/InvariantSubDatum.lean` splits a datum along an invariant
block `S` of indices:

- **`invariant_shift_restrict`** — a block closed under the adjoint local system carries its own
  affine source datum, with the restricted matrix and increments; `invariant_diagonal_restrict`;
- **`eRk_restrict_le`** — differential rank is monotone along the restriction, so every invariant
  block bounds the rank of the whole family from below;
- **`enlargedIncrement`**, **`triangular_shift_enlarged`** — off the block, a datum which is
  diagonal on the complement satisfies a scalar affine law whose increment is
  `sum_(q in S) M_(i,p,q) z_q + omega_(i,p)`: no longer a base element;
- **`enlargedIncrement_mem_adjoin`** — that increment lies in the differential field generated over
  `K` by the block observables, which is exactly the coefficient field the flat theory now needs.

`formal/GaloisForLFunctions/HTGeometry/SourceBoundaryBaseChange.lean` supplies that field:

- **`restrictSource`**, `restrictSource_algebraMap`, **`restrictSource_fixesConstants`**,
  **`restrictSource_deriv`** — a source automorphism restricts to any stable intermediate field,
  and all the structural hypotheses of the master law descend from the ambient field;
- **`differentialIndependent_iff_linearIndependent_boundaryClass_baseChange`** — **the master
  source-boundary law holds verbatim over any derivation-closed source-stable intermediate field.**
  Nothing in the law needed the coefficient field to be the original base;
- `algebraMap_C_deriv_eq_zero_of_base`, `intermediateField.instIsScalarTower`.

`formal/GaloisForLFunctions/HTGeometry/SourceStableDifferentialAdjoin.lean` certifies stability:

- **`mapsTo_differentialAdjoin`** — an automorphism which preserves the base, commutes with the
  derivation and moves every generator inside the generated differential field maps that whole
  field into itself (adjoin induction through the jets);
- `ringEquiv_symm_deriv`, `ringEquiv_symm_algebraMap`,
  **`sourceStable_mem_differentialAdjoin_iff`** — both directions of stability, hence a legitimate
  new base;
- the instance `differentialAdjoin.instDifferentialAlgebraAmbient`, which makes a generated
  differential field a differential algebra inside the ambient field.

`formal/GaloisForLFunctions/HTGeometry/TriangularSourceBoundary.lean` assembles the first
non-diagonalizable case:

- **`blockField`**, **`blockIncrement`**, `blockField_stable`;
- **`unipotentTriangular_differentialIndependent_iff`** — *a unipotent triangular datum is flat
  over the differential field of its invariant block*: the complementary observables are
  differentially independent over that field exactly when the boundary classes of their enlarged
  increments are linearly independent over the constant-coefficient differential operators.  The
  curved obstruction has moved from the local system into the coefficient field;
- **`unipotentTriangular_differentialIndependent_of_linearIndependent`** — the hypertranscendence
  payoff: independence of those boundary classes makes the complementary observables differentially
  independent already over the *original* base, by restriction of scalars along `K ⊆ blockField`;
- **`unipotentTriangular_differentialIndependent_sumElim`** — the whole family: a block independent
  over the base plus boundary classes independent over the block field give differential
  independence of every observable at once.

The last step uses `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentTower.lean`:

- `differentialJetSet_range`, **`differentialIndependent_sumElim`** — *differential independence is
  additive along a tower*: a base-independent family together with a family independent over the
  differential field it generates is jointly independent over the base.  This is
  transcendence-degree additivity in the differential setting, obtained from the algebraic tower
  law for the jet families through `IntermediateField.algebraicIndependent_adjoin_iff`.

The constant field does not move under the base change: every statement above is proved with the
same `C`, because the constant hypotheses of the master law are conditions on the ambient field `L`
(`hfixed`, `hCfixed`) and on `C` itself, and `algebraMap_C_deriv_eq_zero_of_base` transports the
remaining one.

The cardinal form of the same tower is
`formal/GaloisForLFunctions/HTGeometry/DifferentialRankTower.lean`:

- `transcendental_of_diffIndepOn`, **`diffIndepOn_union_of_diffIndepOn_adjoin`** — the set form of
  the tower law;
- **`isBasis_union_of_isBasis`** — a basis of `X` over `F` and a basis of `Y` over
  `differentialAdjoin F X` union to a basis of `X ∪ Y` over `F`.  Independence is the tower law;
  spanning is idempotence of the differential closure applied to `X ∪ J ⊆ closure (I ∪ J)`;
- `disjoint_of_isBasis` — the two bases are disjoint, because a member of the second is
  transcendental over the field the first set generates while a member of the first lies in it;
- **`eRk_union_eq_eRk_add_eRk`** — **differential rank is additive along a tower**:

```text
eRk_F (X ∪ Y) = eRk_F X + eRk_(F<X>) Y.                                         (31f)
```

Mathlib has no contraction-rank lemma for matroids, so `(31f)` is proved by exhibiting the union of
two bases rather than by a matroid minor computation.  Applied to the two blocks of a triangular
datum it turns the block criteria into a single rank statement for the whole family.

### The general case: an arbitrary local system with a fundamental matrix

`formal/GaloisForLFunctions/HTGeometry/FundamentalMatrixSourceGauge.lean` removes every structural
assumption on the adjoint local system.  If the homogeneous system has an invertible solution
matrix `Y` in the ambient field, then

```text
sigma_i(Y) = M_i Y  and  sigma_i(z) = M_i z + omega_i
  ==>  sigma_i(Y^(-1) z) = Y^(-1) z + Y^(-1) M_i^(-1) omega_i.                  (31g)
```

- `baseMat`, `baseMat_mul`, `baseMat_one`, `map_sigma_mul`, `map_sigma_one`, `sigma_mulVec` — the
  source action on matrices;
- **`map_sigma_fundamental_inv`** — the inverse fundamental matrix transforms by the inverse local
  system, `sigma_i(Y^(-1)) = Y^(-1) M_i^(-1)`, proved by uniqueness of two-sided inverses;
- **`fundamental_shift`** — `(31g)`;
- `map_baseMat_sigma_symm`, `map_sigma_symm_map_sigma`, **`map_sigma_symm_fundamental`**,
  **`map_sigma_symm_fundamental_inv`** — the same in the inverse source direction, with the base
  matrices transported by `tau_i^(-1)`.

`formal/GaloisForLFunctions/HTGeometry/FundamentalMatrixSourceBoundary.lean` assembles it:

- `fundamentalGenerators`, `fundamentalField`, entry-membership lemmas;
- **`fundamentalField_stable`** — the differential field generated by `Y` and `Y^(-1)` is stable
  under every source direction and its inverse, so it is a legitimate new base;
- `fundamentalIncrement` — the increments of `(31g)` as elements of that field;
- **`fundamental_differentialIndependent_iff`** — **the curved source-boundary criterion for an
  arbitrary local system**: over the fundamental field, the flattened family is differentially
  independent exactly when the boundary classes of its increments are `C[D]`-independent;
- **`differentialAdjoin_fundamentalFlatten`**, **`eRk_fundamentalFlatten`** — the flattening is an
  invertible base-linear change, so it costs no rank over that field;
- **`fundamental_eRk_union`** — with `(31f)`:

```text
eRk_K (entries(Y, Y^(-1)) ∪ z) = eRk_K entries(Y, Y^(-1)) + eRk_(K<Y>) (Y^(-1) z).   (31h)
```

No property of the local system is used — not diagonalizability, not a triangular filtration, not
irreducibility.  The only input is an invertible solution matrix in the ambient field, which is
exactly what a Picard–Vessiot extension supplies.  The diagonalizable and unipotent-triangular
results above are the special cases where that matrix can be taken base-valued or block-structured.

### What the fundamental matrix costs, and that it costs nothing else

`formal/GaloisForLFunctions/HTGeometry/FundamentalMatrixUniqueness.lean`:

- `baseMat_injective`, `baseMat_eq_of_mul_eq` — a base matrix is determined by its image, and an
  invertible right factor cancels;
- **`fundamental_integrability`** — *existence of a fundamental matrix is not free*: when the source
  directions commute, it forces the flat-connection cocycle condition

```text
tau_i(M_j) M_i = tau_j(M_i) M_j                                                 (31i)
```

  on the adjoint local system.  This is the integrability condition of
  `GaloisForLFunctions.cocycleCondition` and is exactly the price of `(31g)`;
- `invariant_entry_mem`, **`fundamental_ratio_invariant`** — two fundamental matrices of the same
  local system differ on the right by a matrix fixed by every source direction, hence by a matrix of
  constants;
- **`fundamentalField_eq_of_fundamental`** — consequently `K⟨Y, Y^(-1)⟩` does not depend on which
  fundamental matrix is chosen, so `(31g)`, `(31h)` and the criterion are *intrinsic* to the datum.

`formal/GaloisForLFunctions/HTGeometry/FundamentalMatrixNonexistence.lean` shows the hypothesis is
not removable:

- `eq_zero_of_eq_neg`, `not_invertible_of_eq_neg`, `baseMat_neg_one`;
- **`not_exists_fundamental_of_neg_one`** — if a source direction acts trivially on the ambient
  field and the local system is `-1` in that direction, then `Y = -Y`, so `Y = 0` and no invertible
  solution matrix exists — *in every field of characteristic zero, whatever else the extension
  contains*.  The integrability condition `(31i)` holds vacuously here, so `(31i)` is necessary but
  not sufficient.

What this settles and what it does not: the mere *presence* of an adjoint action does not break
the linear source-boundary law — only nontrivial adjoint holonomy can, and the holonomy is fully
absorbed by a fundamental matrix.  The curved rank problem is closed, relative to the fundamental
matrix, for **every** affine source datum whose homogeneous part is solvable in the ambient field,
with the same constant field `C` throughout, in both the independence and the cardinal form, and
the answer does not depend on which fundamental matrix is used.

The only remaining question is not about the local system but about the ambient field: does `L`
contain a fundamental matrix?  That question is settled negatively in general —
`not_exists_fundamental_of_neg_one` exhibits a local system with no invertible solution matrix in
any field of characteristic zero.  So "the homogeneous part is solvable in `L`" is an irreducible
hypothesis of the curved law, not a step still to be discharged; over a field it is exactly the
condition under which a Picard–Vessiot object is a field rather than a pseudo-field.

## Bold successor: curved source-boundary conjecture

`[CONJECTURE]` Every finite-source hypertranscendental observable has a minimal differential
Tannakian source envelope.  Its logarithmic derivative is an affine local system

```text
sigma_i(z) = Ad(a_i) z + ell_s(a_i),                    (10)
```

and its complete differential-algebraic polymatroid is determined by a localized twisted
source-cohomology object together with the Tannakian tensor relations of the adjoint local
system.  The commutative theorem is exactly the flat trivial-adjoint case.

The universal nonlinear invariant is then the adjoint holonomy/curvature of (10), not an
additional collection of jets.  Continuation and monodromy should be direct realizations of this
holonomy; positivity, spectral completeness, and boundary-condition uniqueness should be
polarized realization conditions on the same twisted object.

**Falsifier:** two faithful minimal source envelopes with the same twisted source-cohomology and
the same Tannakian tensor relations but different differential-algebraic rank functions, or a
finite-source observable admitting no minimal envelope even up to pro-algebraic equivalence.

## Novelty gate

Classical inputs:

- Buium--Pillay algebraic `D`-groups and logarithmic differential equations;
- the homomorphism identity for the logarithmic derivative of a commutative `D`-group;
- the fact that `G^sharp` is the kernel of a first-order logarithmic differential equation;
- one-operator Kolchin--Ostrowski and parameterized differential-Galois rank theorems.

New candidate surface:

- an arbitrary, possibly noncommuting family of compatible source automorphisms;
- one simultaneous base coboundary in every source direction;
- the complete rank function for every finite family of `G`-valued points;
- the exact elimination of the sharp kernel as a possible hidden HT-capacity layer.

No checked source states (7)--(9) in this arbitrary-source form.  This is affirmative evidence,
not a proof of absence; specialist and bibliographic review remain required.

## Significance and anti-theatre gate

- `[PASS]` The theorem strictly contains the split `G_a^r x G_m^s` theorem.
- `[PASS]` It classifies a complete differential polymatroid, not one dependence.
- `[PASS]` It kills a proposed radical layer and replaces it with a stronger exact theorem.
- `[PASS, PROVISIONAL]` The arbitrary-source theorem surface was not located in the parent
  literature.
- `[PASS]` A concrete analytic example whose source datum has nontrivial adjoint holonomy:
  `formal/GaloisForLFunctions/HTGeometry/ExponentialShiftHolonomyWitness.lean`.  Inside the
  meromorphic differential field of the plane, `exp(z + 1) = e · exp(z)`, so for the shift by one
  the adjoint local system is the scalar `e`.  **`expLocalSystem_holonomy_nontrivial`** — no base
  gauge over the constants carries it to the identity, because a constant gauge acts trivially on a
  scalar local system while `e ≠ 1`.  **`expFundamental_isFundamental`** — the exponential is its
  own fundamental matrix, so the curved theory of `(31g)`--`(31h)` applies to it verbatim.
- `[FORMALIZED]` Theorem A `(5)`, Theorem B `(7)`--`(8)` in polymatroid form, and the
  sharp-kernel corollary `(9)` are formalized unconditionally and are axiom-clean; the `D`-group
  layer is built here because algebraic `D`-groups are absent from current Mathlib.
- `[FAIL if oversold]` The proof is short once classical `D`-group logarithmic geometry and the
  project additive theorem are imported.  It is significant progress, not a Fields-Medal result.

## RH pressure test `[CONJECTURE]`

If zeta's relevant source envelope were commutative and finite-dimensional, Theorem B would force
all of its hypertranscendental capacity into an ordinary linear boundary module; a genuinely
nonlinear common obstruction spectrum could not come from a hidden Manin/sharp layer.  The live
hypothesis is therefore that the common RH obstruction, if real, is the polarized degeneracy
spectrum of a nontrivial twisted/pro-source envelope.  This is a research hypothesis, not an RH
result.

## References checked

- A. Buium, *Differential Algebraic Groups of Finite Dimension*, 1992.
- D. Bertrand, *Algebraic D-groups and non-linear differential Galois theory*, 2009 notes.
- D. Bertrand and A. Pillay, *A Lindemann--Weierstrass theorem for semi-abelian varieties over
  function fields*, JAMS 23 (2010), 491--533.
- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*,
  Math. Ann. 342 (2008), 333--377.

## Lean formalization plan and ledger

The theorem splits into five layers.  Mathlib has no algebraic `D`-groups, so the `D`-structure is
built here; the arbitrary-family additive source theorem is already corpus-owned in
`AutomorphismFamilyOstrowski` and `SourceLogarithmicBoundary` and is used as the linear engine.

1. **The `D`-group layer and Theorem A.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/CommutativeDGroupObservable.lean`:
   - `DGroupPresentation` — a commutative algebraic `D`-group presented by its points, their
     coordinates and the algebraic logarithmic derivative.  Three laws: the logarithmic derivative
     is a group homomorphism (commutativity), each logarithmic coordinate is differential rational
     in the coordinates, and each coordinate derivative is rational in the coordinates and the
     *jets* of the logarithmic coordinates.  The last law is exactly the first-order system
     `(6)` solved for `Y′`, which is what a `D`-structure supplies;
   - `differentialJetSet_mono`, `differentialAlgebraicOver_of_mem_intermediateField`,
     `coordFamily`, `ellFamily`, `ell_mem_differentialAdjoin_coordFamily` — the inclusion
     `E_S ⊆ F_S`;
   - **`differentialAlgebraicOver_coordFamily`** — the substantial half of Theorem A: every
     coordinate of a point of the family is differentially algebraic over the differential field
     generated by the logarithmic coordinates of the family.  The coordinates generate a finite
     rational state field over that base which differentiates into itself, so the corpus theorem
     `differentialAlgebraicOver_of_mem_finiteGeneratorState` applies;
   - **`differentialClosure_coordFamily_eq_ellFamily`** — equation `(5)`: the two families have
     the same differential-algebraic closure;
   - **`eRk_coordFamily_eq_ellFamily`** — the rank form of `(5)`, through the differential
     matroid;
   - **`differentialAlgebraicOver_coords_of_ell_eq_zero`** — the corollary `(9)`: every coordinate
     of a sharp point is differentially algebraic over the base, so the sharp kernel stores no
     hypertranscendental capacity.

2. **The source layer and Theorem B, criterion form.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/DGroupSourceBoundary.lean`:
   - `DGroupSourceData` — an equivariant action of the source family on the points together with
     the translating points of `(1)` and their logarithmic coordinates over the base;
   - **`DGroupSourceData.sigma_ellFamily`** — equation `(3)`: the multiplicative source recurrence
     of the points becomes an additive source recurrence of the logarithmic coordinates, because
     the logarithmic derivative of a commutative `D`-group is a homomorphism;
   - **`dGroupSource_ellFamily_differentialIndependent_iff`** — equation `(8)`: the logarithmic
     coordinate family is differentially independent exactly when no nonzero finite differential
     character of the source increments is one simultaneous base coboundary.  This is the
     arbitrary-family additive theorem of the corpus applied to `(3)`;
   - `dGroupSource_eRk_coordFamily_eq` — the transfer of the answer back to the points.

3. **The source-boundary module `(4)`.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/SourceCoboundaryModule.lean`:
   - `derivC`, `derivPi` — the derivation as an endomorphism linear over the constants, and its
     coordinatewise action on source cochains;
   - `SourceCochain`, `BaseCochain` — `K^I` and `K` as modules over the constant-coefficient
     differential operators `C[D]`, through `Module.AEval'`;
   - `coboundC`, **`coboundPoly`** — the simultaneous coboundary map is `C[D]`-linear, because the
     source automorphisms commute with the derivation and fix the constants;
   - **`sourceBoundaryModule`**, `boundaryClass` — equation `(4)`: source cochains modulo
     simultaneous coboundaries;
   - **`boundaryClass_eq_zero_iff`** — a cochain is a boundary exactly when it is a simultaneous
     coboundary;
   - `aeval_derivPi_apply`, `boundaryClass_add`, `boundaryClass_smul`, `boundaryClass_sum` and
     **`linearIndependent_boundaryClass_iff`** — the boundary classes of a family of increments are
     linearly independent over `C[D]` exactly when no nonzero family of operators `P_{a,j}(D)`
     makes `∑ P_{a,j}(D) ω_{i,a,j}` one simultaneous coboundary.  This is `(8)` verbatim.

   `formal/GaloisForLFunctions/HTGeometry/SourceCoboundaryOperatorBridge.lean` supplies the
   dictionary between the two presentations of a finite differential character:
   - `polyFinsupp`, `finsuppPoly` and their round trips;
   - `pow_derivC_apply`, **`aeval_derivC_sum`** — an operator acts as its jet character;
   - `jetCharacterOfOperators`, `operatorsOfJetCharacter`, `operatorSum_eq_jetSum` and
     **`operator_criterion_iff_jet_criterion`** — the jet-character form used by the corpus source
     theorem and the operator form used by the boundary module are the same condition.

4. **The rank law `(7)`.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/DGroupSourceRankLaw.lean`:
   - **`differentialIndependent_iff_linearIndependent_boundaryClass`** — the master law: a family
     of observables shifting by base increments in every source direction is differentially
     independent exactly when the boundary classes of those increments are linearly independent
     over `C[D]`;
   - **`dGroup_differentialIndependent_iff_linearIndependent_boundaryClass`** and
     **`dGroup_subfamily_differentialIndependent_iff`** — the same for a commutative `D`-group
     family and for every reindexing of it, which is the polymatroid form of `(7)`: the two rank
     functions have the same independent sets;
   - **`dGroup_sourceBoundary_universality`** — the assembled statement: equal differential rank of
     the points and their logarithmic coordinates, together with the boundary-class description of
     independence for every subfamily.

5. **Instances.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/DGroupBasicInstances.lean`:
   - **`additiveDGroup`** — the additive group, logarithmic derivative `x ↦ x′`;
   - **`multiplicativeDGroup`** — the multiplicative group, logarithmic derivative `x ↦ x′/x`.
   Both satisfy the presentation laws, so the theorems above are non-vacuous and contain the
   classical additive and multiplicative source theorems.

6. **Products and the split case.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/DGroupProduct.lean`:
   - `range_subset_range_append_left`, `range_subset_range_append_right`;
   - **`DGroupPresentation.prod`** — the product of two presentations, coordinates and logarithmic
     coordinates concatenated; both rationality laws hold blockwise;
   - **`DGroupSourceData.prod`** — source data multiply;
   - `additiveMulDGroup` — the split group `G_a × G_m`.  With the two one-dimensional
     presentations this makes every split group an instance, so the theorem literally contains the
     split `G_a^r × G_m^s` statement.

7. **Intrinsicality of the rank.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/DGroupBasisChange.lean`:
   - `algebraMap_C_mem`, `deriv_finsetSum`, `differentialJet_finsetSum`,
     `differentialJet_algebraMap_C_mul` — constants pass through jets;
   - **`DGroupPresentation.basisChange`** — an invertible constant matrix applied to the
     logarithmic coordinates gives another presentation with the same coordinates; the first-order
     system is recovered through the inverse matrix, whose entries are constants and therefore
     commute with the derivation;
   - **`differentialClosure_ellFamily_basisChange`** — the card's intrinsicality claim: changing
     the basis of the Lie algebra does not change the differential closure, hence not the rank in
     `(7)`.  Both closures are the closure of the unchanged coordinate family.

   The fibre statement of the corollary section is also closed:
   **`DGroupPresentation.differentialAlgebraicOver_coords_singleton`** — every coordinate of a
   point is differentially algebraic over the differential field generated by that point's own
   logarithmic coordinates, so every fibre of `ell_s` — a torsor under the sharp kernel — has
   differential transcendence degree zero over its image point.

8. **The cardinal form of `(7)`.**  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/SpanRankMaximalSubfamily.lean` supplies the
   linear-algebra half over an arbitrary commutative domain:
   - `exists_smul_mem_of_mem_span` — if every generator has a nonzero multiple in a submodule, so
     does every element of the span;
   - **`rank_span_eq_mk_of_torsion_generators`** — the rank of a span through an independent core:
     the quotient by the core's span is torsion, hence of rank zero, and rank is additive along the
     quotient;
   - **`exists_maximal_linearIndepOn_finset`** — a family indexed by a finite type has a
     cardinality-maximal independent subfamily; every member has a nonzero multiple in its span,
     and adjoining any outside index destroys independence.

   `formal/GaloisForLFunctions/HTGeometry/SourceBoundaryRankCardinal.lean` assembles it:
   - **`eRk_eq_rank_span_boundaryClass`** — for a finite family of observables shifting by base
     increments, the differential matroid rank and the `C[D]`-rank of the span of the boundary
     classes are the same natural number.  One maximal independent subfamily computes both: on the
     linear side by the torsion-quotient argument, on the differential side because the source
     law makes it a differential-matroid basis of the family;
   - **`dGroup_eRk_coordFamily_eq_rank_span_boundaryClass`** — equation `(7)` itself: for a family
     of points of a commutative algebraic `D`-group, the differential rank of the coordinates
     equals the rank of the span of the boundary classes of their logarithmic source increments.

   Mathlib has no linear matroid (`Matroid.ofFun` does not exist), so the comparison is made
   through these two rank computations rather than by identifying two matroids.  The
   `dim_{C(D)}` of the card is this `C[D]`-rank, by `IsLocalization.rank_eq`.

## Log

- 2026-07-15 -- The commutative `D`-group conjecture collapsed to the exact rank theorem; the
  proposed character-invisible HT radical was ruled out and replaced by the linearization-horizon
  dichotomy.
