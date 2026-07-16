# Hypertranscendental selection is a capacity-descent Postnikov tower

- **ID:** `hypertranscendental-capacity-descent-postnikov-tower`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / GRADED GLOBAL SELECTION OBJECT
- **Scientific status:** `[CONJECTURE] [DEGREE-ONE SEED PROVED] [FIELDS-SCALE OPEN CORE]`
- **Statement:** Source-specific HT selection is governed not by one universal obstruction class,
  but by a Postnikov tower whose degree-zero layer controls active capacity, degree-one layer
  controls additive sewing, and higher layers record nonabelian associators and polarized descent.

## Why a tower is forced

Three attacks now determine three distinct levels.

1. Constraint support is universal: every finite simplicial spectrum occurs.
2. Active palettes exactly classify finite realizability and minimum dimension, but a residual
   family of sources realizes each palette: support plus activity is source-blind.
3. A universal degree-two selection gerbe is false: the all-depth pair-face class has a complete
   degree-one additive sewing law.
4. Intrinsic analytic dimension does not bound the tower: boundary-wedge sources have `htDim=2`
   while their source-coherence projective dimension takes every value at least three.

Therefore the unified object cannot live at one fixed cohomological degree.  Its obstruction degree
must follow the categorical height of the local data.

## Degree-zero layer: capacity concentration `[PROVED]`

For a local quasi-Abelian carrier `X_A` with structural lattice `H_A`, quotient its maximal compact
complex subtorus:

```text
Act(X_A)=X_A/B_A.
```

The degree-zero defect is

```text
K_A=ker(H_A -> Act(X_A)).                                (1)
```

Complete HT orbit freedom forces `K_A=0`.  If `K_A!=0`, every observable has finite cyclic capacity
on a nonzero kernel subgroup, although all finite capacities may occur across different
observables.  If `K_A=0`, fixed-factor all-order jet interpolation produces a residual family of
observables attaining infinite orbit capacity.

This layer is classified exactly by `htDim=aqaDim`.

## Degree-one layer: pair-face sewing `[PROVED]`

For the generic mixed-constraint class with directions `tau_1,...,tau_d`, put

```text
C^0_pair=direct_sum_(i<j) A_(ij),
C^1_pair=direct_sum_(i<j<k) (A_(ijk) direct_sum A_(ijk)). (2)
```

For `D=(D_(ij))`, define on a triple `i<j<k`

```text
(d_pair D)_(ijk)
 = (p_(ij,ijk)D_(ij)-p_(ik,ijk)D_(ik),
    p_(ij,ijk)D_(ij)-p_(jk,ijk)D_(jk)).                   (3)
```

Then

```text
d_pair D=0
 iff the three pair pushforwards agree on every triple.   (4)
```

Hence the exact pair-face theorem becomes

```text
Comp_d=ker d_pair=H^0(C_pair^bullet),
Q_d/(Q_d intersection Mer_DA) ~= H^0(C_pair^bullet).      (5)
```

Every degree-one obstruction value `d_pair D` is concrete: it is the failure of the proposed local
pair observables to share one triptic restriction.  Vanishing is necessary and sufficient for
global realization modulo DA.  The triptic reciprocity theorem is exactly the one-triple
restriction of (4).

The positive private sectors survive inside `H^0`: for every pair `e`, the nonzero module

```text
Priv_e=intersection_(k notin e) ker p_(e,e+k)             (6)
```

embeds as a cocycle supported on `e`.  Thus degree-one sewing is complete but noncompressible.

## Higher layers `[CONJECTURE]`

For nonlinear local objects with noncommutative gauge automorphisms, pairwise comparison maps need
not compose strictly on triples.  Their associators form the next obstruction layer.  Iterated
coherence of those associators may require further stages.

> **[CONJECTURE -- CAPACITY-DESCENT POSTNIKOV PRINCIPLE]** Every regular source-minimal HT class has
> a canonical differential-birational Postnikov object `Sel_HT(F)` over its active constraint
> spectrum such that:
>
> 1. `pi_0` is the active capacity/stabilizer layer;
> 2. the first linearized `k`-invariant is the additive sewing differential;
> 3. the next `k`-invariant is the nonabelian comparison associator;
> 4. polarization is a homotopy-coherent transport reduction of the entire tower, not a scalar
>    sign attached at the end;
> 5. the tower is effective exactly when it reconstructs one pointed analytic HT source;
> 6. continuation, monodromy, positivity, spectral completeness, and boundary canonicity are
>    conservative realization images of successive layers of this same tower.

This formulation does not force every obstruction into the same degree or scalar group.  It claims
they are successive shadows of one structured global selection object.

## Exact first new theorem target

Upgrade (5) from a module isomorphism to a functorial descent theorem:

1. define `C_pair^bullet` independently of the ordering of directions;
2. prove naturality under deletion, permutation, and source refinement;
3. show the pair-face map is an isomorphism of differential-translation objects onto `H^0`;
4. identify private sectors as the local-support filtration of `H^0`;
5. prove the terminal residue is the augmentation of the same complex, not a separate invariant.

The point is not the elementary identity (4).  The candidate-new content is functoriality and the
identification of the already complete nonlinear differential matroid with the cohomology object of
one descent complex.

## First nonlinear target

Choose one nonlinear nonabelian HT class already possessing two genuine local realizations.  Build
its comparison 2-groupoid and prove that its associator class:

- is invariant under differential-birational source presentation;
- restricts to (3) after abelianization/linearization;
- vanishes exactly when the local active carriers reconstruct one analytic source;
- is detected by two independently constructed realization functors.

Without this target, the Postnikov language is only parent-theory decoration.

## Obstruction-chain dictionary `[CONJECTURE]`

```text
spectral incompleteness  = failure of faithfulness at pi_0 or a surviving linearized k-invariant;
continuation failure     = non-effectivity of a descent stage;
monodromy                = holonomy of the first nontrivial comparison stage;
positivity failure       = obstruction to polarized reduction of the tower;
boundary noncanonicity   = torsor of trivializations after obstruction vanishing.
```

The dictionary is testable only through constructed realization functors.

## Parent-theory and novelty boundary

Postnikov towers, obstruction theory, hypercohomology, Cech descent, gerbes, stacks, and differential
modules are parent theory.  The following are not novelty:

- writing compatibility as a kernel;
- calling a sequence of obstructions a Postnikov tower;
- assigning standard cohomological degrees to standard descent data.

The possible new mathematics is the canonical HT construction, the active capacity `pi_0`, the
proof that the pair-face differential is its first linearized `k`-invariant, reconstruction of the
analytic source from tower effectivity, and joint conservativity of genuinely different analytic
realizations.

## Anti-theatre gate

Retire or revise the tower if:

1. its stages depend on a chosen presentation rather than the source;
2. the pair-face specialization does not recover the exact quotient and nonlinear matroid;
3. a fixed existing derived or twistor category already supplies the whole tower unchanged;
4. higher stages add no strict realizability restriction;
5. effectivity fails to reconstruct a pointed analytic source;
6. realization comparisons remain analogies.
7. the tower is truncated using analytic dimension rather than a source-specific collapse law.

Every no-go must identify the lowest missing stage or prove that the tower truncates positively for
the source class under attack.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` Different RH proof chains may terminate at different nonzero stages
of the completed-zeta selection tower.  Critical zeros could be a common self-dual degeneracy
spectrum only after the tower and realization functors are constructed independently.  This
conjecture does not assert such a construction or prove RH.

## Lean boundary

The concrete pair differential (3), its zero/equality equivalence (4), permutation covariance, and
kernel description should be formalized once the exact finite indexing types are fixed.  Existing
`TelescopeIdeal`, `PairFacePrivateSector`, and differential-matroid modules supply the quotient and
private-sector algebra; no analytic statement should enter as an axiom.

## Gates

- [x] support universality established
- [x] active capacity degree-zero layer established
- [x] fixed-degree gerbe conjecture falsified by pair-face data
- [x] exact degree-one pair differential and cohomology statement proved on paper
- [x] positive private cocycles identified
- [x] no finite Postnikov-height bound follows from intrinsic HT dimension
- [x] rank-one polarization transport shown to collapse local orientation chambers
- [ ] formalize the functorial pair descent complex
- [ ] prove permutation/deletion/refinement naturality
- [ ] recover the terminal residue as augmentation
- [ ] build one nonlinear comparison 2-groupoid
- [ ] prove presentation invariance
- [ ] prove effectivity reconstructs one analytic source
- [ ] construct two jointly conservative realization functors
- [ ] complete literature and specialist novelty audit
