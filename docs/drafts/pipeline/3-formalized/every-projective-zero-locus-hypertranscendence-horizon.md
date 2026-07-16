# Every projective zero locus is a complete hypertranscendence horizon

- **ID:** `every-projective-zero-locus-hypertranscendence-horizon`
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION THEOREM / DIFFERENTIAL ALGEBRA / PROJECTIVE GEOMETRY
- **Scientific status:** `[LEAN-PROVEN] [NOVELTY PROVISIONAL] [SIGNIFICANCE PACKAGE IN PROGRESS]`
- **Paper lane:** *Before There Was Time: Holographic Universality and the Integrability Barrier*

## Theorem

Let `K` be a field, let `iota` and `eta` be finite types, and let

```text
P_j in K[c_i : i in iota]
```

be a finite family of homogeneous polynomials, with no common-degree hypothesis. There is an
explicit rational function field `L/K`, an `iota`-indexed family of derivations `delta_i`, and one
element `x in L` such that for every nonzero law vector `c`, with

```text
D_c = sum_i c_i delta_i,
```

one has the exact equivalence

```text
{x, D_c x, D_c^2 x, ...} is algebraically dependent over K
  iff
P_j(c)=0 for every j.                                      (1)
```

Consequently every projective algebraic zero locus defined by finitely many homogeneous equations
is the complete ordinary differential-algebraicity horizon of one observable under a finite linear
pencil of derivations. Outside the horizon, the entire infinite jet tower is algebraically
independent, not merely independent up to a prescribed finite order.

No commutativity of the basis derivations is asserted.

## Construction

For common degree `d`, ordered prefix states propagate freely to depth `d`. At that layer their
commutative collapse is the prescribed terminal polynomial vector `P(c)`. An equation-labelled
infinite word tail supplies a fresh disjoint generator block at every later depth. Thus

```text
D_c^(d+r) x = sum_(j,w:|w|=r) P_j(c)c_w y_(j,w).            (2)
```

If all `P_j(c)` vanish, the `d`-th jet is zero. If one survives, every later block is a nonzero
linear form on a fresh algebraically independent family, so all jets are algebraically independent.

For unequal degrees `d_j`, take

```text
D = 1 + sum_j d_j
```

and replace `P_j` by all `M P_j` with `deg M=D-d_j`. At a nonzero `c`, some coordinate is nonzero,
so all lifted products vanish exactly when `P_j(c)=0`. This reduction is also formalized.

## Lean surface

The final theorem is

```text
exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus
```

in
`formal/GaloisForLFunctions/HTGeometry/DirectionalProjectiveZeroLocusRealization.lean`.

Its proof depends on the unconditional modules:

- `AlgebraicIndependentDisjointLinearForms.lean`;
- `DirectionalProjectiveVarietyRealization.lean`;
- `DirectionalProjectiveCompleteRealization.lean`;
- `DirectionalWordPolynomialSurjectivity.lean`.

## Significance and anti-theatre gate

This is a genuine universal realization theorem, but universality statements have strong known
parents. Reineke proved that every projective variety is a quiver Grassmannian; Sidman--Smith gave
linear determinantal equations for projective schemes; Jorgensen realizes every projective variety
as a module rank variety. The free word construction also has a quiver presentation.

The result is not Fields-level merely because its carrier is new. Its potentially significant
content is the exact complete-hypertranscendence equivalence `(1)`, combined with:

1. pretemporal flat rigidity, which forces the horizon to be empty in every regular flat
   common-source realization;
2. the general principal-symbol factorization `J_symbol=m^T I`;
3. the commuting free-tail obstruction, which proves that abelian law spaces require non-free
   prolongation modules;
4. a future canonical Kähler reconstruction of the projective scheme, including multiplicities.

The emerging classification is therefore not simply “everything occurs,” but

```text
flat regular laws       -> empty horizon;
free noncommuting laws  -> every projective zero locus;
commuting laws          -> only integrably prolongable horizon modules.
```

## Novelty gate

Exact searches found no paper stating `(1)` for the varying-derivation ordinary
hypertranscendence locus of one field element. This is an absence-of-hit result, not a priority
claim. Dangerous parent theories remain quiver Grassmannians, determinantal representations, rank
varieties, recognizable series, jet degeneracy loci, and universal constructions in differential
algebra.

Primary comparison points:

- M. Reineke, *Every projective variety is a quiver Grassmannian* (2012),
  `https://arxiv.org/abs/1204.5730`;
- J. Sidman and G. Smith, *Linear determinantal equations for all projective schemes* (2011),
  `https://arxiv.org/abs/0910.2424`;
- D. Jorgensen, *Rank varieties over the generic hypersurface I* (2026),
  `https://arxiv.org/abs/2605.17736`.

## Physical interpretation `[CONJECTURE]`

Before a time direction is selected, projective law space records all linear combinations of
candidate derivations. The theorem says hypertranscendence alone imposes no topological selection
principle on the resulting holographic horizon: arbitrary projective zero-locus geometry can be
encoded by a free pretemporal observable algebra.

This is not a theorem that the physical universe realizes every projective geometry. It is the
opposite constraint: any physical restriction must enter through additional laws such as
commutativity, locality, gauge symmetry, positivity, or unitarity. The commuting obstruction proves
that at least one such restriction is mathematically substantive.

## RH impact

Projective horizon geometry by itself cannot distinguish the zeta/RH situation, because a free
differential field can engineer any finite homogeneous zero locus. An RH proof must use arithmetic
integrability or a canonical source, not the bare topology of a hypertranscendence discriminant.

## Verification

- [x] common-degree ordered-word coefficient surjectivity
- [x] exact finite-packet dependence theorem
- [x] exact complete-jet algebraic-independence equivalence
- [x] unequal-degree zero-locus-preserving lift
- [x] direct source checks
- [x] targeted module builds
- [x] terminal axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] independent expert priority audit
- [ ] canonical Kähler scheme reconstruction
