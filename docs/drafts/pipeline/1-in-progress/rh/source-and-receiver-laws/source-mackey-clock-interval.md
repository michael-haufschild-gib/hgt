# The source Mackey interval of a constrained hypertranscendental function

- **ID:** `source-mackey-clock-interval`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT TOPOLOGY / CROSS-REPRESENTATION FIELD OBJECT
- **Scientific status:** `[CLASSICAL MACKEY-ARENS PARENT] [HT SOURCE-DUAL CONJECTURE] [GAMMA MODEL] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `clock-descent-anomaly.md`
  - `self-dual-decorated-clock-boundary.md`
  - `../../../3-formalized/gamma-periodic-constraint-corona.md`
- **Statement:** The topology carried by a constrained HT source is not an arbitrary completion of
  its clock tower. The source constraint enlarges the finite-coordinate dual by infinite
  conormals. The weak-to-Mackey interval of this enlarged dual pair is the canonical topology
  interval in which different analytic obstruction theories can be compared.

## The forced dual enlargement

Let `Phi` be a linear source chart embedded in the infinite clock `P=K^N`. Let

```text
I = K^(N)                                                   (1)
```

be the finite-support coordinate covectors. The product clock topology on `Phi` is the weak
topology `sigma(Phi,I)`. Let `W subset Phi` be the homogeneous source tangent.

Assume `W` realizes arbitrary values on every finite coordinate set. Then `W` is dense for
`sigma(Phi,I)`, and every Hausdorff continuous linear observation annihilating `W` is zero. These
claims are Lean-formalized for the raw product clock.

Therefore a nonzero source conormal cannot lie in `I`. The source must provide an enlarged
separating dual

```text
F_source = I + N_source subset Phi^*,                     (2)
```

where `N_source` contains infinite-support conormals and

```text
W = intersection_(nu in N_source) ker(nu)                 (3)
```

at least after the appropriate source closure. Relative to `(Phi,F_source)`, the constraint is
closed and visible; relative to `(Phi,I)`, it is dense and invisible.

This is a topology theorem about observables of the constraint, not a time parameter or a hidden
flow.

## The literal interval `[BRIDGE]`

For a separating dual pair `(Phi,F_source)`, classical Mackey--Arens theory gives:

```text
sigma(Phi,F_source) <= tau <= tau_M(Phi,F_source)          (4)
```

for every Hausdorff locally convex topology `tau` whose continuous dual is exactly `F_source`.
The weak topology is the coarsest compatible topology and the Mackey topology is the finest.
Formula `(4)` is established parent theory and is not claimed new.

The **source Mackey interval** is the interval of compatible topologies in `(4)`, together with
the affine calibration, constraint kernel `(3)`, and reflection action on the dual pair. It is
canonical only after the source has constructed `F_source`; choosing `F_source` from a desired
spectrum is circular.

## Cross-representation equivalence criterion

**[CONJECTURE]** Two analytic obstruction constructions represent one constrained HT object if
and only if their source charts are related by a dual-pair isomorphism carrying:

1. the finite clock covectors `I` to `I`;
2. the source conormal space `N_source` to `N_source`;
3. the affine calibration section to the affine calibration section;
4. the coherent clock-descent anomaly to the same comparison class;
5. the reflection involution and orientation to their counterparts.

If this holds, their topologies lie in one Mackey interval. If their continuous duals differ, they
are different source objects even when their scalar determinants or degeneracy sets coincide.

This supplies a hard anti-redressing gate. “Same spectrum,” “same index,” or “same RH-equivalent
criterion” is not a comparison map.

## Self-dual stable degeneracy `[CONJECTURE]`

Suppose the source constructs a parameterized conormal relation `Lambda_lambda` in the dual pair
and an anti-linear reflection `J` preserving `F_source`. Define a degeneracy to be
**Mackey-stable** when it is the failure of algebraic transversality between `Lambda_lambda` and
its reflected relation, hence persists in every topology compatible with the same dual pair.

The proposed common spectrum is the support of this topology-independent transversality defect,
not the union of spectra of separately chosen operators. The five obstruction languages then have
precise proof obligations:

| Language | Required realization of the same dual-pair defect |
|---|---|
| spectral incompleteness | homology of a completion of the comparison cone |
| continuation failure | failure of a weak inverse to extend to a stronger compatible topology |
| positivity failure | failure to orient the reflected conormal pairing |
| monodromy | determinant-line holonomy of the same conormal relation |
| boundary conditions | distinct closed realizations inside the same Mackey interval |

The Mackey interval alone does not make these quantities equal. Equality must be proved by maps
preserving the source dual pair and comparison class.

## Gamma model

For the period-one Gamma/digamma source, let `Phi` contain the entire Fourier polynomials and let
`W` be the periodic homogeneous tangent. Finite derivatives at zero give `I`. The source supplies
the infinite conormal

```text
nu(h)=h(1)-h(0)=sum_(n>=1) h^(n)(0)/n!.                   (5)
```

Finite Fourier packets make `W` dense for the raw product-jet topology, so `nu` is not continuous
there. In the analytic compact-open source topology, `nu` is continuous and `W=ker(nu)` is closed.
Thus Gamma concretely realizes the dual enlargement

```text
I  ->  I + K nu.                                          (6)
```

The reflection law for the global shift cofactor preserves its nonunit divisor. What remains open
is to construct the reflected dual-pair involution and prove a self-dual conormal relation, not
merely a self-dual scalar symbol.

## Zeta terminal speculation `[CONJECTURE; NOT AN RH RESULT]`

A completed-zeta source would have to construct `(Phi,F_source,Lambda,J)` from prime and
archimedean constraints before inspecting zeros. Different RH proof chains would be faithful
realizations only if they preserve this same enlarged dual pair and comparison class.

The critical-line zeros would then be the fixed-locus part of the Mackey-stable self-dual
transversality spectrum. Off-line zeros, if any, would occur in nonfixed reflection pairs. No
claim that the spectrum lies on the fixed locus is made.

## Collision audit

- Mackey--Arens theory already classifies compatible locally convex topologies of a dual pair.
- Rigged Hilbert spaces already use a source test space and enlarged dual to continue resolvents
  and define generalized spectra.
- Boundary triples, determinant lines, and Hermitian K-theory already package extensions,
  holonomy, and self-duality once the relevant dual pair or operator is supplied.

The candidate-new residue is not `(4)`. It is the necessity chain

```text
HT finite clock freedom
  -> product-density and zero Hausdorff product conormal
  -> source constraint must enlarge the continuous dual
  -> the enlarged dual, not a chosen completion, fixes the topology interval
  -> common obstructions must preserve one self-dual dual-pair comparison class.  (7)
```

Scientific novelty remains unverified until a non-Gamma class of HT sources is constructed and
the self-dual stable-degeneracy theorem is proved.

## Gates

- [x] finite-observable product-density theorem formalized
- [x] Hausdorff product-observation no-go formalized
- [x] Gamma infinite conormal and source topology constructed
- [x] Mackey--Arens parent collision identified
- [ ] source dual pair constructed functorially for a nontrivial class of constrained HT sources
- [ ] source conormal kernel equality `(3)` proved in that class
- [ ] reflection shown to preserve the enlarged dual pair
- [ ] Mackey-stable transversality defect defined and proved representation-invariant
- [ ] three obstruction chains mapped to one dual-pair class
- [ ] independent novelty/significance audit
