# Flat law superconnection, curvature nullhomotopy, and holonomy law

- **ID:** `nhg-flat-superconnection-hierarchy`
- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [NO ROUTE INPUT] [NOT RH]`
  `[LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED]`
- **Role:** first exact transport hierarchy for Nomological Homotopy Geometry.

## 1. Setup

Let `B` be a smooth manifold and let

\[
 E=\bigoplus_j E^j\longrightarrow B
\]

be a finite-rank graded vector bundle. On `Omega(B;E)`, use total degree = form degree + internal
degree. A superconnection of total degree one is written

\[
 \mathbb D=D_0+D_1+D_2+D_3+\cdots,
\tag{SC.1}
\]

where

\[
 D_0=\partial\in\Omega^0(B;\operatorname{End}^{1}E),\qquad
 D_1=\nabla,
\]

and, for `k>=2`,

\[
 D_k=A_k\in\Omega^k(B;\operatorname{End}^{1-k}E).
\tag{SC.2}
\]

Composition below means graded composition as operators on `Omega(B;E)`; this convention includes
all Koszul signs. Assume

\[
 \mathbb D^2=0.
\tag{SC.3}
\]

This is the linear representation-up-to-homotopy chart of a source-anchored law algebroid.

## 2. Component theorem

### Theorem 2.1 — higher transport hierarchy

For every `n>=0`, the form-degree-`n` component of `(SC.3)` is

\[
 \boxed{\sum_{i+j=n}D_iD_j=0.}
\tag{SC.4}
\]

In particular,

\[
 \partial^2=0,
\tag{SC.5}
\]

\[
 [\partial,\nabla]=0,
\tag{SC.6}
\]

\[
 F_\nabla+[\partial,A_2]=0,
\tag{SC.7}
\]

and

\[
 d_\nabla A_2+[\partial,A_3]=0.
\tag{SC.8}
\]

Thus ordinary connection curvature need not vanish. It is canonically nullhomotopic through the
two-form transport cell `A_2`; the failure of that nullhomotopy to be covariantly closed is itself
nullhomotopic through `A_3`; equation `(SC.4)` continues this hierarchy.

#### Proof

Each `D_k` raises total degree by one and form degree by `k`. Expanding

\[
 \mathbb D^2=\sum_{i,j\geq0}D_iD_j
\]

and collecting terms of fixed form degree `n` gives `(SC.4)`. For `n=0`, this is `(SC.5)`. For
`n=1`, it is `D_0D_1+D_1D_0=0`, which is `(SC.6)`. For `n=2`, it is

\[
 D_1^2+D_0D_2+D_2D_0=0,
\]

which is `(SC.7)`. For `n=3`, it is

\[
 D_1D_2+D_2D_1+D_0D_3+D_3D_0=0,
\]

which is `(SC.8)`. The same collection proves every higher identity. QED.

## 3. Cohomological flatness

Assume the ranks of the fibrewise cohomology groups

\[
 H^j(E,\partial)=\ker(\partial:E^j\to E^{j+1})/
 \operatorname{im}(\partial:E^{j-1}\to E^j)
\]

are locally constant, so they form a graded vector bundle `H(E,partial)`.

### Theorem 3.1 — induced observer connection is flat

Equation `(SC.6)` makes `nabla` descend to a connection `nabla^H` on `H(E,partial)`, and

\[
 \boxed{F_{\nabla^H}=0.}
\tag{SC.9}
\]

#### Proof

Equation `(SC.6)` says `nabla` preserves cycles and boundaries, so it induces `nabla^H`. For a
cycle `x`, equation `(SC.7)` gives

\[
 F_\nabla x=-\partial(A_2x)-A_2(\partial x)=-\partial(A_2x).
\]

Thus `F_nabla x` is a boundary. Hence the curvature induced on cohomology vanishes. QED.

### Corollary 3.2 — local flatness does not close history

The flat connection `nabla^H` defines a holonomy representation

\[
 \operatorname{Hol}_{\mathbb D}:\pi_1(B,b)\longrightarrow
 \operatorname{Aut}(H(E_b,\partial)).
\tag{SC.10}
\]

It can be nontrivial even though `(SC.9)` holds. Therefore:

\[
 \boxed{\text{cohomological curvature }0\ \not\Longrightarrow\
 \text{closed lifted history}.}
\tag{SC.11}
\]

#### Proof

Flatness makes parallel transport homotopy-invariant, hence gives `(SC.10)`. Take a flat line
bundle on `S^1` with nonidentity monodromy. Its curvature is zero and its holonomy is nontrivial.
QED.

## 4. Exact chain-curved model

### Example 4.1 — nonzero connection curvature erased by higher transport

Let `B=R^2` with coordinates `(x,y)`. Let `E^0` and `E^1` be trivial real line bundles, let
`partial:E^0->E^1` be the identity, and let `partial|E^1=0`. Define `h:E^1->E^0` as the identity
and `h|E^0=0`. Then

\[
 [\partial,h]=\operatorname{id}_E.
\tag{SC.12}
\]

Give both terms the scalar connection

\[
 \nabla=d+x\,dy,
\qquad F_\nabla=dx\wedge dy\,\operatorname{id}_E.
\]

Set

\[
 A_2=-dx\wedge dy\,h,
\qquad A_k=0\quad(k\geq3).
\]

Then `(SC.12)` gives `F_nabla+[partial,A_2]=0`; also `d_nabla A_2=0` and `A_2^2=0`.
Consequently

\[
 \mathbb D=\partial+\nabla+A_2
\]

satisfies `mathbb D^2=0`, although `F_nabla` is nonzero. The fibre complex is acyclic, so the
cohomological observer sees nothing.

This example proves that ordinary curvature, homological curvature, and observed holonomy are
different levels of one transport hierarchy.

## 5. Field consequences

1. A raw commutator or ordinary connection curvature is not automatically a law invariant. Higher
   transport may nullhomotope it.
2. The invariant object is the entire flat superconnection, up to structured equivalence, not one
   selected component.
3. Passing to cohomology is an irreversible observer: it erases the chain-level nullhomotopy tower.
4. Vanishing cohomological curvature still permits nontrivial global holonomy.
5. A curvature-to-holonomy generation theorem requires anchored integration plus analytic and
   effectivity hypotheses; it cannot follow from `mathbb D^2=0` alone.
6. No action or cost follows from the superconnection. Metric history remains a further compatible
   enhancement.

## 6. Hostile boundary

- On a contractible base, flat cohomological holonomy is trivial, but chain-level `A_k` may remain
  nonzero.
- On a non-simply-connected base, all `A_k` for `k>=2` may vanish while flat holonomy is nontrivial.
- Acyclic complexes can carry nonzero chain curvature and higher transport while every
  cohomological observer is zero.
- Two flat superconnections can induce the same cohomology local system and differ in higher
  transport cells.
- Nothing here identifies prolongation growth, positivity, recurrence, or cost. Those require the
  filtration, cyclic structure, integrated history, and action of the full NHG field.

## 7. Proof status

All statements above follow from the form-degree decomposition of a flat superconnection, standard
fibrewise cohomology, and the displayed finite-rank example. No route-specific theorem, source
selector, zero hypothesis, or RH statement is used.

## Lean formalization status

- **Status:** `[LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED]`
- **Module:**
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection`
- **Umbrella wiring:** imported by
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry`; card is promoted to Stage 3.
- **Exact hierarchy capstones:** `component_eq_zero`, `differential_sq_zero`,
  `differential_connection_anticommute`, `curvature_add_nullhomotopy_eq_zero`, and
  `covariantA2_add_nextNullhomotopy_eq_zero`.
- **Cohomological observer capstones:** `flatSuperconnection_inducedConnection_sq_eq_zero`,
  `Differential.induced_curvature_eq_zero`, and `Differential.inducedConnection_sq_eq_zero`.
- **Exact-model capstones:** `exactModel_nullCurvature`, `exactModel_curvature_ne_zero`,
  `exactModel_cycles_eq_boundaries`, and `exactModel_cohomology_subsingleton`.
- **Holonomy-separation capstones:** `circleSignHolonomy_nontrivial` and
  `zeroCurvature_not_imply_trivialHolonomy`.
- **Verification:** foreground
  `lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/FlatSuperconnection.lean`
  completed with zero errors and zero warnings.
- **Promotion gate:** umbrella build and `#print axioms` audit passed on 2026-08-13.
