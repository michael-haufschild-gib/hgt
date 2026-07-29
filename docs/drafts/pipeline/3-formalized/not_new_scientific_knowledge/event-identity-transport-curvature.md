# Event-created identities compose exactly at commuting interfaces

- **ID:** `event-identity-transport-curvature`
- **Stage:** 3-formalized
- **Type:** EXACT C⋆-ALGEBRA THEOREM / PHYSICS BRIDGE / NOT NEW MATHEMATICS
- **Parent:** `../../1-in-progress/event-generated-identity-curvature-law.md`
- **Status:** `[DEPENDENCY-CLOSED PAPER PROOF] [UNCONDITIONAL LEAN]`
- **Physics status:** `[CONJECTURAL INTERPRETATION ONLY]`

## Question

If an event creates only a partial physical identity, when can the identity transports created by
two successive events be composed without adding a new comparison?

## Definitions

Let \(\mathcal A\) be a unital \(C^*\)-algebra. Call \(u\in\mathcal A\) a partial identity
transport when
\[
u u^\dagger u=u.                                                   \tag{1}
\]
It creates the initial and final projections
\[
s(u)=u^\dagger u,
\qquad
t(u)=u u^\dagger.                                                  \tag{2}
\]

For \(u\) followed by \(v\), define the interface identity curvature
\[
\mathcal K(v,u)
=[t(u),s(v)]
=(u u^\dagger)(v^\dagger v)-(v^\dagger v)(u u^\dagger).           \tag{3}
\]

## Theorem

If \(u\) and \(v\) satisfy `(1)`, then
\[
\boxed{
v u\text{ is a partial identity transport}
\quad\Longleftrightarrow\quad
[t(u),s(v)]=0.
}                                                                  \tag{4}
\]
Equivalently,
\[
\boxed{
\mathcal K(v,u)=0
\quad\Longleftrightarrow\quad
v u(vu)^\dagger vu=vu.
}                                                                  \tag{5}
\]

Thus noncommutativity of the event-created identity at the shared interface is exactly the
obstruction to composing the two partial transports.

## Proof

Equation `(1)` and its adjoint imply that \(s(u),t(u),s(v),t(v)\) are self-adjoint idempotents.
Put
\[
p=t(u)=uu^\dagger,
\qquad
q=s(v)=v^\dagger v.
\]

If \(pq=qp\), then
\[
\begin{aligned}
(vu)(vu)^\dagger(vu)
&=vu u^\dagger v^\dagger vu\\
&=v p q u\\
&=v q p u\\
&=vu,
\end{aligned}
\]
using \(vq=v\) and \(pu=u\). Hence \(vu\) is a partial isometry.

Conversely, suppose \(vu\) is a partial isometry. Its final projection
\[
r=(vu)(vu)^\dagger
\]
is a self-adjoint idempotent. Since \(t(v)r=r=rt(v)\), the compression
\[
q p q=v^\dagger r v
\]
is also a self-adjoint idempotent. Now set
\[
x=(1-q)pq.
\]
Using \(p^2=p\), \(q^2=q\), and \((qpq)^2=qpq\),
\[
x^\dagger x
=qp(1-q)pq
=qpq-(qpq)^2
=0.
\]
The \(C^*\)-identity implies \(x=0\). Therefore
\[
pq=qpq.
\]
Taking adjoints gives \(qp=qpq\), hence \(pq=qp\). This proves `(4)`. Equation `(5)` is `(4)`
with the commutator written as a difference. \(\square\)

## Novelty boundary

The operator theorem is established mathematics, usually attributed to Halmos--Wallen: a product
of partial isometries is a partial isometry exactly when the range projection of the first factor
commutes with the initial projection of the second. See:

- P. R. Halmos and L. J. Wallen, *Powers of partial isometries*, Journal of Mathematical
  Mechanics **19** (1970), 657--663;
- A. an Huef, I. Raeburn, and I. Tolich, *Structure theorems for star-commuting power partial
  isometries*, Linear Algebra and its Applications **481** (2015), 107--114,
  [arXiv:1703.03506](https://arxiv.org/abs/1703.03506).

The name `eventIdentityCurvature` is an interpretation of the standard commutator, not a
mathematical priority claim. In the invertible Lorentz \(2\times2\) sector, repolarizing products
of noncommuting positive factors is already the Thomas--Wigner rotation. For density-amplitude
comparisons, nearby holonomy is already Uhlmann transport. Those are shadows and hostile
precedents, not evidence that `(3)` is gravity.

## What this tells us

The theorem supplies a sharper common reading of several corpus obstructions:

1. an event represented by a partial isometry creates its own source and target identity
   projections;
2. those identities need not agree with identities created by the next event;
3. disagreement is quantum noncommutativity, not missing bookkeeping;
4. when disagreement is nonzero, ordinary multiplication cannot preserve the class of partial
   identity transports; and
5. any successor law must either change support, discard information, or add a canonical
   repolarization/comparison.

The exact public sentence is:

> **Quantum events can create identities that cannot be composed.**

The physical conjecture suggested, but not proved, is:

> **Spacetime and force are the canonical record of repairing noncomposable quantum identity.**

This is stronger than saying that gauge fields are connections or that noncommutativity produces
geometric phase. It becomes new physics only if one source law derives the event, the support
projections, the repair, and all observed responses without supplying them separately.

## New mathematical open core

The next object cannot be another fixed-Hilbert-space polar decomposition. It must be a
**source-generated support-varying polar completion** with a universal property:

1. events, rather than pre-existing objects, generate their initial and final positive
   identities;
2. zero \(\mathcal K\) gives strict partial composition;
3. nonzero \(\mathcal K\) canonically creates a minimal comparison cell rather than requiring a
   chosen dilation or connection;
4. comparison cells compose coherently across triples and independent event products;
5. the cell's public quotient is the complete positive causal record;
6. its internal automorphisms are exactly the event's retained gauge identities;
7. the exceptional source uniquely selects the \(3\)-hidden/\(2\)-public complex interface and
   exact Standard Model global group; and
8. complete calibrated history is finitely horizontalizable exactly in the
   differential-algebraic phase.

Items 1--8 are not consequences of Halmos--Wallen and remain the actual research jump.
Hypertranscendence is not identified with the local commutator `(3)`: the corpus already contains
flat systems with infinite holonomy. Its viable role is obstruction to finite global
horizontalization after the accumulated reporter has been derived.

## Formal certificate

Lean module:
`formal/GaloisForLFunctions/HTGeometry/EventIdentityTransportCurvature.lean`.

Unconditional declarations:

- `IsPartialIdentityTransport`;
- `eventIdentityCurvature`;
- `IsPartialIdentityTransport.star_transport`;
- `IsPartialIdentityTransport.finalProjection`;
- `IsPartialIdentityTransport.initialProjection`;
- `IsPartialIdentityTransport.mul_of_interface_commute`;
- `IsPartialIdentityTransport.mul_iff_interface_commute`; and
- `IsPartialIdentityTransport.curvature_eq_zero_iff_mul`.

No physical assumption is encoded as a Lean axiom. Direct foreground checking uses:

```text
lake env lean GaloisForLFunctions/HTGeometry/EventIdentityTransportCurvature.lean
```

Final leaf audit:

- `lake build GaloisForLFunctions.HTGeometry.EventIdentityTransportCurvature`;
- result: `2888/2888` jobs, build successful; and
- every theorem above has exactly the standard logical dependencies `propext`,
  `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1: exact event-support composability question isolated
- [x] 1 → 2: dependency-closed \(C^*\)-algebra proof and prior-art boundary
- [x] 2 → 3: unconditional Lean formalization and umbrella registration
- [ ] 3 → 4: bridge only; not a standalone publication target

## Log

- 2026-07-29 — generic polar-split unification was hostile-tested against Thomas--Wigner and
  Uhlmann holonomy.
- 2026-07-29 — extracted Halmos--Wallen composability as exact positive survivor.
- 2026-07-29 — formalized the full \(C^*\)-algebra equivalence and commutator-zero form in Lean.
