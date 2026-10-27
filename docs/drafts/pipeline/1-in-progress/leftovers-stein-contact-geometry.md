# Faithful geometry for the smooth Stein hull theorem

- **ID:** leftovers-stein-contact-geometry
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION ROUTE; classical bridge, no novelty claim
- **Source:** [original theorem](../2-fully-proven/leftovers/smooth-stein-order-two-autonomous-ade-frequency-rank.md)
- **Statement:** Formalize the original compact smooth minimal-hull dimension bound and its frequency-rank corollary, with every geometric input proved.

## Goal

Preserve the original Stein surface, embedded smooth hull, and real-holomorphic
flow. Derive all auxiliary structures from these hypotheses. In particular,
an assumed contact metric, compact Lie action, dimension bound, periodic orbit,
or Stein maximum principle cannot replace its construction.

## Internal and external audit

Current corpus searches for K-contact and minimal isometric Reeb dynamics did
not surface reusable differential-geometric results. The general corpus has
many unrelated uses of “contact”; those are not inputs to this theorem.

The compact-isometry-group closure of a K-contact Reeb flow and its contact
torus action are classical; see Goertsches–Nozawa–Töben,
[§2 of *Equivariant cohomology of K-contact manifolds*](https://arxiv.org/pdf/1102.4476).
This provides a candidate replacement for the unrestricted Weinstein input.
It does not itself supply a Lean proof or the metric needed by this hull.

## Exact contact-branch mechanism

The original argument gives `H=TK∩J(TK)`, the flow-invariant Levi tensor,
and its everywhere-zero/nowhere-zero dichotomy. In the contact branch,
minimality and `[X,JX]=0` force `X` transverse to `H`. The uniquely normalized
form `β` satisfies `ker β=H`, `β(X)=1`, and `L_X β=0`, hence `ι_X dβ=0`.

Minimality makes the hull connected. On its complex line bundle `H`, the
nonzero form `dβ` has a fixed Levi sign `σ∈{−1,1}`. With
`P(v)=v−β(v)X`, define the actual metric

`g(u,v)=β(u)β(v)+σ dβ(Pu,J Pv)`.

Rank-two linear algebra makes this symmetric and positive definite. The
flow preserves every factor, so it preserves `g`. Its closure in the compact
Riemannian isometry group is an abelian compact Lie group `G`. Minimality
makes the `G` action transitive. For fundamental fields `Y,Z` of `G`,
`β(Y)` and `β(Z)` are invariant under the original minimal flow, hence
constant. Also `[Y,Z]=0`, so

`dβ(Y,Z)=Y(β(Z))−Z(β(Y))−β([Y,Z])=0`.

Transitivity makes these fields span every tangent space, contradicting
contactness. This keeps the exact geometric conclusion and uses the extra
holomorphic invariance already present in the original assumptions.

An alternative to a full Lie-group theorem is available if the existing
geodesic infrastructure supports compactness in the smooth topology. A
uniform limit of isometries is smooth locally: pass to a convergent subsequence
of first derivatives at a point and use
`F(exp_p v)=exp_(F p)(dF_p v)`. The compact closure `G` then acts smoothly in
the space variable, with continuous derivatives of every order in `G`.
Its stabilizer at any point is trivial: a commuting isometry fixing one
point fixes its dense flow orbit. Thus evaluation identifies `G` with `K`.

Haar-average localized smooth vector fields over `G`. On a sufficiently
small support, the contributing transformations and their derivatives are
close to the identity, so averages of a local basis remain independent at
one point. Invariance and transitivity make them a global frame. Their
flows commute with `G`, and every such commuting flow belongs to `G` by
evaluation at one point. Consequently the averaged fields commute. The
same exterior-derivative calculation gives `dβ=0`. This route still requires
the complete smooth-limit, averaging, positivity and flow proofs; none is
being assumed as an interface field.

## Local maximum arguments

There are also direct calculus routes for the other branches. At a maximum
of a strictly plurisubharmonic function restricted to a Levi-flat hull,
choose a local nonzero section `V` of `H`. The identity

`ddᶜρ(V,JV)=V²ρ+(JV)²ρ+dρ(J[V,JV])`

has nonpositive first two terms. Levi flatness puts `[V,JV]` in `H`, so the
last term vanishes. This contradicts strict plurisubharmonicity without
needing a separately constructed complex leaf. In real dimension four,
the tangent map of the embedding is an isomorphism. At a restricted maximum,
`dρ=0` on the full ambient tangent space; the second derivative test again
contradicts strict plurisubharmonicity. These are proof strategies, not
substitute assumptions.

## Open formal dependencies

- Faithful complex-surface and Stein definitions; derive the required strict
  plurisubharmonic function from the chosen Stein model, without assuming the
  desired maximum obstruction.
- Smooth tangent/CR bundles, Levi tensor, pullbacks and exterior derivative;
  local vector fields and the maximum identities above.
- Smooth compact Riemannian isometry-group theorem, closed Lie subgroups,
  and surjectivity of infinitesimal evaluation for the transitive action.
- Actual invariant metric construction, minimality reductions and dimension
  comparison for the embedded hull.
- Actual Bohr hull, equivariant realization, and equality of character rank
  with the relevant dimension. A structure field asserting that equality is
  not a proof.

## Gates

- [x] Exact statement and candidate proof mechanism recorded.
- [x] Classical parent mechanism located; no novelty claimed.
- [ ] Dependency-closed formal models and proofs.
- [ ] Direct named-source Lean checks and transitive axiom audits.
- [ ] Original card fully covered, wired and promoted.

## Current status

No new Lean declaration is claimed for this route. The original theorem card
remains at stage 2. Bi-scale source checks continue independently under the
same full formalization programme.
