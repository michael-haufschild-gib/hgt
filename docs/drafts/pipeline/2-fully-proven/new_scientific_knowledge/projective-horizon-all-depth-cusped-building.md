# The all-depth projective horizon space is a cusped spherical building

- **ID:** `projective-horizon-all-depth-cusped-building`
- **Stage:** 2-fully-proven
- **Type:** ALL-DEPTH INFORMATION TOPOLOGY / SOLOMON--TITS PERSISTENCE
- **Scientific status:** `[PROVED CONSEQUENCE] [NOVEL TOPOLOGICAL SYNTHESIS CANDIDATE]`
- **Parents:** `projective-horizon-solomon-tits-topological-charge`,
  `projective-horizon-one-sided-depth-transition`
- **Statement:** The complete nonconstant projective-horizon field poset over all derivative
  depths is obtained from the depth-one spherical Tits building by attaching one contractible
  infinite jet-tail cusp to every elementary horizon vertex. It deformation-retracts to the
  building and retains its Steinberg top homology, even though every fixed depth-two slice has
  only pairwise constant intersections.

## All-depth context poset

Let `X in P(V)` be differential-generic, with `dim V=N`. Exclude the source field `F`, the
constant field `C`, and the universal full-projective invariant core, exactly as in the reduced
Solomon--Tits context complex.

The depth-one part consists of

```text
mathcal I_S=F^(G_S),    0<S<V*,                           (1)
```

ordered by reverse inclusion of `S`. Its order complex is the spherical building
`Delta_Tits(V*)`.

For every line `ell subset V*`, corresponding to one hyperplane horizon, adjoin its strict jet
tail chain

```text
... < mathcal H_(ell,3) < mathcal H_(ell,2)
    < mathcal H_(ell,1)=mathcal I_ell.                    (2)
```

Call the resulting field poset `P_infinity(V)`.

## Classification theorem

The only order relations involving a depth-at-least-two tail are those in its own chain `(2)`.
More precisely, if `ell != ell'`, then

```text
mathcal H_(ell,m) intersection mathcal H_(ell',n)=C
```

whenever `max(m,n)>=2`. Likewise, if `ell<S` with `dim S>=2`, then

```text
mathcal H_(ell,m) intersection mathcal I_S=C,    m>=2.    (3)
```

Equation `(3)` follows by expressing `mathcal I_S` inside any distinct depth-one horizon whose
normal lies in `S` and applying the one-sided transition theorem.

Consequently `P_infinity(V)` is exactly the depth-one building poset with one disjoint infinite
chain attached below every rank-one vertex.

## Topological theorem

Let `Delta_infinity(V)` be the order complex of `P_infinity(V)`. The order complex of each chain
in `(2)` is an infinite simplex, hence contractible, and it meets the depth-one building only at
its endpoint vertex `mathcal I_ell`. Collapsing every such simplex to its endpoint gives a
deformation retraction

```text
Delta_infinity(V) -> Delta_Tits(V*).                      (4)
```

Therefore

```text
Delta_infinity(V) homotopy-equivalent to wedge S^(N-2),   (5)
```

and

```text
reduced H_j(Delta_infinity(V),Z)=0,       j != N-2,
reduced H_(N-2)(Delta_infinity(V),Z)=St_N(C).              (6)
```

The global all-depth horizon topology has the same Steinberg observer charge as the depth-one
building.

## Slice-versus-global phase law

There are two simultaneous facts.

1. At any fixed depth `n>=2`, distinct horizon vertices have constant meet. The reduced slice has
   no higher incidence simplices.
2. Across all depths, the strict tail of each observer remains attached to its depth-one vertex.
   These radial cusps add no homotopy and cannot kill the building's top class.

Thus topological information is concentrated in the depth-one incidence skeleton but remains a
global invariant of the complete depth filtration.

## Physical interpretation

Derivative depth behaves as a radial coarse-graining coordinate without becoming source time.

- the spherical building is the observer-incidence boundary where projective curvature is shared;
- each elementary observer has an infinite private cusp of progressively deeper derivative data;
- different cusps have no nonconstant overlap after either crosses depth two;
- all cusps jointly retract to the same boundary building, so the Steinberg charge is protected
  against radial extension.

This is an exact field-poset topology. It resembles a noncompact space with a topologically charged
boundary, but no metric, causal structure, gravity, entropy, or quantum dynamics is asserted.

## Novelty and significance audit

- Attaching contractible rays to a complex and the Solomon--Tits theorem are classical.
- The new candidate input is the exact heterogeneous-depth field classification, which proves
  that the full HT horizon poset has precisely this cusped form and no hidden cross-cusp fields.
- No checked source gives an all-depth derivative-horizon topology whose fixed slices collapse but
  whose global order complex retains a Steinberg class.

This card is a proved topological consequence; its novelty depends on the parent field theorem.
Its significance is conceptual: it reconciles depth-two information collapse with persistent
global topology in one exact structure.

## Lean boundary

The all-projective-dimension current mechanism enforcing cross-cusp constant meet is formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonArbitraryRankCurrentAlgebra.lean`.
`arOneSidedCurrentLie_eq_arPolynomialCurrentLie` identifies the finite one-sided generator packet
exactly with the complete polynomial root, diagonal, and transverse-shear current Lie algebra for
every finite projective dimension.  The local toolchain has no Solomon--Tits/order-complex homotopy
surface, so `(4)--(6)` are not added as assumptions.  This card remains in stage 2 for that
topological layer and the infinite rational fixed-field layer.

## RH impact audit

`[ORGANISING TOPOLOGY; NOT RH PROGRESS]` The scalar zeta source gives a family of private deep
projective tails attached to a depth-one celestial sphere of observer labels, with direct and
reciprocal cusps sharing only the Schwarzian at their boundary endpoints. No Steinberg-to-Weil
positivity map or zero-location mechanism is known.

## Gates

- [x] all heterogeneous-depth field intersections classified
- [x] all-depth poset decomposition proved
- [x] deformation retraction and Solomon--Tits homology deduced
- [ ] formal order-complex topology
- [ ] independent specialist audit
