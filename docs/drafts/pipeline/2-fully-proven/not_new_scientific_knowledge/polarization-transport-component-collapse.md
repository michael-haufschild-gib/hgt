# Polarization transport collapses orientation surgery to component data

- **ID:** `polarization-transport-component-collapse`
- **Stage:** 2-fully-proven / boundary-wedge Lean seed complete
- **Type:** THEOREM / POSITIVE SUCCESSOR TO ORIENTATION BLINDNESS
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Parents:**
  - `../new_scientific_knowledge/hypertranscendental-hochster-source-coherence-duality.md`
  - `../../1-in-progress/hypertranscendental-polarization-fibration.md`
  - `fixed-analytic-dimension-arbitrary-source-coherence.md`

## The distinction forced by orientation surgery

The derived constraint topology alone is blind to residue orientation.  This does not imply that
an orientation coupled to the restriction maps of that topology is arbitrary.  The missing datum
is transport.

Let `X` be a finite simplicial constraint complex and attach a one-dimensional real coherence
line to every vertex.  A Boolean orientation is a map

```text
epsilon : Vert(X) -> {+,-}.                                  (1)
```

Call it transport-compatible when every nonzero restriction along an edge is an isometry.  Since
an isometry between one-dimensional nondegenerate real forms preserves the sign of the form,

```text
{transport-compatible orientations on X}
       ~= {+,-}^(pi_0(X)).                                   (2)
```

In particular, if `X` is connected, the compatible fibre has exactly two points.  A positive
pointing at one vertex selects the unique all-positive section.

## Proof

Along every edge `{u,v}`, compatibility gives `epsilon(u)=epsilon(v)`.  Equality propagates along
edge paths, so `epsilon` is constant on connected components.  Conversely, every assignment of
one sign to each component is constant on edges and therefore compatible.  These constructions
are inverse.  If `X` is connected, evaluation at any chosen vertex gives the equivalence with one
Boolean sign.  Requiring that value to be positive leaves a singleton.  `QED`

The statement remains valid for one-dimensional Hermitian lines over any real closed field.  For
higher-rank stalks, the component sign is replaced by the locally constant Witt/Krein class; the
classification of compatible forms then also depends on the transport holonomy.

## Exact boundary-wedge seed

For

```text
Delta_(r,s)=boundary(sigma^r) wedge boundary(sigma^s),      r,s>=2,
```

delete the common vertex `0`.  The induced complex is the disjoint union of two full simplices,
so its compatible orientation fibre is

```text
{+,-} x {+,-}.                                              (3)
```

Restore `0`.  Every left and right vertex is joined to `0`, hence the sewn wedge is connected and
the compatible fibre becomes

```text
{+,-}.                                                      (4)
```

Positive pointing at `0` leaves one section.  Thus sewing is not merely topological gluing: when
polarization transport is retained, it removes one independent orientation degree of freedom.

## No-go and positive law

> **NO-GO.** Adding an uncoupled sign cube to a derived constraint topology cannot solve the
> selector problem; the signs remain free decorations.

> **POLARIZATION-TRANSPORT LAW.** Restriction-compatible polarization converts topology into an
> orientation constraint: the residual sign freedom is exactly component freedom, and pointing
> kills the last global sign on a connected boundary.

This is the smallest positive mechanism by which the topology participates in positivity without
determining positivity by itself.

## RH-facing consequence

A potential RH proof may not merely exhibit a positive form somewhere on a derived zeta object.
It must construct source-natural transport maps and prove that the form is compatible with them.
If the resulting polarized boundary is connected in the relevant exit-path or realization
category, one source-positive pointing could then propagate globally.  The hard arithmetic
problem is to construct that pointing and prove that no degeneracy breaks transport; this theorem
does neither and is not an RH result.

## Parent-theory and anti-theatre verdict

After erasing HT language, `(2)` is the elementary classification of locally constant Boolean
functions by connected components, or the rank-one case of transporting signatures in a local
system.  It is therefore not new scientific knowledge.

Its role is architectural: it identifies the first coupling absent from the orientation-surgery
counterexamples and supplies an exact finite seed for the polarization fibration.

- `[PROOF GATE -- PASS]`
- `[SIGNIFICANCE AS POSITIVE MECHANISM -- PASS]`
- `[PARENT-THEORY GATE -- FAIL FOR NEW KNOWLEDGE]`
- `[ANTI-THEATRE -- BRIDGE]`
- `[PAPER VERDICT]` Use as the rank-one seed in the polarization-fibration theory, not as a
  standalone paper.

## Lean surface

`formal/GaloisForLFunctions/HTGeometry/WedgeRealization.lean` defines the boundary-wedge complex,
its deleted-centre induced subcomplex, and compatible Boolean polarization transport.  The exact
equivalences are:

```text
boundaryWedgeDeletedCompatibleOrientationEquivBoolProd
boundaryWedgeCompatibleOrientationEquivBool
```

The first realizes `(3)` and the second realizes `(4)` unconditionally.

## Gates

- [x] component classification proved
- [x] deleted-centre two-component fibre proved
- [x] sewn connected fibre proved
- [x] positive pointing consequence proved
- [x] novelty downgrade recorded
- [x] boundary-wedge Lean verification complete
- [ ] extend from Boolean rank-one forms to restriction-compatible Witt objects
- [ ] construct one source-natural nontrivial transport system analytically
