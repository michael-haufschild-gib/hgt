# Jet-dependent projective observers do not give a source-pure Hjelmslev refinement

- **ID:** `projective-horizon-hjelmslev-observer-refinement`
- **Stage:** 5-failed
- **Type:** RETIRED PHYSICAL-TOPOLOGICAL EXTENSION
- **Status:** `[ROUTE CLOSED] [SOURCE-PURITY OBSTRUCTION]`
- **Parent:** `projective-horizon-depth-two-building-collapse`

## Proposed extension

Replace constant horizon labels `H in P(V*)` by projective hyperplanes over the truncated ring

```text
C[t]/(t^n).
```

Their incidence geometry is a projective Hjelmslev geometry, closely related in rank three to
truncations of affine buildings. The proposal was that derivative depth might replace the
depth-one spherical Tits building by an ultrametric congruence geometry rather than truly
collapsing it.

## Exact obstruction

Let `g(t) in GL(V,C[[t]])` be a jet-dependent observer frame and let it transform a free vector
arc `X(t)` to

```text
Y(t)=g(t)X(t).                                             (1)
```

For the induced substitution on the free differential jet field to be source-pure, it must
commute with the source derivation. But

```text
Y'=gX'+g'X.                                               (2)
```

The first term is the transformed source derivative; the second is an observer connection. For
`(2)` to agree projectively with the transformation of `X'` for every generic `X`, the endomorphism

```text
g^(-1)g'                                                  (3)
```

must send every line to itself. In dimension at least two, an endomorphism preserving every line
is scalar. Hence

```text
g^(-1)g'=lambda(t) I.                                     (4)
```

After quotienting by scalar matrices, `(4)` says

```text
[g(t)]'=0 in PGL(V),                                      (5)
```

so the projective observer is constant. Conversely a constant projective frame plainly commutes
with the derivation.

Thus the only projective observer changes compatible with the bare source derivation are the
constant `PGL(V)` frames already used by the spherical horizon building.

## Why the route is retired

A nonconstant Hjelmslev observer can be retained only by adding a connection that differentiates
the observer coefficients. That is extra carrier/transport data and changes the source problem.
It violates the mission's static constraint boundary rather than refining it.

The failure strengthens the parent interpretation: the depth-two pairwise collapse is not an
artifact of omitting jet-dependent observer labels. The depth-one spherical building is maximal
inside source-pure projective geometry.

## Parent-theory collision

Equation `(4)` is the standard rigidity of gauge transformations preserving the trivial
connection. Projective Hjelmslev geometries and their relation to affine buildings are also
classical. Their combination here is a useful route exclusion, not new scientific knowledge.

## RH impact audit

`[NO RH IMPACT]` A jet-dependent zeta observer would introduce an external connection and cannot
be advertised as information intrinsic to `zeta`. This is a modelling firewall, not a statement
about zeros.

