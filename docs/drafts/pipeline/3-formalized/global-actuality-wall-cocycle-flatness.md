# Every global possibility-wall map is exactly flat

- **ID:** `global-actuality-wall-cocycle-flatness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT NO-GO / POSITIVE CLASSIFICATION
- **Status:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../2-fully-proven/not_new_scientific_knowledge/global-actuality-wall-cocycle-flatness.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ActualityWallFlatness.lean`

## Exact formal statement

For arbitrary types of states \(X\) and walls \(W\), an arbitrary global side assignment is a
function

\[
\mathsf{side}:W\to X\to\mathrm{Bool}.
\]

The relative profile

\[
\mathsf{profile}_b(x)(w)
  =\mathsf{side}(w,x)\mathbin{\mathtt{xor}}\mathsf{side}(w,b)
\]

is formalized as `actualityWallProfile`.

The module proves:

- `actualityWallProfile_self`: a state has the zero profile relative to itself;
- `actualityWallProfile_symm`: separation is symmetric;
- `actualityWallProfile_difference`: two profiles with one base differ by their direct profile;
- `actualityWallProfile_changeBase`: changing basepoint is one Boolean translation;
- `actualityWallProfile_cocycle`: relative profiles form an exact cocycle;
- `actualityWallProfile_triangleHolonomy`: every triangular holonomy is zero;
- `actualityWallProfile_eq_iff`: profile fibers are exactly wall-indistinguishability classes;
- `actualityWallProfile_injective_iff`: profiles are faithful exactly when walls separate points;
- `globalActualityWallCoordinate_flat`: every wall coordinate is a Boolean vertex coboundary and
  has zero XOR holonomy on every finite closed walk of every simple graph on \(X\).

The final theorem reuses the corpus's exact Boolean coboundary criterion from
`BooleanEdgeFieldWitnesses.lean` and `CoherenceFlatness.lean`.

## Match to paper theorem

Characteristic functions identify subsets of \(W\) with functions \(W\to\mathrm{Bool}\), and
pointwise XOR with symmetric difference. Therefore the formal difference, base-change, cocycle,
triangle, fiber, and injectivity theorems are exactly clauses 1--8 of the paper statement in
Boolean-coordinate form.

`globalActualityWallCoordinate_flat` strengthens the triangular clause to every finite closed walk:
one global wall coordinate is an exact vertex coboundary on any chosen graph of states.

No physical typing appears in the theorem. It does not assume or conclude gravity, spacetime,
quantum theory, or gauge forces.

## Verification

Direct source check:

```text
lake env lean GaloisForLFunctions/HTGeometry/ActualityWallFlatness.lean
```

passed without output.

Final module audit:

```text
lake build GaloisForLFunctions.HTGeometry.ActualityWallFlatness
```

completed successfully: `993/993`.

Scratch `#print axioms` audit:

```text
actualityWallProfile_cocycle
  [Quot.sound]

actualityWallProfile_triangleHolonomy
  [Quot.sound]

actualityWallProfile_injective_iff
  [propext, Quot.sound]

globalActualityWallCoordinate_flat
  []
```

These are standard Lean foundations; the strongest arbitrary-loop flatness theorem has no listed
axiom dependency.

## Scientific status

The mathematics is a Boolean coboundary identity and is not new scientific knowledge. Its exact
physical lesson is restrictive:

> A single global binary map of possibilities cannot carry gravitational holonomy. If
> event-created boundaries underlie spacetime, gravity must be obstruction to global wall
> coordinates, not motion between sides of already global walls.

The parent physical identification remains conjectural.

## Gates

- [x] exact dependency-closed paper theorem matched
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] direct `lake env lean` check passed
- [x] final single-module `lake build` passed
- [x] scratch axiom audit passed
- [x] repository formal lint passed
- [x] novelty downgraded to `[REDISCOVERED] [BRIDGE]`

## Log

- 2026-07-29 — exact global-wall profile classification and arbitrary closed-walk flatness
  formalized unconditionally.
- 2026-07-29 — repository formal lint passed.
