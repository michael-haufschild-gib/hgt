# Critical* HTGeometry: folder split and heartbeat elimination

- **ID:** critical-heartbeat-elimination
- **Stage:** 1-in-progress
- **Type:** tooling / Lean hygiene
- **Target:** every `GaloisForLFunctions.HTGeometry.Critical.*` module compiles with no
  `set_option maxHeartbeats` line at all, and no entry in `formal/heartbeat-baseline.txt`.

## Folder split (done)

`HTGeometry/Critical<Bucket><Rest>.lean` → `HTGeometry/Critical/<Bucket>/<Rest>.lean`, module
`…HTGeometry.Critical.<Bucket>.<Rest>`, for Schur, Block, Geometric, Sheet, Source, Normal,
Observation, Chart, Coefficient, Field, RawCoordinate, Reciprocal — 168 modules. Per-bucket
umbrellas collected by `HTGeometry/Critical.lean`, which is the single line the area umbrella
imports. Index files regenerated; every import in the tree resolves.

## What actually costs heartbeats here

Mentioning the ring tower is cheap (~100 heartbeats). What is expensive:

- a tactic that abstracts a goal containing the tower (`rw`, `obtain`, `refine`, `simp`): tens of
  thousands of heartbeats per step, because the goal and its instance arguments are rebuilt and
  re-checked;
- a written-out type that the elaborator must synthesize a second time and compare against what it
  already has (a redundant ascription, or `haveI : <tower type> := lemma`);
- deep tower instance searches: `Algebra ↥obsField ↥normalClosure` 64k,
  `Algebra ↥srcField ↥normalClosure` 38k, `IsScalarTower ↥obsField ↥srcField ↥algClosure` 82k,
  `Algebra ↥obsField ↥(AlgHom.fieldRange σ)` 69k, `Algebra.IsSeparable ↥obsField ↥normalClosure`
  over 200k on its own;
- the kernel re-checking a large proof term built from inline `let`s rather than named constants.

## Fixes that worked (each verified by compiling at the default budget)

1. Do the rewriting where the terms are abstract, then apply the result over the tower once:
   `Critical/Geometric/SheetUpperBound` (cast side condition), `Critical/Normal/ClosureArcReduction`
   (shifted-tail reduction), `Critical/Reciprocal/Numerator` (power bookkeeping),
   `Critical/Sheet/SchurPlacePullback` (ratio in a valuation subring).
2. Replace `rw [<definition>]`-then-apply by the direct application: delta-unification instead of
   motive construction (`SheetUpperBound`).
3. Replace `rw`/`simp` steps on tower-sized goals by term-mode `congrArg`/`Eq.trans`
   (`Schur/CollisionSingular` 12M → default, `Sheet/LabelInertiaOrbit` helpers).
4. Extract a `have` whose type is tower-sized into a named lemma — this also cuts the kernel cost
   of the parent (`Sheet/LabelInertiaOrbit`, `Geometric/NormalClosureTower`).
5. Prove an expensive instance by its explicit route instead of `infer_instance`, split into named
   facts: `Critical/Geometric/NormalClosureTower` now carries normality, algebraicity, integrality
   and separability of the normal closure once, all at the default budget.
6. Reuse mathlib instead of a local lemma where one exists (`MulAction.IsBlock.translate`).

## Fixes that did *not* work (do not repeat)

- **Splitting a declaration whose cost is a shared instance tower makes it worse**: each part
  re-derives the tower. `Geometric/MonodromyFaithful` got slower split into three.
- **Dropping the written-out type mechanically across the tree** (195 sites) broke typeclass
  resolution where the type guides instance selection — it took `Critical/Observation/Field` down
  with it. The change is only safe per site, with a compile.
- Naming tower instances in a shared upstream module (`Critical/Geometric/Monodromy`) changes which
  instance terms the dependents elaborate, which desynchronises every dependent olean
  (`(kernel) unknown constant … criticalGeometricSheet._proof_2`). New modules are safe; editing
  the proof content of a widely imported one is not, unless the dependent subtree is rebuilt.

## Verification

A module is checked by compiling a copy with its `maxHeartbeats` line removed, against the oleans
of the rebuilt tree. The rename invalidated 204 modules; the rebuild pass compiles each at the
default budget first and deletes the escalation whenever that succeeds, so measurement and fix are
the same action.
