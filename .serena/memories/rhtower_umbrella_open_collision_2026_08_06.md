# RHTower umbrella collisions of 2026-08-06 — both FIXED, umbrella green

`lake build GaloisForLFunctions.RHTower` is green again (17284 jobs). Two area-wide name collisions
blocked it; neither is visible to `lake env lean <file>`.

## 1. `RHTower.setIntegral_Ioi_comp_add_right` — fixed on committed files

Declared both in `ComplementaryPacketCofinalIsometry` (real-valued) and in the new
`EulerHedenmalmMobiusStokesInverse` (complex-valued) — two genuinely different lemmas, same name.
Renamed the committed real-valued one to `setIntegral_Ioi_zero_comp_add_right` (it is the `L = 0`
case of the existing `setIntegral_Ioi_comp_add_right'`) and updated its two call sites in
`ComplementaryPacketCofinalIsometry` and `ComplementaryPacketTwoPointDistance`. Those two plus
`ComplementaryPacketAffineFlux` and `ComplementaryPacketLocalZetaTwo` rebuild green.

## 2. `RHTower.deningerExtendByZero` — fixed, but it was a live race

A committed `def` in `DeningerExtendByZero.lean:31` versus a new `theorem` in
`DeningerFineLifting.lean`. The def is the canonical owner (the module is named after it and carries
its `_eq_of_mem` / `_eq_zero` / `_continuous` family), so the theorem was renamed to
`deningerFineAction_extendByZero`, with its single call site in `DeningerFineSurjective.lean` updated.

**This was a partial clobber and had to be repaired mid-flight.** Both files were untracked and
another session rewrote them *between* my read and my edit: the call-site rename landed, the
declaration rename failed because the signature had changed under me (`A : DeningerFineAction F` had
become `A : DeningerFineAction F R`, `ρ : C(X, ℝ)` had become `ρ : ↥R`). For a few seconds the pair
was inconsistent. Recovery rules that follow:

- after any cross-file rename in a live tree, re-grep **every** touched file for the old name before
  moving on; do not trust that all edits applied;
- an Edit that fails on "string not found" in a live tree usually means the file changed, not that you
  mis-copied — re-read before retrying;
- `lake env lean` on the *consumer* compiles against the declaring module's **stale olean**, so a
  rename looks like `unknown identifier` until you `lake build` the declaring module first.

If the Deninger session rewrites those two files from stale content, the collision returns; the fix
above is the one to reapply.

## Detector discipline

A namespace-blind regex scan for duplicate top-level names over `RHTower/` reports ~135 hits, almost
all false positives from per-file namespaces and structure fields (`mk`, `add`, `Hom.comp`, …). Only
the area umbrella build identifies real collisions, and it reports them one at a time. Use
`lake build GaloisForLFunctions.RHTower`; never act on a scan.
