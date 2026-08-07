# Sonin folder: all five cards formalized and MOVED to stage 3 (2026-08-07)

## Result

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin/` **no longer exists**.  All
five cards now live in `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/sonin/`, each
with `Stage: 3-formalized`, beside its `<id>-formalized.md` certificate companion.

## Pipeline convention

Promotion to stage 3 **moves** the paper card (`git mv`) and sets its `Stage:` field; the short
formalized companion sits in the same directory.  Leaving the paper card in stage 2 because a
companion exists is wrong — the stage is a property of the card's location.  After moving, repoint:
the companion's `Paper proof:`, the card's `Formalized companion:`, inbound links from other stages,
and any `../`-relative parent links whose depth changed (one such was
`../1-in-progress/sonin-log-shell-cyclic-finite-part-descent.md`, now three levels up).

Stage-3 cards legitimately keep an unchecked `3 → 4 publication-ready` gate — the next stage's gate,
not formalization debt.  Only the cofinal card still carries one.

## Gate state (all five)

| card | open gates |
|---|---:|
| `sonin-principal-shell-cyclic-trace` | 0 |
| `sonin-aperture-area-rigidity-and-restriction-defect` | 0 |
| `sonin-aperture-principal-cyclic-mass-conservation` | 0 |
| `sonin-principal-relative-trace-splitting` | 0 |
| `cofinal-essential-phase-sonin-coupling-nonannihilation` | 1 (`3 → 4 publication-ready`) |

## Audit performed

Every backticked identifier in all ten files resolved against a namespace-accurate declaration
index, then `#print axioms` on each in scratch files with minimal imports (`lake env lean`):

| card | declarations | nonstandard axioms |
|---|---:|---:|
| sonin-principal-shell-cyclic-trace | 554 | 0 |
| cofinal-essential-phase-sonin-coupling-nonannihilation | 186 | 0 |
| sonin-aperture-area-rigidity-and-restriction-defect | 70 | 0 |
| sonin-aperture-principal-cyclic-mass-conservation | 57 | 0 |
| sonin-principal-relative-trace-splitting | 52 | 0 |

Only `propext`, `Classical.choice`, `Quot.sound`.  1215 `formal/GaloisForLFunctions/*.lean` paths
cited by the cards all exist; every cited module is reachable from the `RHTower` umbrella;
`formal lint passed`; `LEAN_GAPS.md` reports no active `sorry`/`admit`/`axiom`/`opaque`/`unsafe`.

## Two real gaps found and closed

**1. The normalized packet family.**  The cofinal card states `(3)`, `(4)`, `(4a)`, `(4b)`, `(4c)`
for `w_r = u_r/‖u_r‖₂`, but Lean had them only for the raw `soninPacketEven`, whose norm tends to
`√(E/2)` — so the headline `‖Z_r w_r‖ → 1` was not a theorem about the card's own packets.  Closed
in `SoninNormalizedPacket.lean` (21 declarations): the unit packet and its inverse dilate, unit-norm
proofs plus eventual nonvanishing of the raw packet, both Meyer conditions carried across the
normalization at function level with the `L²`-class identification, and all five limits restated.
Proof shape: `hraw.div hnorm hLne`, then `refine hdiv.congr fun n => ?_; simp only [Pi.div_apply];
rw [...]` — `Tendsto.div` yields a `Pi.div`, so `Pi.div_apply` is needed before the rewrite.

**2. The Burnol conductor.**  See `mem:research/sonin_burnol_weld_terminally_retired_2026_08_07`.

## Documentation defects fixed

- `sonin-aperture-principal-cyclic-mass-conservation.md` had a checked formalization gate and **no
  Lean table**; one was written mapping `(1)`–`(13)`.
- `bddAbove_soninRefTail` was stale (generalised to `HTGeometry.bddAbove_fourierTail`).
- Added table rows for `(1)`, `(2)`'s internal swap step, `(6)` to the big card.
- Two stage-3 companions were missing entirely; the `sonin-principal-shell-cyclic-trace` companion
  covered one module while the card spans Theorems G–S across ~174 modules — rewritten with a
  chapter table, several module attributions corrected against source (Theorem N is in
  `SoninBurnolLogShellWeyl`, not `SoninBurnolConductorReflection`; Theorem Q's chain is in
  `SoninApertureFlagChain`, not `SoninFlagChainQuantitative`).
