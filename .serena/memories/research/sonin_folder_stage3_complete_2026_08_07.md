# Sonin folder: all five cards formalized and at stage 3 (2026-08-07)

## Result

All five cards in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/sonin/` have their
stated theorems unconditionally formalized, and all five now have stage-3 companions in
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/`.

## Pipeline convention (was not obvious)

Stage 3 does **not** move the paper card.  The paper card stays in `2-fully-proven` with
`Stage: 2-fully-proven`; a short *companion* card is created in
`3-formalized/new_scientific_knowledge/` with `Stage: 3-formalized`, a `Paper proof:` back-pointer,
a Lean-module list, a numbered formal theorem chain, and a verification block.  Existing companions
had stale back-pointers (missing the `sonin/` path component) — fixed.  Paper cards now carry a
`Formalized companion:` line.

Stage-3 cards routinely keep unchecked *frontier* gates (e.g. "prove RH or terminally retire").
Those are not formalization gates and do not block stage 3.

## Audit performed

Extracted every backticked identifier from each card, resolved it against a namespace-accurate
declaration index, then ran `#print axioms` on each in a scratch file with minimal imports:

| card | declarations | nonstandard axioms |
|---|---:|---:|
| sonin-principal-shell-cyclic-trace | 547 | 0 |
| cofinal-essential-phase-sonin-coupling-nonannihilation | 165 (+21 new) | 0 |
| sonin-aperture-area-rigidity-and-restriction-defect | 62 | 0 |
| sonin-principal-relative-trace-splitting | 50 | 0 |
| sonin-aperture-principal-cyclic-mass-conservation | 23 + 23 | 0 |

Only `propext`, `Classical.choice`, `Quot.sound` throughout.  All 233 modules cited by the cards are
reachable from the `GaloisForLFunctions.RHTower` umbrella.

## The one real gap found, and closed

The cofinal card states `(3)`, `(4)`, `(4a)`, `(4b)`, `(4c)` for the **normalized** packet
`w_r = u_r/‖u_r‖₂`, but the Lean surface had them only for the raw modulated profile
`soninPacketEven`, whose norm tends to `√(E/2)`, not to 1.  So `‖Z_r w_r‖ → 1` — the card's headline
`(4)` — was not a theorem about the packets the card defines.

Closed in `formal/GaloisForLFunctions/RHTower/SoninNormalizedPacket.lean` (21 declarations, wired
into the `RHTower` umbrella):

- `soninNormalizedPacket`, `soninNormalizedDilatedPacket`, `soninNormalizedDilatedPacket_eq`;
- `norm_soninNormalizedPacket`, `norm_soninNormalizedDilatedPacket`,
  `eventually_soninPacketEven_ne_zero` (the raw packet is eventually nonzero because its norm
  converges to a positive limit, so the normalization never degenerates);
- `soninNormalizedPacketFun` with both Meyer conditions `soninNormalizedPacketFun_zero`,
  `integral_soninNormalizedPacketFun`, plus `soninNormalizedPacket_coeFn` tying the function to the
  `L²` vector;
- `tendsto_norm_soninApertureCoupling_soninNormalizedPacket_sub` `(3)`,
  `tendsto_norm_soninApertureCoupling_apply_soninNormalizedPacket` `(4)`,
  `tendsto_norm_adjoint_soninApertureCoupling_soninNormalizedDilatedPacket_sub` `(4a)`,
  the two `(4b)` halves, and
  `tendsto_pow_mul_norm_soninNormalizedPacketMellin` `(4c)`.

Mechanism: the normalization is a *real positive scalar*, so it passes through every continuous
linear map; every statement is the raw statement divided by `‖u‖`, and `‖u‖` converges to a nonzero
limit.  The recurring proof shape is `hraw.div hnorm hLne` followed by
`refine hdiv.congr fun n => ?_; simp only [Pi.div_apply]; rw [...]` — `Tendsto.div` produces a
`Pi.div` of functions, so `Pi.div_apply` is needed before the pointwise rewrite.

## Documentation fixes

- `bddAbove_soninRefTail` in the big card was stale; the lemma was generalised to
  `GaloisForLFunctions.HTGeometry.bddAbove_fourierTail`.
- `sonin-aperture-principal-cyclic-mass-conservation.md` had **no** Lean table at all despite a
  checked formalization gate; one was written mapping `(1)`–`(13)`.
- Added rows for `(1)`, `(2)`'s internal swap step, and `(6)` to the big card's table.
- The stage-3 `sonin-principal-shell-cyclic-trace` companion covered only the original module while
  the card spans Theorems G–S across ~173 modules; rewritten with a chapter table.  Several of its
  module attributions had to be corrected against the source (Theorem N lives in
  `SoninBurnolLogShellWeyl`, not `SoninBurnolConductorReflection`; Theorem Q's chain lives in
  `SoninApertureFlagChain`, not `SoninFlagChainQuantitative`).

## Remaining frontier (open research, not formalization debt)

Burnol completion and the completed lower floor.  By
`not_bddBelow_soninCompletedPacketValueVar_of_bddAbove` a surviving completion must grow at least as
fast as the coupling energy; by `bddBelow_soninCompletedPacketValueVar_iff` its excess over that
energy must be summable.  Both are single explicit sequences.
