# Review-1111 assemblies of proved pieces

- **ID:** review-1111-assemblies
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, "Assemblies of proved pieces".
- **Goal:** a complete, unconditional Lean solution for each task, easiest first.

## Status

| Task | Status |
|---|---|
| A78 | Already a theorem: `SurfaceOfSpecZ.ScaleLocality.finite_top_negative_in_every_window` (any finite top layer, no separation, windows longer than `card(S)π/Γ`). |
| A47 | Already formalized: `3-formalized/one-quartet-current-constant.md`. |
| A136 | Frontier map now grades the comb index, trace classification, Laguerre tails, horocycle and detector moment modules [L]. `ReflectedHalvesAreNotDirichletSeries` compiles cleanly. `TheShiftedSelbergFormIsAHarmonicModel`, `TheMobiusKernelConvergesInMean` are under active peer edits (MZF/Levinson card A111): not touched. |
| A134 | Owned by the peer Levinson card `levinson-gate-from-below-square-root-twists.md` (A111): not duplicated. |
| A133 | Formalized: `3-formalized/artin-degree-two-character-of-the-cube-roots-of-two.md`. |
| A137, A135, A89, A132 | Queued. |

## Queued notes

- A137: an asymptotic of `x^{−Θ}M_φ(x)` needs control of `Σ 1/ζ′(ρ)` near the top line; the
  explicit formula for `Λ` uses integral multiplicities and has no such input. Decide the
  strongest unconditional statement before formalizing.
