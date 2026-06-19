# Library ticket — multiplier-dichotomy-theorem proven (BRIDGE), add theorem row

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19
- **Reason:** `multiplier-dichotomy-theorem.md` moved `0-backlog → 2-fully-proven` (grade BRIDGE,
  FOUNDATIONAL). It is the first proven theorem of the Hölder-recentering (two-sources framing, #130).

## Update needed

**Add a new `§C` row** (next free #, e.g. #131) to `docs/drafts/door/00-status.md`:

| # | Shortest version | Bucket | Type | Priority |
|---|---|---|---|---|
| 131 | multiplier-coboundary dichotomy: a rank-1 difference module's solution is holonomic/DA **iff** the multiplier is constant-up-to-σ-coboundary (CC); else hypertranscendental. **PROVED HERE:** (I) CC ⟹ gauge-trivial, Galois `⊂𝔾_m`, DA solution `f=g·c^z`; (II) degree-at-∞ obstruction (`g(z+1)/g(z)→1`) ⟹ non-constant-polynomial multipliers are non-CC, putting `Γ` (a=z) on the hypertranscendental side. **IMPORT:** not-CC ⟹ hypertranscendental (Hölder 1887 for `Γ`; ADH/Hardouin–Singer general). Corollary: the CC class **is** the Source-A/Source-B (archimedean/prime) divide — every prime place is CC (holonomic, Source B), the archimedean place is the unique non-CC place (Hölder, Source A), C5 = their weld. `F_q` shadow: all places CC ⟹ holonomic (Weil), predicts corank 1 vs ∞ (#121). | [[bucket-archimedean-generator]] / [[G1-difference-holder]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |

Card path: `docs/drafts/pipeline/2-fully-proven/multiplier-dichotomy-theorem.md`.

## Notes for the ledger

- This **grounds 00-status #130** (two sources of hypertranscendence): #130 was CONJECTURE/FRAMING; the
  multiplier-coboundary *backbone* of that framing is now a proven BRIDGE theorem. Suggest annotating #130's
  row: "the multiplier dichotomy backbone is now proven (#131)."
- Door-2 verdict **BRIDGE** (each case is a single parent; the organizing divide is the payload) — consistent
  with §59/§60 Source-B BRIDGE. **Does not earn C5.** C5 remains the weld (non-CC × CC, joint), open.
- Honest import flag: case (III) cites Hölder 1887 (`Γ`, solid) + ADH/Hardouin–Singer (general rational
  multiplier — recalled reference, to verify against literature before publication-ready). The banked
  corollary depends only on the `Γ` case (Hölder).
- `00-index.md`: the `[[bucket-archimedean-generator]]` and `[[G1-difference-holder]]` bucket rows may note
  the dichotomy as the proven Source-A/B separator.
