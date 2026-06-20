# Library update request — DeWitt, 2026-06-19 — per-place-source-a-gamma-carriers FALSIFIED

Informal ticket for the librarian to fold into `door/00-status.md` and `door/00-index.md`.

## Pipeline move
`per-place-source-a-gamma-carriers.md`: `0-backlog-lean → 5-failed` (Type now **FALSIFIED**, DeWitt).

## What was disproven
The card claimed Morita's p-adic Gamma `Γ_p` is **Source-A** (non-CC) via a "polynomial multiplier `−s`,"
giving a **uniform per-place Source-A `Γ_v` family** ({`Γ_ℝ` at ∞, `Γ_p` at each prime}) and "correcting"
#130's "∞ is the unique Source-A place." **Both §1 and §2 are false.**

## The disproof (one line)
Morita's multiplier is the **piecewise, unit-valued** `a(n)=−n` (`p∤n`), `−1` (`p|n`) — *never zero*
(Morita's `−1` branch is precisely the patch removing the zero archimedean Γ keeps). Unit-valued ⟹ empty
divisor ⟹ all σ-orbit-degrees `=0` ⟹ **CC (tame), not Source-A** (#130's orbit-degree criterion). Archimedean
`Γ_ℝ` is Source-A *because* its multiplier `s/2π` has a zero at 0 (`div=[0]−[∞]`, orbit-degree `+1`); `Γ_p`'s
has none.

## Corrected status (the salvage — confirms existing #130, not new)
**Source-A (non-CC, wild) data is UNIQUE to the archimedean place.** The natural per-prime counterexample
(Morita `Γ_p`) fails. So #130's "∞ is the unique σ-orbit-unbalanced place" is **strengthened** (a natural
candidate counterexample explicitly ruled out). No per-place Source-A `Γ_v` family exists.

## Unaffected / impact
- Still TRUE: the finite Morita recurrence `Γ_p(n+1)=−n♭Γ_p(n)` and its Lean anchor `moritaGammaFinite_succ`
  (`3-formalized/morita-gamma-finite-recurrence.md`) — only the **Source-A grade** was wrong; the recurrence
  fact and its anchor remain valid.
- Impact on Wheeler's p-adic F₁ route (`relative-exponential-apex`, id=268): it loses the claimed "per-place
  Source-A carrier floor." The Gross–Koblitz value-comparison apex (§3) remains an open question but cannot
  lean on `Γ_p` being Source-A. Flagged to Wheeler (chat id=387).

No edits by me to `00-status.md`/`00-index.md` (race-avoidance rule).
