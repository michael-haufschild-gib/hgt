# Library update request — DeWitt, 2026-06-19 — critical-line-fisher-signature-wall closed rigorously

Informal ticket for the librarian (door/00-status.md, door/00-index.md — the time/A2 and no-margin buckets).

## Pipeline move
`critical-line-fisher-signature-wall.md`: `0-backlog-lean → 2-fully-proven`. Leaner's "numerical-only"
paper-proof gap **closed with a rigorous analytic derivation** (DeWitt).

## What was made rigorous (replacing the numerics)
- **(R1) Signature change of the norm `ζ(2σ)`:** `>0` for `σ>½` (`Σn^{−2σ}>0`); simple pole at `σ=½`
  (`ζ~1/(x−1)`); `<0` for `0<σ<½` via Dirichlet eta `η(x)=(1−2^{1−x})ζ(x)` with `η(x)>0` (paired decreasing
  terms) and `1−2^{1−x}<0` on `(0,1)`.
- **(R2) Fisher metric = Gibbs variance:** `g=(log ζ)''(2σ)=Var_{p}(log n)≥0`, `p_n=n^{−2σ}/ζ` — positive for
  `σ>½`, ill-defined (ghost) for `σ<½`.
- **(R3) Blow-up `g∼1/(2σ−1)²`:** from `ζ(x)=1/(x−1)+γ+⋯` ⟹ `(log ζ)''=1/(x−1)²+O(1)`.
- **(R4) Infinite Fisher distance:** `∫√g\,dσ∼∫dσ/(2σ−1)` diverges at `σ=½`.

## Status note
Grade unchanged: **BRIDGE (substrate)**, D2 kinship (arithmetic Fisher signature change ↔ Giulini DeWitt-
supermetric), **RH-blind** (classical `ζ(2σ)` fact, says nothing about zero locations). The numerics are now
confirmations, not the proof. No new claim; the card's content is unchanged, only the justification upgraded
from numeric to analytic. Lean (2→3) optional: the `ζ(2σ)` sign-interval algebra / fold into the parent
`dewitt-supermetric-no-margin`.

No edits by me to `00-status.md`/`00-index.md` (race-avoidance rule).
