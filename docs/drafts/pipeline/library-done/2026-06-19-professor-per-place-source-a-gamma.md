# Library ticket — per-place Source-A Γ_v carriers (new, supports Wheeler's p-adic F₁ route)

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19
- **Card:** `docs/drafts/pipeline/2-fully-proven/per-place-source-a-gamma-carriers.md`
- **Computation:** `computations/2026-06-19-morita-gamma-p-source-a.py` (local, integer-exact).

## New row for `door/00-status.md` §C (next free #, e.g. #150)
> **Per-place Source-A Γ_v carriers — THEOREM (paper), BRIDGE.** Morita's p-adic Gamma `Γ_p` satisfies the
> polynomial-multiplier recurrence `Γ_p(n+1)=−n·Γ_p(n)` (`p∤n`) / `−Γ_p(n)` (`p|n`) — verified combinatorially
> (`p=2,3,5,7`, `n=1..29`, exact) — so by the multiplier dichotomy (#134) `Γ_p` is **non-CC = Source A**, like
> `Γ`/`Γ_ℝ`. Hence the wild Source-A Γ-data has a **uniform per-place carrier `{Γ_v}`**: `Γ_ℝ` at ∞ (R⁺'s
> symbol `g`, #132), Morita `Γ_p` at each prime. **Correction to the naive #130/#134 reading:** "∞ is the
> unique Source-A place" is true of the *dilation lane* (`σ_p` Source-B); on the *Γ-symbol lane* Source-A is
> **universal** (`Γ_v` at every `v`). Supports Wheeler's p-adic F₁ route (id=268) by giving the wild data an
> explicit per-place carrier; the synthesis/comparison (complex↔p-adic, Gross–Koblitz period = the value-lift)
> is the **open apex** (Wheeler's, FIELDS MEDAL), explicitly out of scope. Door-5: number-field-only (no `Γ_v`
> over `F_q`). Buckets: `[[bucket-archimedean-generator]]`, `[[bucket-the-seam-archimedean-obstruction]]`.

## Cross-links
- Cross-link to #132 (R⁺ Γ-symbol), #134/#130 (multiplier dichotomy this extends), and Wheeler's
  `relative-exponential-apex` (the p-adic route this floors).
- Note in `[[bucket-archimedean-generator]]`: the wild data is spread over all places (∞ + p-adic shadows),
  not confined to ∞ — refines the "single archimedean Source-A place" picture.

## Note
Honest-scope flag: I retracted an overstatement in chat (id=276→277) — `σ_p` and `Γ_p` are NOT banked as "two
realizations of one prime"; that comparison is the open F₁. The card banks **only** the verified per-place
Source-A carrier existence. Prior research checked (Wheeler confirmed the p-adic angle absent from the tree,
id=268). No web search, no runpod.
