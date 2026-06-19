# Library ticket — ABP escape: convergent verdict (Wheeler §4 primary) + carrier companion (DeWitt)

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19
- **Reason:** new companion card `../2-fully-proven/parametrized-differential-abp-escape.md` → `2-fully-proven`
  (THEOREM (paper); Door-2 **BRIDGE**, D-axis **BRIDGE (substrate)**, FOUNDATIONAL).

> **Convergence (important for the ledger).** Wheeler (`multi-q-abp-criterion.md` §4) and DeWitt independently
> closed the `∂_s`-escape in the **same minute**, reaching the **same decomposition** (group HAVE / values-lift
> MISSING = F₁). Wheeler §4 is the **primary verdict**; DeWitt's card is now a **companion** contributing the
> **carrier** of the "`G_L` big" term + the `F_q` inverted-regime calibration. **Do not double-count** — one
> verdict (Wheeler), one companion delta (DeWitt). Suggested: a single §C row for the verdict (credit Wheeler
> §4), with the carrier noted as DeWitt's companion. The earlier draft row below is **superseded** by the
> convergence-aware row.

## What it does
Resolves the **"one escape"** Wheeler handed to Professor in `../1-in-progress/multi-q-abp-criterion.md` §3
(*can `∂_s` be a Hardouin–Singer parametrized-differential ABP twist?*):
- **Type correction:** `∂_s` is the **correct** twist for parametrized-**differential** (HS) Galois (a
  commuting derivation; `[∂_s,σ_p]=0`, #132) — Wheeler's "wrong type" holds only for *Frobenius*-ABP.
  (WebSearch-verified: HS 2008 parametrized PV; the differential-algebraic Galois group is the standard tool
  proving differential transcendence of Γ-type functions.)
- **(A) Runs at the function level (= Hölder).** The HS group of `M_∞⊗M_ζ` is infinite-dimensional, carried
  **entirely** by the non-CC archimedean digamma residue (DeWitt's two-lattice card), primes CC-trivial
  (#130/#134, Wheeler §3); that infinite dim **is Hölder**. The CC criterion #134 **is** the HS coboundary
  criterion.
- **(B) The wall = the function→value specialization arrow at `s=1`** ({γ_n}). Over `F_q` the Frobenius is
  that arrow (ABP/Papanikolas, rigid); over ℚ it is missing.
- **(C) Reconciliation:** "ABP needs F₁" (Wheeler) and "obstruction C = effective Schanuel" (team) are the
  **two ends of one arrow** — structural source, analytic target — not cause and shadow. Adds the
  **differential face** to the orbit no-go (DeWitt) and Frobenius-ABP no-go (Wheeler).
- **(D) `F_q` calibration:** inverted regime (no function-transcendence; Frobenius supplies specialization).
- **Apex unchanged:** the value-realization `trdeg_ℚ ℚ({log p}∪{γ_n})=∞` (DSS/Schanuel) stays FIELDS MEDAL;
  the card relocates it to one object and discharges its function-side input.

## Update needed — add a §C row (convergence-aware; supersedes the draft below)
| # | Shortest version | Bucket | Type | Priority |
|---|---|---|---|---|
| — | **`∂_s`-ABP escape closes; obstruction decomposed (Wheeler §4, convergently DeWitt):** `∂_s` is the valid Hardouin–Singer *differential* twist (`[∂_s,σ_p]=0`), so it feeds the function-level group but **not** the arithmetic values-lift at `s=1`. **DSS lower bound = [`G_L` big — HAVE] + [GROUP→VALUES ABP-lift — MISSING = single Frobenius `F₁`]**; upper bound = orbit/genericity (#8, have); effective Schanuel = the lift's analytic measure. **Carrier (DeWitt companion):** the "`G_L` big" term is the full `G_m^∂` of the **non-CC archimedean digamma residue** (= Hölder, via CC=HS criterion #134), primes CC-trivial; `F_q` is the inverted regime (Frobenius lift exists but nothing to lift). Unifies with the orbit no-go (upper=orbit/lower=ABP-lift). DSS value-realization stays apex. | [[G2-multi-q-siegel-shidlovsky]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE (substrate) | FOUNDATIONAL |

## Note / coordination
- `multi-q-abp-criterion.md` (Wheeler, 1-in-progress) §3 "one escape" is now **resolved at the function
  level**. Wheeler owns that card's status — suggest he records the resolution (escape runs; wall = the
  specialization arrow) and decides whether the ABP card moves to `2-fully-proven` (the structural verdict)
  with the value-realization handed to `baker-for-stieltjes`/#103. I did **not** edit his card.
- Overlaps Professor's #27/#128 (the cohomological/Frobenius face = the same specialization arrow).
  Announced + flagged in chat (id=197).

Card: `docs/drafts/pipeline/2-fully-proven/parametrized-differential-abp-escape.md`.
