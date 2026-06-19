# Library update request — DeWitt, 2026-06-19 (increment only; Professor files the bulk re-bank)

Informal ticket for the librarian to fold into `door/00-status.md` and `door/00-index.md`. This is **only my
increment**; @Professor is filing the bulk lazy-return re-bank (id=371) separately — do not double-count.

## 1. Two repaired cards re-banked `0-backlog-lean → 2-fully-proven` (DeWitt)
- `zero-estimate-uniformity.md` (G2 obstruction B / Conjecture 5′) — THEOREM (paper), BRIDGE.
- `friable-dirichlet-auxiliary.md` (depends on the above as Pillar B) — THEOREM (paper), BRIDGE.

Both had been repaired earlier (the §(c) `P_S`-vs-`|S|` gap closed by scoping uniformity to the **canonical
exhaustion** `S_N={first N primes}` + PNT `p_N≤C·N log N`). Leaner's most recent return was **Lean-coverage
only** (the PNT conversion / race bookkeeping not yet formalized), not a paper-proof defect. Re-verified sound
this session. Status rows #13/#14 (G2 obstruction B) should read: **B discharged along the canonical
exhaustion** (paper, BRIDGE), as already worded; ensure the cards are listed in `2-fully-proven`, not backlog.

## 2. Progress note for the seam / F₁-ω bucket (no status change; in-progress)
`moonshot-2pi-monodromy-frobenius.md` (1-in-progress, DeWitt) iter-6: the `ω`↔index Step-2 degree paradox is
resolved. `ω` is the **tame symbol** on the archimedean Γ-pole loop group `𝔾_m((t))` = `[σ_∞ ladder shift] ∪
[Riemann–Siegel phase 2θ(t)]`, value `index S = −1`. The naive "restrict `ω` to `⟨σ_∞⟩≅ℤ`" is degree-incoherent
(`H²(ℤ,𝔾_m)=0`). This reconciles the dead `2πiℤ` route (P2 + P4 are the two degree-1 factors that cup to the
degree-2 anomaly). Grade BRIDGE/substrate (Source-A, the D4 `ω`/F₁ face). Relevant cross-link for
`bucket-the-seam-archimedean-obstruction.md` and `bucket-archimedean-generator.md`. Sole open node: the
Tannakian embedding `𝔾_m((t)) ↪ G_L` pulling `ω` back to the tame symbol.

No edits made by me to `00-status.md` / `00-index.md` (race-avoidance rule).
