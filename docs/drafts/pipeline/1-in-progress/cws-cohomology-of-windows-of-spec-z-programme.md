# Cohomology of Windows of Spec ℤ (CWS) — programme card

- **ID:** CWS
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7
- **Statement:** attach to each window length `A` a finite arithmetic object whose `h¹` is Weil's
  window form; determine the window datum exactly; decide which carriers (count, capacity, placement)
  can realize `h¹`; calibrate (curves, prime-free windows, first prime); locate selection.

## Goal
Develop the field of §2.7: answer its questions by Lean theorems, build its tools. Folder
`formal/GaloisForLFunctions/CohomologyOfWindowsOfSpecZ/`, umbrella `CohomologyOfWindowsOfSpecZ.lean`,
README there.

## Lean modules (planned order)
TheWindowDatum, TheCanonicalClassOfAWindow, TheFirstPrimeFold, TheFrobeniusAtInfinityOfAWindow,
TheWindowIndex, TheWindowGenusIsAYoungConjugate, WindowRealizations, WindowNaiveHeights,
TheWindowCohomologyOfACurve, TheSelectionBatteryOfWindows.

## Paper statements (to formalize)
1. Canonical class: for `H` supported in `[−A,0]`, `n ≤ e^A`, `ℓ = log n`:
   `w‖H − τ_ℓH‖² − 2w‖H‖² = w∫_{−A}^{−ℓ}(H(u) − H(u+ℓ))² − w∫_W m_n H²`, `m_n = 1[u ≤ −ℓ] + 1[u ≥ ℓ − A]`;
   `∫_W m_n = 2(A − ℓ)`; Riesz degree `Σ 2w_n(A − log n)`.
2. First-prime fold: `log 2 ≤ A < log 3` ⇒ active set `{2}`; `log 2 ≤ A < log 4` ⇒ `I₋ ∩ I₊ = ∅`.
3. Window involution: `Q(H(−A−·)) = Q(H)`; multiplier `e^{−(s−½)A}`.
4. Young: `2Lx − x(log x − 1) ≤ e^{2L}`, equality iff `x = e^{2L}`.
5. Realizations: exist ⇔ RH; infinite positive index on every window.

## Open
See README §7.

## Log
- 2026-11-02 — created; README first draft written.
