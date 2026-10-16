# CHMD: single-prime-power window (2026-10-16)

User pivot: "chain-variance domination at a fixed prime power with the explicit weight". STATUS MUST-1561.
Card: 3-formalized/chmd-single-prime-window-2026-10-16.md. Module `RHTower/CHMDSinglePrimeWindow` (ns RHTower.CHMDPolar), 17 decls.

## Results
- `weilLevyForm f := γ(0)∫f² + (NonnegativeCone.jumpEnergy f).toReal`; **`sourceEnergy_compactLift_eq_levy_sub_tsum_cross`**:
  E(compactLift v) = weilLevyForm(Θv) − Σ' n ∫ phiDoobPrimeCross v n (explicit-formula form, via ground-state cancellation).
- `phiDoobPrimeCross_eq_zero_of_window` (supp ⊆ Ioo a (a+L), L ≤ log n ⇒ cross n ≡ 0); `tsum_cross_eq_sum_of_window`
  (L ≤ log m ⇒ only n ∈ Ico 2 m); `…_levy_of_window_le_log_two`; **`…_levy_sub_cross_two`** (L ≤ log 3).
- **`integral_phiDoobPrimeCross_le_strips`**: ∫cross n ≤ atom n · (mass of (Θv)² on the two end strips of width L − log n).
- `PrimeTwoDomination v := ∫cross 2 ≤ weilLevyForm(Θv)`; `sourceEnergy_nonneg_iff_primeTwoDomination` (window ≤ log 3);
  `primeTwoDomination_of_riemannHypothesis` (primitive tests); `primeTwoDomination_of_strip_coercivity`; `vonMangoldtAtom_two`.

## Lesson
Per-prime-power domination J_n ≥ D_n ⟺ anticorrelation at lag log n (false termwise for positive tests). The window
form is the honest fixed-prime-power statement; it is quantitative (corpus WeilLevy lane: nonneg cone ≤ 12/25, deficit
−0.0033 at log 2). Next: sign law on the one-signed odd cone (all cross terms ≤ 0 for windows ≤ 2 log 2).

## Lean traps
- `HasCompactSupport.pow` does not exist; use `funext … pow_two` + `.mul_left`. `two_mul_le_add_sq a b : 2*a*b ≤ a^2+b^2`.
- `Nat.Ico_succ_singleton`, `Finset.Ico_self` for finite windows; `Real.log_le_log (hx : 0 < x) (h : x ≤ y)`.
