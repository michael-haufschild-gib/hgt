# Almost every zero ordinate of a short window is nearly Weil-positive

- **ID:** almost-every-zero-ordinate-nearly-weil-positive
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** frontier map, "Averaged positivity" row: "individual heights, in particular zero
  ordinates (selection)"; B1.4 ("to every height, in particular zero ordinates"); walls ledger 3.14.
- **Statement.** There are `C, Γ₀` such that for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `η > 0`, the set `Z` of
  zero copies with ordinate in `[Γ, Γ+H]` has `#Z ≥ H log Γ/(16π)`, at most `C H/η` copies of `Z` have
  `Φ(Im q) > η`, and at every other `q ∈ Z`, for all `A ≥ 0` and real `F₀ ∈ C²_c([−A,A])`,
  `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ −4η(A+1)² e^A N(F₀)²` at `γ = Im q`. The exceptional ordinates are a
  proportion `O(1/(η log Γ))`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryZeroOrdinateIsNearlyWeilPositive.lean`:
`pairWeight`, `sum_offLineField_le_split`, `exists_sum_offLineField_zeroOrdinates_le`,
`exists_shortWindow_almostEvery_zeroOrdinate_nearly_positive`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`. Wired into `ArithmeticCastelnuovoSeveri.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. `Σ_{q'∈Z} Φ(Im q') = Σ_q Σ_{q'∈Z} δ_q²(1 + (Im q − Im q')²)^{−2}`.
2. Copies `q` with ordinate in `[Γ−H, Γ+2H]`: the inner sum is at most `δ_q² ℒ(Im q)`, with the Lorentzian
   mass `ℒ(t) ≤ 8(c + log(|t|+4)) ≤ 8(c+3) log Γ`; and `Σ δ_q² ≤ C₃ H/log Γ`
   (`exists_window_sum_sq_depth_le`). Contribution `≤ 8(c+3)C₃ H`.
3. Other copies are at distance `≥ H` from every ordinate of `Z`, so `(1+x²)^{−2} ≤ H^{−2}(1+x²)^{−1}`,
   `δ² ≤ 1/4`, and the double sum is `≤ (1/(4H²)) Σ_{q'∈Z} ℒ(Im q') ≤ 6(c+3)(log Γ)²/H ≤ H`
   (`#Z ≤ 3H log Γ`).
4. Markov over `Z`: `η·#{Φ > η} ≤ Σ_Z Φ ≤ C H`. The core count `#Z ≥ H log Γ/(16π)` is
   `exists_window_core_count`. Near-positivity at the good ordinates is
   `neg_offLineField_le_fullZeroForm`.
