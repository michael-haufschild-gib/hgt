# Weil positivity at almost every zero ordinate

- **ID:** almost-every-zero-ordinate-weil-positive
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** B1.4 "selection … in particular zero ordinates"; frontier map "Averaged positivity" row
  ("individual heights, in particular zero ordinates"); walls ledger 3.14.
- **Statement.** For every zero copy `q`, aperture `A ≥ 0` and nonnegative `F₀ ∈ C²_c([−A,A])`, at
  `γ = Im q`: `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ (∫F₀)² − 4(A+1)² e^A N(F₀)² Φ(γ)`. Hence, in every window
  `[Γ, Γ+H]`, `Γ^{99/100} ≤ H ≤ Γ/8`, all but `C H/η` of the `≥ H log Γ/(16π)` zero copies satisfy
  `Q_{Im q}(F₀) ≥ (∫F₀)² − 4η(A+1)² e^A N(F₀)²` for all apertures and all nonnegative tests; this is
  `> 0` whenever `4η(A+1)² e^A N(F₀)² < (∫F₀)²`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryZeroOrdinateIsWeilPositive.lean`:
`integral_le_norm_paperFT_depthSumProfile_self`, `tsum_depthDiff_le_offLineField`,
`sq_integral_sub_offLineField_le_fullZeroForm`, `exists_shortWindow_almostEvery_zeroOrdinate_positive`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `ArithmeticCastelnuovoSeveri.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. Quadrature with the single zero `ρ₀ = q` kept:
   `Re W(F₀e^{iγ·}) ≥ m_{ρ₀}|F̂(depthSum_{ρ₀})(−γ)|² − Σ_ρ m_ρ d_ρ(γ)`.
2. At `γ = Im ρ₀` the phase cancels: `F̂(depthSum_{ρ₀})(−Im ρ₀) = ∫F₀(u) cosh(δu) du ≥ ∫F₀` for `F₀ ≥ 0`,
   and `m_{ρ₀} ≥ 1`.
3. `Σ_ρ m_ρ d_ρ(γ) ≤ 4(A+1)² e^A N² Φ(γ)` (depth-difference law of
   `AlmostEveryHeightIsNearlyWeilPositive`).
4. The count of exceptional ordinates is `exists_shortWindow_almostEvery_zeroOrdinate_nearly_positive`.
