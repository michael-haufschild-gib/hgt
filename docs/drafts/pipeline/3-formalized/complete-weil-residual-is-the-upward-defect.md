# At every overlap the complete Weil residual on Ramanujan modes is the upward defect

- **ID:** complete-weil-residual-is-the-upward-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/completed-shell-energy-is-the-actual-mode-energy.md`;
  premise `hquasi` of `CACT.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_of_quasimodes`.
- **Statement:** For `φ ∈ C²` supported in `[0,1]` with `M = ∫φ² > 0`, every `c > 0`, `m ≥ 1`, and
  `v_N` the normalized Ramanujan vector,
  `‖W_N v_N − E_m(c) v_N + (Up_N v_N/‖g_N‖² − S_m(c) v_N)‖ → 0`, where `E_m(c)` is the completed
  conductor energy, `S_m(c) = 2/(Mφ(m)) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`, and `Up_N` the upward
  non-ratio prime windows.

## Goal
Complete-Weil positivity at a fixed overlap `c > 0` was reduced to norm quasimodes
`‖W v − E_m v‖ → 0`. This theorem removes every block of the residual except the upward windows,
so the premise becomes the single ℓ² statement `Up v/‖g‖² − S_m v → 0`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  Lean `tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm`; standard axioms.

## Proof
`E_m = E_ref − S_m` (`completedConductorEnergy_eq_sub_shellCorrection`), and the exact decomposition
`W = (log N + self − γ + selfErr) I − P + Center(α) − Cross^{far} + PoleErr + Ov − NR` gives

`W v − E_m v = −(P v − (log N − ρ_m) v) + selfErr v + (Center v − α_m v) − Cross^{far} v + PoleErr v
 + (Ov v − Down v) − (Up v − S_m v)`,

using the row identity `NR = (Down + Up)/‖g‖²` (each prime-pair entry minus its ratio part is the
`k`-sum of `Λ(k)k^{-1/2}` times the autocorrelation at `log k ∓ (log n − log j)`; the lag range is
finite by support). The first five terms vanish at every `c`: prime residual (`c`-free), self error
`≤ e^{1/2} c/(2N)`, center residual (`c`-free), far cross error (on `s > 2w`, `s − w > s/2` gives
entries `≤ 152 (∫|φ|)²/M · w² max(n,j)²/|n−j|²`, then the reciprocal-square kernel bound), pole error
(quadratic dilation error once `c ≤ N`). In `Ov v − Down v` the archimedean pairing `log(N/c) G` of
near atoms cancels against the downward divisor weight `Σ_{d∣ℓ} Λ(d) c_m(ℓ/d) = c_m(ℓ) log ℓ − J_m(ℓ)`,
exterior products are a bounded strip; the near center block has entries
`(α/N) ψ(s) ≤ α(1/2 + e^{1/2}/(4N))` because `s ≥ 1/N`. Bounded near-pair numerators over
`O_c(1)` partners in the top fraction of the horizon give `O(1)` squared norm before the `1/log N`
normalization.

## Lean
- `RAPT/TheNonRatioPrimeRowsSplitIntoDownwardAndUpward.lean`: `fullWeilNonRatioMatrix_row_eq`.
- `RAPT/TheReplacementErrorsVanishAtEveryOverlap.lean`: `tendsto_completeWeilSelfError_of_pos`,
  `tendsto_fullWeilPoleErrorMatrix_ramanujan_norm_of_pos`,
  `tendsto_separatedCrossErrorMatrix_ramanujan_norm`.
- `RAPT/TheCompleteWeilResidualIsTheUpwardDefect.lean`: `tendsto_nearCenterVector_norm`,
  `completeWeilMatrix_ramanujan_residual_eq_at_every_overlap`,
  `tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm`, `norm_sq_upwardPrimeVector_sub`.
- Downward block: `CACT.tendsto_normalizedFullNearGammaDownwardVector_norm`.

## Log
- 2026-10-30 — formalized; upward ℓ² limit and positivity corollary in progress (hgt-b0).
