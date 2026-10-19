# Square-Root Threshold: frontier (SRT-4, SRT-5)

- **ID:** srt-frontier
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the proved items; CONJECTURE for the open targets
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md §5
- **Statement:** Locate, at height `T` and prime length `X = e^{2a}`, the information in localized
  Weil forms that makes a zero of depth `δ` visible, and prove the unconditional ranges.

## Goal
Map the plane (height `T`, prime length `X`, height-window length `ℓ`) into regions where
positivity of localized Weil forms of `ζ` is (a) proved unconditionally, (b) equivalent to a
zero-free region of a given depth, or (c) RH-strength.

## Gates
- [x] 0 → 1  in-progress: well-posed; SRT-1 to SRT-3 proved in Lean
- [ ] 1 → 2  fully-proven: complete paper proofs of the frontier items below
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Proved (Lean, unconditional, standard axioms only)
- SRT-1 `isolatedPairConfig_weil_nonneg_iff`: exact visibility law; depth-`δ` pair visible at
  `X ≈ (4δL)^{1/δ}`.
- SRT-2 `re_windowedW_nonneg_of_aperture_nonneg`, `exists_offLine_lattice_windowed_nonneg`: window
  averages at resolution `r` see only aperture-`r` positivity; off-line configurations pass them.
- SRT-3 `windowedW_eq_integral_heightShift`, `zetaZeroConfig_re_W_nonneg_of_small_aperture`
  (aperture `e^{−50}`), `re_integral_heightShift_zetaZeroConfig_nonneg`: windows of length
  `≳ e^{50}` give nonnegative height averages for `ζ` at every aperture.
- SRT-5a `exists_zetaZeroConfig_re_W_heightShift_nonneg`, `zetaZeroConfig_re_W_heightShift_ge`:
  for a fixed profile, single-height positivity holds for `X ≲ (log T/68)²`. This range matches
  the visibility range of depth-`½` zeros (`X ≈ 4L²`).

## Open targets (in order)
1. **SRT-4a exact windowed mean value.** For a window `η` on `[-r, r]`:
   `∫ |h_η(−2πξ)|² |Σ c_j e^{2πiξλ_j}|² dξ = Σ_{j,k} c_j c̄_k k_η(λ_j − λ_k)`.
   It is exactly diagonal when the `λ_j` are `2r`-separated. Prime frequencies `log n`, `n ≤ X`,
   are `1/X`-separated, so the diagonal regime is `X ≤ 1/(2r)`: prime length at most half the
   window length. This is the square-root threshold as an identity.
2. **SRT-4b variance of localized forms of `ζ`.** Write `W_ζ(S_ξ f) = A_f(ξ) − Π_f(ξ)`, with the
   archimedean-plus-pole part `A_f` and the prime polynomial `Π_f`. Then the windowed variance
   equals `‖η‖² Σ_n 2Λ(n)²/n |k_f(log n)|²` exactly below the threshold. Chebyshev then bounds
   the windowed proportion of heights with `W_ζ(S_ξ f) < 0` by `O((log X/log T)²)`.
3. **SRT-4c beyond the threshold.** Off-diagonal pairs `|log(n/m)| < 2r` are shifted sums.
   *Calibration:* Zeta23 (`formal/.lake/packages/Zeta23`) proves `> 2/3` of zeros on the line by
   localized explicit formulas at aperture `L = λ log(T/2π)` with `λ ≤ 1` (`Params.Valid.lam_le_one`).
   Its proportion `H(λ) = 2 − 1/λ − λ/3` would grow up to `λ = √3`. The obstruction is exactly
   the prime-side traces beyond `X = T`, that is, the off-diagonal of item 1.
4. **SRT-5b converse visibility for `ζ`.** A zero `½ + δ + iγ₀` that is deepest in its window
   should make some localized form at height `γ₀` negative once `sinh(2δa)/δ ≳ (1 + a) log γ₀`.
   *Difficulty:* a Gallagher/Plancherel–Pólya bound for the zero side with the local count
   `A₀ log(|t| + 3)` is needed. Off-line competitors contribute `2(c² − s²)` with even part `s` and
   odd part `c` of the tilted test, and only the `c²` parts are positive.

## Log
- 2026-10-19 — created; SRT-1 to SRT-3 and SRT-5a proved and wired into
  `GaloisForLFunctions.SquareRootThreshold`.
