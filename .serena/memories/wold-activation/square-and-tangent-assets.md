# Wold–shell Euler activation square — closure state and assets

Card `docs/drafts/pipeline/3-formalized/wold-shell-euler-activation-square.md` closed 2026-08-10.

## Where the card's equations live

- `(1)`–`(3)`, `(4)`, `(5)`: `RHTower/WoldEulerActivationSquare.lean`
  (`activationFactor`, `activationDepthFactor`, `activationSeries_eq_tprod`,
  `activationSeries_zero_activation`, `tendsto_activationSeries_depth`,
  `tendsto_activationSeries_activation`, `tendsto_zetaRatio_depth/activation`).
- `(6)`, `(10)`, `(11)`: `RHTower/WoldEulerActivationHolonomy.lean` (pre-existing).
- `(14)`–`(18)`: `RHTower/WoldShellTangentTransfer.lean`.
- `(20)`–`(23)`: `RHTower/WoldActivationDivisorBlowup.lean` — **already existed** when the card
  still claimed the blow-up was paper-level.  Audit the tree, not the card text.

## Reuse that saved the build

- The activation coefficient `a_h(n) = ∏_{p|n} (1 - p^{-h})` is **already** in the corpus as
  `RHTower.suzukiRadicalFactor α` (`SuzukiPacketCoefficientSeries.lean`) with `h = 2α`, together
  with `suzukiRadicalFactor_apply`, the convolution form, and the packet L-series
  `LSeries_suzukiShiftedCoefficient : L(c_α) s = ζ(s-α)/ζ(s+α)`.  `activationFactor h` is a
  one-line specialization; the infinite-depth face is that L-series after a shift.
- The depth condition `M(n) ≤ m` is `MFree (m+1)` from `MFreeLadder.lean`, whose
  `LSeries_mFree_eq_riemannZeta_div` gives the full-activation face for free.

## New reusable assets

- `tendsto_riemannZeta_of_re_atTop_filter` — zeta → 1 along an **arbitrary** filter escaping right;
  the corpus previously had only the ℕ-sequence form in `XiSourceNormalConeDivisorConservation`.
- `tendsto_ratio_of_normalized` / `tendsto_ratio_of_normalized_real` — if `b^{ms}/log b · f m → 1`
  then `f(m+1)/f m → b^{-s}`.  Both `(17)` and its residual form are instances.
- `summable_logPrime_rpow` — `∑_p (log p) p^{-σ} < ∞` for `σ > 1`, extracted by restricting the
  mathlib von Mangoldt L-series to the prime subtype (`LSeriesSummable_vonMangoldt` + `.subtype`).
- `tendsto_normalizedPrimeTail`, `normalizedShellTangent_sub_atoms` — the dominated tail estimate
  and finite-atom stripping shared by `(15)` and `(16)`.

## Traps

1. `push_cast` rewrites `((Real.log x : ℝ) : ℂ)` to `Complex.log x` (`Complex.ofReal_log`), which
   destroys pattern matching against corpus lemmas stated with `↑(Real.log …)`.  Normalize only the
   numerals: `rw [show ((2:ℕ):ℂ) = (2:ℂ) from by norm_num, show Real.log ((2:ℕ):ℝ) = Real.log 2 …]`.
2. `gcongr` on `x ^ a ≤ x ^ b` picks the base-≥-1 branch; for a base ≤ 1 use
   `Real.rpow_le_rpow_of_exponent_ge` under `mul_le_mul_of_nonneg_left` by hand.
3. Two more umbrella-only name collisions surfaced (`ofReal_div_cpow` in `BurnolSoninDividedShift`,
   `tendsto_descFactorial_div_pow` in `HTGeometry/EndpointChirpGlue`).  Grep every new top-level
   name against the area *before* `lake build <umbrella>`; `lake env lean` never sees them.
   When the existing lemma sits behind a heavy import chain (Sonin layer), rename the new one with
   a specific name instead of importing.
