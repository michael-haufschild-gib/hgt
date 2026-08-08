# Card `raw-mobius-hermitian-positive-excursion-law` — CLOSED, stage 3 (2026-08-08)

Now `docs/drafts/pipeline/3-formalized/raw-mobius-hermitian-positive-excursion-law.md`.
Its open gate was "full analytic Lean formalization"; it is now checked.

## Already in the tree before this cycle (card prose was stale again)

* `(R3)` lower, twisted: `TwistedOrderLawTheta.two_mul_zeroAbscissa_sub_one_le_limsup`
* `(R3)` upper, any unit-bounded sequence:
  `EvenIndexHermitianOrderUpperBound.limsup_log_mixedAdditiveConvolutionPower_re_le`
* `(R4)` twisted: `TwistedMobiusPositiveExcursion.infinite_pos_twistedMixedAdditiveConvolutionPower`
* `(R4)` zeta: `MobiusEvenIndexPositiveRecurrence.frequently_re_pos_moebius` (even indices — strictly
  stronger than the card's claim)
* `(R7)`/`(R8)` radial law and `(R10)`/`(R11)` subpower→decay:
  `DirichletLMixedAdditiveZeroAbscissaLaw`, `MixedConvolutionSubpowerAbelBound`

## Added — `RHTower/RawMobiusHermitianExcursionLaw.lean`

* `zetaZeroAbscissa_le_of_rawMixed_subpower` — the zeta pole obstruction on the **raw** (all-index)
  Hermitian convolution: a global one-sided bound `Re R_k(N) ≤ C(N+1)^α` forces
  `Θ ≤ (α+1)/(2k)`.  Chain: `norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower` gives
  `moebiusProfile = O(x^{-b})`, then `not_isBigO_moebiusProfile_rpow` at a zeta zero right of `b`.
* `mobiusRawHermitianOrder`, `le_mobiusRawHermitianOrder`, `mobiusRawHermitianOrder_le`,
  **`rawOrder_moebius_bounds`** = `(R3)` for zeta; **`rawOrder_twisted_bounds`** = `(R3)` for twists.
* **`frequently_rpow_le_rawMixed_moebius`**, **`frequently_rpow_le_rawMixed_twisted`** = `(R5)`,
  stated with the card's `k ≥ 2` (`1 ≤ j`).
* **`frequently_one_le_moebiusBinaryCorrelation_raw`** = `(R6)`,
  `∑_{a+b=N} μ(a) μ(b) ≥ 1` infinitely often, from the even-index integral version.

## Why `k ≥ 2` is not a simplification

At `k = 1` with `Θ = 1/2` the lower edge `2kΘ − 1` is exactly `0`, so the exponent argument gives
nothing; the card itself proves the binary endpoint by the separate recurrence route.  That route is
`(R6)`, which is proved here.  Do not try to state `(R5)` at `k = 1` — the `nlinarith` will fail and
it is false as an exponent claim.

## Standing pattern for this family of cards

`le_limsup_of_no_subpower_below` (in `TwistedMobiusOrderLowerBound`) is the universal entry point:
supply a crude polynomial bound `Re R_k(M) ≤ (M+1)^D` and a "no global subpower below θ" theorem,
get `θ ≤ limsup`.  Ω₊ statements then come from negating the frequently-form, absorbing with
`HTGeometry.exists_global_subpower_of_eventually_le`, and hitting the same no-subpower theorem.
