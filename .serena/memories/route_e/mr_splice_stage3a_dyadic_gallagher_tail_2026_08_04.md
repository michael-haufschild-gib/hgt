# MR splice stage 3a: dyadic Gallagher far tail formalized (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md`.

Built `RHTower/Sieve/GallagherDyadicTail.lean` (wired into `RHTower.lean`, targeted build 8798
jobs pass, axioms only propext/Classical.choice/Quot.sound, zero lint warnings):

- `dyadicAnnulus W k = {2^k W ≤ |w| < 2^{k+1} W}` with measurability, pairwise disjointness,
  `exists_dyadic_scale` (least-index argument via `Nat.find` on `pow_unbounded_of_one_lt`), and
  `iUnion_dyadicAnnulus : ⋃ k = {|w| ≥ W}`.
- `gallagher_split_integral_dyadic`: for ANY real α β (no sign hypotheses needed) with
  `∫_{Icc(-T,T)}‖logPoly a s‖² ≤ αT + β` for all T ≥ W:
  `∫_ℝ ‖logWindowSum‖² ≤ 2δ²(αW+β) + 4α/(π²W) + 4β/(3π²W²)`.
  Mechanism: `hasSum_integral_iUnion` over the annuli, per-annulus weight cap via the SHARP decay
  `fourier_triC_re_le_inv_sq : (𝓕 triC δ w).re ≤ 1/(π²w²)` (already in `GallagherTail.lean` —
  constant 1, found in-tree; do not redeclare, name collides), then two geometric tsums
  (`tsum_geometric_of_lt_one`, `Summable.tsum_le_tsum`).
- `gallagher_meanValue_dyadic_le`: instantiation with `integral_Icc_normSq_logPoly_le`
  (α = 2Σ₂, β = 4N(1+logN)Σ₂/π). Far tail carries Σ₂ = ∑‖a‖², never (∑‖a‖)².

Consequence: the Gallagher frequency budget for the MR splice is now W = N/L in Lean, not
(N/L)² — the false-wall removal certified in
`mem:route_e/mr_splice_stage1_prime_cube_and_corridor_2026_08_04` is formal.

Lean traps hit: (a) `fourier_triC_re_le_inv_sq` already declared in `GallagherTail.lean` with a
`w ≠ 0` hypothesis and constant 1 — always grep before declaring; (b) `push_neg` is deprecated
(warnings fail the gate) — use `rw [not_le]/[not_lt]`; (c) membership in a `setOf` conjunction
set: rewrite inside `hw.1`, not inside `hw`; (d) `field_simp` can close goals fully — a trailing
`ring` then errors "no goals".

Next: stage 3b (log-power fight) per the card.
