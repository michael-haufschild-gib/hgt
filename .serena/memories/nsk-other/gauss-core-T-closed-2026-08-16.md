# Gauss card: (T) proved, and proved for the whole piecewise-exponential symbol algebra

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/gauss-component-quasi-inner-residue-hierarchy.md`
(passes 43, 44, 45 at the end of the card record everything below).

## In the tree (all unconditional, axiom-clean, umbrella-wired)

- `HTGeometry/LatticeTailSums.lean`, `HTGeometry/PowerSeriesTailBound.lean` — elementary ℤ-lattice
  weights in `ℝ≥0∞`, and `tsum_int_tail_rpow_le : Σ_(|j|>J)(1+|j|)^(-s) ≤ 2(1+J)^(1-s)/(s-1)`.
- `RHTower/GaussShiftRatioWeight.lean`, `GaussSpikeBandSum.lean`, `GaussDefectHighModeTail.lean` —
  the ratio-weighted Parseval identity and the two regime bounds; spike mass `≤ (2+4K^(1/2))·n`;
  high-mode tail `≤ 16A²(1+K)/(1+J) + 16KA²(1+log n)/n`.
- `RHTower/GaussLowModeKernelBound.lean` — `spike_lowBand_separation`,
  **`norm_fourierCoeff_symbol_truncate_le`** (general symbol) and its reciprocal-square
  specialization `norm_fourierCoeff_invSq_truncate_le`, `norm_gaussSampleRatioDefect_le_of_lowBand`,
  `sum_norm_fourierCoeff_lowBand_le`.
- `RHTower/GaussConvolutionCoefficient.lean` — **`norm_fourierCoeff_lpBoundedMulCLM_le`**: for any
  measurable real symbol of modulus `≤ Cb` with `|ĉ(x)| ≤ A/(1+|x|)`, the multiplied vector's
  coefficients are dominated by the harmonic convolution with constant `A`.
- `RHTower/GaussSpikeDefectVanishing.lean` — `norm_sq_shiftedDiag_symbol_highMode_le`,
  `norm_sq_shiftedDiag_symbol_lowMode_le` (spike bound `eps = 24·A_k·A·(5+3K)·(1+log I)/I`), and
  the three capstones
  `tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero`     (general symbol),
  `tendsto_norm_gaussShiftedBlockDiag_invSq_defect_zero`      (B^(-2)),
  `tendsto_norm_gaussShiftedBlockDiag_expPiecewise_defect_zero` (every `IsExpPiecewise` symbol of
  modulus ≤ 1, via `norm_fourierCoeff_of_isExpPiecewise`, `A_k = n·M·2·exp|alpha|`).

## Key simplifications that made (T) work

Carry the exponent `1/2`, not `1/m`: for `m ≥ 2`, `rho^4 ≤ rho^(2m) ≤ Kn/|n+l|`.  Split at the
operator level so the two regimes never recombine inside one sum.  `‖defect‖ ≤ 1 + ‖defect‖²`
avoids square roots on the low band.

## What remains — the `m`-fold telescope, and why it is not mechanical

`R̃_n = B ∘ S̃ ∘ B^(-2) ∘ S̃* ∘ B`.  `B`, `B^(-2)` are symbol multiplications = harmonic convolutions
(cost one logarithm, absorbable by `log_div_le_rpow_div`).  But `S̃`, `S̃*` are FOURIER MULTIPLIERS
with symbol `rho_j ≍ (n/|n+j|)^(1/(2m))`, which is `O(1)` in the bulk and `(Kn)^(1/(2m))` at
`j ≈ -n`.  So a uniform class `A/(1+|j|)^theta` is NOT invariant: the damage sits at a moving
frequency, and no drop of `theta` repairs it.  The invariant class must be two-piece:

    |ĝ(j)| ≤ A/(1+|j|)^theta  +  Bc·[2|n+j| < n]·(n/(1+|n+j|))^c .

Design notes checked by hand: the spike part sits at distance ≍ n from frequency 0, only the
0-th coefficient is read at the end, and a harmonic convolution moves spike mass to frequency 0
with gain `1/(1+n)` — for `c < 1` the spike mass is `≍ n`, so the transfer is `O(1)`, i.e. the
uniform constant stays BOUNDED rather than decaying.  That is enough for the telescope
`‖X^r v - Y^r v‖ ≤ Σ_i ‖Y‖^(r-1-i)‖(X-Y)(X^i v)‖`, which only needs the class to be invariant with
bounded constants.  Exponent constraint from pass 44's analysis: the high-mode term needs
`theta > 3/4` (not `1/2`).

Already available for the one-step law on the constant vector:
`RHTower/GaussRelativeOneStep.lean` — `tendsto_norm_gaussPrincipalStep_one_sub_amplitude`
(three-vector split; `m ≥ 2`).  The general-vector version replaces `fourierLp 2 0` by `f` and
`b = B·1` by `B f`, and needs `B f` to stay in the class.
