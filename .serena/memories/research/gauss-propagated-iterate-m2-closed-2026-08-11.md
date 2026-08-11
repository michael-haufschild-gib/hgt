# Gauss quasi-inner propagated-iterate wall: depth one closed (2026-08-11)

Card: `docs/drafts/pipeline/1-in-progress/gauss-propagated-iterate-log-mean.md`.

The frontier map's "remaining local theorem" of the Connes–Consani quasi-inner lane
("stage-by-stage control of the propagated iterates R_n^i f inside the telescope, followed by
the logarithmic mean") is closed at its first depth, unconditionally, umbrella-wired:

New modules (all build; axioms = propext, Classical.choice, Quot.sound):
- `HTGeometry/HarmonicPowerConvolution.lean` — `tsum_harmonicPowConv_le`: lattice convolution
  `Σ_l (1+|l|)^{-β}(1+|j−l|)^{-1} ≤ 2^γ(1+|j|)^{-γ}·(2·Σ intPowWeight (β+1−γ))` for
  `0 < γ < β ≤ 1`. Log-free; two-region γ-exchange + weighted AM–GM + translation invariance.
- `RHTower/GaussConvolutionCoefficient.lean` — Parseval convolution law for a bounded real
  symbol (`hasSum_fourierCoeff_lpBoundedMulCLM`) + kernel decay `‖q̂(x)‖ ≤ 2/(1+|x|)`.
- `RHTower/GaussDoubleDefect.lean` — the double-defect estimate for every m ≥ 2
  (`tendsto_norm_gaussDoubleDefectVector_comp`): master lattice bound, evenness, product cap
  `ρ_j²ρ_l² ≤ 24 + 6K·I/v_j + 6K·I/v_l` (via `r⁴ ≤ 1 + r^{2m}` — the exact entry point of
  m ≥ 2), far-band dominated convergence at exponent 3/2.
- `RHTower/GaussRelativeOneStep.lean` — `R` and `M` self-adjoint; relative one-step law
  `‖R_i·1 − a_δ‖ → 0` for every m ≥ 2 (`tendsto_norm_gaussPrincipalStep_one_sub_amplitude`),
  by the exact three-term split Δw' + Δ(B⁻²Δ*b) + T₋δ(B⁻²Δ*b).
- `RHTower/GaussSquareDiagonalLogResidue.lean` — m = 2 capstones: fold `⟨1,R²1⟩ = ‖R·1‖²`,
  relative diagonal `o(1/n)`, `tendsto_gaussSquareFourierDiagonal_logResidue`
  (limit 2(p²−1)²/(4 log p)), `tendsto_gaussSquareLocalDiagonal_logResidue`
  (limit `gaussChannelResidue 2 p`). Formula (A) for the operator at m = 2.

Frontier map updated in 4 places. Open continuation (on the card): m ≥ 3 needs depth-⌈m/2⌉
iterate control = k-fold defect chains (k ≤ m+1) by the same band-split architecture; then
multi-place assembly, identification with the CC intersection/Weil object, and the positivity law.

Key method facts: the proved `tendsto_gaussIterate` is absolute o(1) and useless for the log
mean (main term ≍ 1/n); `‖R−M‖ ≍ n^{1/(2m)}` kills operator-norm propagation; everything must be
rate-free and fold through self-adjointness. Lean traps hit: un-ascribed lambdas in named
`refine` arguments loop the whnf unifier (ascribe binders); `rw [← ofReal_toReal-eq]` rewrites
inside itself.