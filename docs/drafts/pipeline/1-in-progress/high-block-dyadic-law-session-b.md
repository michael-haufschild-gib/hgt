# The high-block dyadic mean-square law (session B working card)

**Goal.** Discharge the last input of the single-input `(L)` constant and the Levinson gate:
`ZetaDyadicMeanSquareLaw R c` and `DyadicDetectorMeanSquareLaw R c` (F681/F682) on high blocks —
for `a ≥ T₀(ε)`, `[a, v] ⊆ [a, 2a]`, `σ₀ = ½ − d`, `d = R/log T`, `T ∈ [U−1, U]`, `M = U^θ`
(`θ < ¼` so that `8M² ≤ √a` holds on every block), `λ ∈ {0, 1/log U}`:

    ∫_a^v ‖G_λ(σ₀+it) Ψ(σ₀+it)‖² dt ≤ (c + ε)(v − a) + ε (a + U/log U).

Low blocks are covered by the slack (`DyadicLawLowBlocks`). `λ = 0` first (value AFE only), then
the detector with the differentiated AFE.

**Regime (fixed by session B).** Symmetric Gaussian split, `x = √(a/2π)` frozen on the block; the
exact AFE is kept as two infinite series (`riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight`)
and truncated at `L = ⌈K x⌉` using the cutoff's super-polynomial decay
(`exists_norm_smoothAFECutoff_le_neg_rpow`); the dual weight is frozen at the block's base height
(`SmoothAFEZetaDualSeriesFreezing`). No use of the lane's finite-approximation constants with the
`(1+τ)^N L^{−7/2}` and `x^{d+η}τ^{−η}L^{½+η}` terms — those are not small in this regime.

**Block plan.**
* B1 exact AFE on the block, `ζ = D_x − χ·Dual_x − Pole_x` at `s = ½ − d + it`;
* B2 (λ ≠ 0 only) the differentiated identity, `SmoothAFEZetaDisplacedFullDerivativeIdentity`;
* B3 split `∫‖ζΨ‖² ≤ (1+η)[∫‖DΨ‖² + ∫‖χ·Dual·Ψ‖² + 2|cross|] + (1+1/η)∫‖(Pole + tails)Ψ‖²`
  (`MeanSquareSplit`);
* B4 direct energy: MV theorem (`dirichlet_meanValue_theorem`) + the smooth displaced
  Barban–Vehov energy `Σ_r |Σ_{nm=r} n^{−½+d} V(n/x) b_m m^{−½}|²`, evaluated by expanding
  `n^{2d} = e^{2R log n/log T}` in powers of the normalized log and `V` through its Mellin
  representation, against the corpus's log-monomial Selberg laws
  (`tendsto_selbergOriginalLogMonomial_div_log_pow`, all pairs);
* B5 dual energy: twisted mean value (`MollifiedTwistedMeanValueIcc`) with the frozen dual weight,
  the `χ`-modulus weight `(t/2π)^{2d}` via `abs_integral_weighted_meanSquare_sub_le`;
* B6 cross: `norm_integral_archimedeanCross_le` (frozen dual) plus the freezing difference;
* B7 pole: `integral_smoothAFEZetaDisplacedMollifiedPoleRemainder_normSq_le`;
* B8 tails of both series beyond `L`: pointwise from the cutoff decay, `‖Ψ‖ ≤ N`;
* B9 identify `E_dir + E_dual = c(P, Q, R, θ)` (Young) up to `ε`.

**Coordination.** Session A (the `SmoothAFEZeta*`/`Sieve` lane) is active on the arithmetic layer.
Session B writes only new modules named `HighBlock*`, never edits lane modules; every brick is logged
here and mirrored on `levinson-critical-proportion-programme.md`.

## Log
- 2026-09-05 — card opened after F681/F682 (gate from the dyadic law, low blocks). Next: B8 (tails)
  and B1 in the displaced tsum form, then B4.
