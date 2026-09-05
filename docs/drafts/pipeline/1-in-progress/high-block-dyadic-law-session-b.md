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
- 2026-09-05 — B8 direct tail: `HighBlockDirectTail` (free-exponent tail `K x^A L^{1-(1/2-d+A)}/((1/2-d+A)-1)` for every `A > 1`, uniform in `d ∈ [0, 1/4]`, `τ`, `x`).
- 2026-09-05 — B8 dual decay: `HighBlockDualWeightRightShift` — right contour shift of the displaced dual weight to `Re w = 1/2 - d + K`; `exists_norm_smoothAFEZetaDisplacedDualWeight_le_rightShift`: for every `K ≥ 1` one constant gives `‖W_{d,τ}(Y)‖ ≤ C (1+|τ|)^{K+1/2} ‖χ(s)^{-1}‖ Y^{-(1/2-d+K)}` for all `0 < d ≤ 1/4`, `τ`, `Y > 0`. Ingredients: analyticity on `Re w > 1/2`, rectangle Cauchy, Titchmarsh sharp line bound on `Re = -K` extended to all heights, polynomial strip growth against the Gaussian on the horizontal edges. Next: dual tail beyond `L` (term-wise `|χ(s)||χ(s)^{-1}| = 1`, tail `≍ (1+|τ|)^{K+1/2} x^{-(1/2-d+K)} L^{-K}/K`).
- 2026-09-05 — B8 dual tail: `HighBlockDualTail` (`exists_norm_highBlockDual_tail_le`: tail `≤ C(1+|τ|)^{K+1/2} x^{-(1/2-d+K)} L^{-K}/K`, uniform). B1: `HighBlockTruncatedAFE` — `riemannZeta_displaced_eq_truncated` (`ζ = D_L + Dual_L − Pole + Tail_L`, exact) and `exists_norm_highBlockAFETail_le` (uniform two-term tail bound, free exponents `A > 1`, `K ≥ 1`). Next: B3 split and B4 direct energy.
- 2026-09-05 — B4: `HighBlockDirectMeanSquare` — `edPoly_Icc_eq_dirPoly` (the gate mollifier `Ψ` on the displaced line as a `dirPoly` at frequency `−τ`), `highBlockDirectHead_mul_edPoly_eq_dirPoly` (`D_L·Ψ` = one `dirPoly` of length `LN`, coefficients `dirConv`), `highBlockDirectEnergy`, and `abs_integral_normSq_highBlockDirect_sub_le`: `|∫_{T₁}^{T₂}‖D_LΨ‖² − (T₂−T₁)E| ≤ 8LN(1+log LN)E`. Next: B5 (dual×dual with frozen weight: conjugate the `+τ` head so `|χ|²·|dirPoly|²`, then weight transfer), B6 cross, B7 pole, B3/B9 assembly.
- 2026-09-05 — `HighBlockChiModulus`: sharp modulus of `χ` on the moving displaced line, `‖χ(1/2−d+iτ)‖ = (τ/2π)^d e^{e}` with `|e| ≤ d(π/τ + 5/τ²)` uniformly for `0 ≤ d ≤ 1/4` (`abs_log_norm_zetaChi_displacedLinePt_sub_le`, `exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp`, squared form with `chiModulusWeight (2d)`). This is the exact `e^{2R}` weight of the dual×dual term. Convention decision for the assembly: the mollifier is `Sieve.levinsonLinearMollifier M` (critical-line coefficients `w_m/(√m log M)`), i.e. gate coefficients `b_m = (w_m/log M) m^{−d}`, so that the direct energy is exactly the lane object `smoothAFEZetaDisplacedDirectMollifiedCoeff 0 d x L M`.
- 2026-09-05 — B5: `HighBlockDualMeanSquare` — frozen reflected head `H_T` (`highBlockDualHeadFrozen`, weight frozen at `T`), its conjugate `dirPoly` form (`norm_highBlockDualHeadFrozen_eq`), `highBlockDualEnergy`, and `integral_normSq_chi_mul_highBlockDualFrozen_le`: `∫_{T₁}^{T₂}‖χ H_T Ψ‖² ≤ e^{2d(π/T₁+5/T₁²)}[E_dual ∫(τ/2π)^{2d} + 16LN(1+log LN)E_dual (T₂/2π)^{2d}]` for any Fin-indexed mollifier `Ψ = dirPoly N a (−τ)`. Next: B6 cross (Abel summation with the slowly varying weight `conj χ(s) e^{−2iθ}` against the corpus first-derivative test), freezing error, B7 pole, B3/B9 assembly.

## Structural finding (2026-09-05, session B): the cross term is not covered by the corpus cross lemma

The cross term of `|D_LΨ + χ H_T Ψ|²` is `2Re ∫ conj(χ(s)) · (D_LΨ)(τ) · conj(H_T(τ)) · conj(Ψ(τ)) dτ`.
Its frequencies: `D_L` and `Ψ` carry `r^{−iτ}`, `conj(H_T)` carries `n^{−iτ}` (the reflected head has `n^{+iτ}`),
`conj(Ψ)` carries `m₂^{+iτ}`. So the only way to match `norm_integral_archimedeanCross_le` (one `−τ` polynomial
with indices `≤ x` times `conj` of one `−τ` polynomial, gap `2π x K ≤ a`) is `x = L²N` (direct × mollifier × conjugated
dual head), and then `2π x K ≤ a` forces `K ≤ a/(2π L² N) ≈ a^{−2δ}/N < 1`: the hypothesis `0 < log K − …` fails.
Correspondingly the phase derivative `log(τ m₂ /(2π r n m₁))` vanishes at `r n = (τ/2π)(m₂/m₁)`, which is inside the
ranges `r ≤ L`, `n ≤ L` (the corner `r ≈ n ≈ √(τ/2π)` for `m₁ = m₂`), for every split `xy = τ/2π`.
So the cross term has interior stationary points and is `Θ(a)` on a block: it is part of the constant `c`
(the `−1` of `2γ − 1` in the unmollified case), exactly as brick 5af said. Brick 5ba item 4 ("no stationary point,
first-derivative test suffices") treats the dual head as a `−τ` polynomial, which it is not; it is `conj` of one.

**Consequences.**
* The sharp `c(P,θ,R)` needs either the corner stationary-phase evaluation (bricks 5ar–5av) or a product AFE for
  `ζ(s)ζ(s̄)` (Young route; the corpus `SmoothAFEZetaSquare*` modules are for `ζ(½+iτ)²`, not the product).
* An explicit non-sharp constant needs only upper bounds: `|D + χH|² ≤ (1+η)|D|² + (1+1/η)|χH|²`, so
  `c = (√c_dir + e^{R}√c_dual)²`, and the arithmetic input reduces to upper bounds on the mollified energies.
* Session B route: reduce every smooth displaced energy (direct `V`, frozen dual `W_T`, freezing derivative `∂_uW_u`)
  to the sharp-cutoff Barban–Vehov energy by Abel summation in the head variable plus Cauchy–Schwarz:
  `Σ_r r^{−1}|Σ_{m|r} λ_m g(r/m)|² ≤ ‖Δg‖₁² · sup_u Σ_r r^{−1}|Σ_{m|r, r/m ≤ u} λ_m|²` (no arithmetic in the transfer),
  then one classical input: the sharp-cutoff energy is `O(1)` uniformly in the head length `u ≤ L`.
- 2026-09-05 — `HighBlockCutoffMonotone`: the Gaussian cutoff `V` has `V′(x) = −e^{−(log x)²/4}/(2√π x)` (`hasDerivAt_smoothAFECutoff`, differentiation under the integral + `integral_cexp_quadratic`), is real on `(0,∞)` (`smoothAFECutoff_im_eq_zero`), antitone (`smoothAFECutoff_re_antitoneOn`) with `0 ≤ Re V ≤ 1`. Inputs for the total-variation bound of the smooth head weights.
- 2026-09-05 — `HighBlockSmoothToSharpEnergy`: `energy_smooth_le_sharp` — for any head weight `g`, base head `h`, mollifier `b`: `Σ_r‖((g·h) ∗ b)(r)‖² ≤ (Σ_{u<L}|Δg(u)|)² · sup_{u<L} Σ_r‖((h·1_{≤u}) ∗ b)(r)‖²` (telescoping `smooth_head_eq_sum_sharp`, linearity `dirConv_sum_left`, weighted Cauchy–Schwarz `norm_sum_mul_sq_le`). No arithmetic. Every smooth displaced energy now consumes one input: the sharp-cutoff critical energy, uniformly in the head length.
- 2026-09-05 — `HighBlockDirectVariation`: `sum_norm_headDiff_prod_le` (TV of increasing × decreasing-in-[0,1] ≤ 3·a(L)), `smoothAFEZetaDisplacedDirectDetectorCoeff_zero_eq` (`= [(n+1)^d Re V((n+1)/x)]·(n+1)^{−1/2}`), and `sum_normSq_dirConv_direct_le_sharp`: direct mollified energy `≤ (3(L+1)^d)² · sup_{u<L} (sharp critical energy at head length u)` for any mollifier. The direct×direct term now depends only on the sharp-cutoff critical energies.
- 2026-09-05 — `HighBlockDualWeightVariation`: `norm_cpow_neg_sub_cpow_neg_le` (variation of `Y^{−w}` by FTC), left-contour telescoping (`exists_sum_norm_dualWeight_sub_le_left`, `≲ 1/η`), right-contour telescoping (`exists_sum_norm_dualWeight_sub_le_right`), `norm_inv_zetaChi_displacedLinePt_le`, `exists_norm_smoothAFEZetaDisplacedDualWeight_le_uniform` (sup bound), and `exists_sum_norm_dualWeight_diff_le`: `Σ_{n<L}‖W_{d,T}((n+1)x) − W_{d,T}((n+2)x)‖ ≤ C` uniformly in `0<d≤1/4`, `T≥1`, `0<x≤T`, `L`. The `1/w` of the kernel cancels the `‖w‖` of the power derivative: no log loss.
- 2026-09-05 — `HighBlockDualVariation`: `conj_highBlockDualCoeffFrozen_eq` (`= [(n+1)^{−d} conj W_{d,T}((n+1)x)]·(n+1)^{−1/2}`), `sum_norm_headDiff_prod_bv_le` (TV of decreasing-in-[0,1] × bounded-BV ≤ 2 sup + TV), `exists_highBlockDualEnergy_le_sharp`: frozen dual energy `≤ Cv² · sup_{u<L}(sharp critical energy)` uniformly in `0<d≤1/4`, `T≥1`, `0<x≤T`. Both mollified energies of the split now consume the single sharp-energy input.
- 2026-09-05 — `HighBlockFreezing`: moving dual head `highBlockDualHead` (`Σ highBlockDualTerm = χ·head`), mean-value freezing bound `exists_norm_highBlockDualHead_sub_frozen_le` (`‖H_τ − H_T‖ ≤ A(τ−T)T^{−(d+5/4)}x^{d+1/4}Σ_{n<L}(n+1)^{−1/4}`, from the corpus height-derivative bound at `η = 1/4`), `sum_rpow_neg_quarter_le` (`≤ 1 + (4/3)L^{3/4}`), and the pole bound `norm_smoothAFEZetaShiftedPoleResidue_displaced_le` (`≤ x^{1/2+d} e·e^{−τ²}/τ`). Remaining: continuity of the pieces, the sub-block estimate, and the assembly to `ZetaDyadicMeanSquareLaw` from the single sharp-energy input.
- 2026-09-05 — `HighBlockSubBlock`: continuity of every piece along the displaced line, Young/AM-GM square inequalities, and `integral_normSq_zeta_mul_edPoly_subBlock_le`: on `[T,T′]`, `∫‖ζΨ‖² ≤ (1+η)[2(hE_dir + MV_dir) + 2e^{ε_T}(E_dual∫w + MV_dual·2w(T′))] + (1+1/η)·3h·N²(W_sup E_freeze² + E_pole² + E_tail²)` with abstract constants. Remaining: the assembly (parameters `x=√(a/2π)`, `L=⌈a^{1/2+δ}⌉`, `N=⌊U^θ⌋`, `J=⌈a^{1/4+δ}U^θ⌉` sub-blocks, crude bound for `a ≤ U^{θ′}`) to `ZetaDyadicMeanSquareLaw`.
