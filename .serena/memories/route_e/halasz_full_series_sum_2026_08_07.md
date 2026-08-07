# The Halász discrete input, for the full series (2026-08-07)

`RHTower/Sieve/HalaszFullSeriesSum.lean` — green (9066 jobs), axiom-clean, in the umbrella.

Upgrades the corpus's proxy-only dichotomy (`HalaszDichotomy.norm_sum_smooth_le_exp_of_far`,
`HalaszUniqueClose.sum_norm_smoothMulSum_le_of_spacing`, both about `smoothMulSum` = the squarefree
smooth product) to the actual Dirichlet series:

- `norm_tsum_twistedSummand_le_trivial` : `‖F(s)‖ ≤ (1 + 1/(σ-1))·e^{7/2}`.
- `norm_tsum_twistedSummand_le_of_far` : distance ≥ δ ⇒ `‖F(s)‖ ≤ (1+1/(σ-1))·exp(7/2+shift-δ²)`.
- `sum_norm_tsum_twistedSummand_le_of_spacing` : for a frequency set with mesh above the corpus's
  window, `∑_{t∈S} ‖F(σ+it)‖ ≤ (1+1/(σ-1))·e^{7/2+shift}·(|S|·e^{-δ²} + 1)`; the uniqueness input is
  the corpus's `card_filter_close_le_one_of_spacing`.

`shift = 2(σ-1)(log z + log 4)` is `O(1)` at `σ = 1 + 1/log z`.

## Lean notes

- `(((σ:ℝ):ℂ) + ((t:ℝ):ℂ)*I).re = σ` and `.im = t` by `simp` — keep them as named lemmas
  (`re_ofReal_add_mul_I`, `im_ofReal_add_mul_I`) because they are needed to rewrite the abscissa inside
  every application.
- `Finset.sum_le_card_nsmul` + `nsmul_eq_mul` is the clean way to bound a filtered sum by
  card × pointwise bound.
- After `rw [hE, ← Real.exp_add]` a following `congr 1; ring` can fail with "no goals" — `congr 1` may
  already close it. Prefer rewriting the exponent with an explicit `ring`-proved `have` and then
  `Real.exp_add`.

Remaining on the path: the discrete-to-integral passage (Gallagher/Sobolev) and the Perron assembly
(`HTGeometry.SmoothWeightPerron`). See `mem:route_e/distance_abscissa_bridge_2026_08_07`.
