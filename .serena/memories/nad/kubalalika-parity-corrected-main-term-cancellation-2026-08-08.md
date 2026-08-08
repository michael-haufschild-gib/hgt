# Card `kubalalika-parity-corrected-main-term-cancellation` — **STAGE 3, COMPLETE** (2026-08-08)

Card moved to `docs/drafts/pipeline/3-formalized/kubalalika-parity-corrected-main-term-cancellation.md`.
Route kill against a claimed RH disproof.  **Sections 1, 2, 3, 4 all formalized unconditionally**,
axioms `[propext, Classical.choice, Quot.sound]`.  Only gate left open is the novelty/priority
audit, which is not a Lean obligation.

## The stale claim that blocked this card for two weeks

The 2026-07-24 log deferred Sections 1–3 as "tied to the preprint's contour machinery not in the
corpus".  **Both halves were false.**  PNT is corpus-owned
(`RHTower.Sieve.tendsto_sum_vonMangoldt_div`), and Section 3 needs *no* contour input: equation (4)
is the *definition* of `A_Y` handed over by Sections 1–2, so (5) is a statement about the dilated
von Mangoldt square wave alone.  Read what a card's equations actually depend on before costing it.

## The theorem (Section 3, equation (5))

`RHTower.tendsto_dilated_vonMangoldt_sign_sum {α} (0 < α) (α ≤ π)`:

```
(1/T) ∑_{0 < m ≤ T} Λ(m) · sgn(sin(α T / m))  →  1 − 2 α log 2 / π
```

Companions in `RHTower/DilatedVonMangoldtSignLimit.lean`:
`..._integral` (same limit as `J(α) = α ∫_α^∞ sgn(sin x)/x² dx`, via `integral_sign_sin_mul_inv_sq_Ici`),
`..._one`, `..._two`, `..._difference` (the two dilations differ by exactly `(2/π) log 2` — the
coefficient that cancels the small-`n` Landau–Gonek term), `..._odd` and
`sum_Ioc_not_odd_vonMangoldt_le_log`.

## The four-step route (reusable for any dilated arithmetic square wave)

1. **Blocks.** `sgn(sin x) = (−1)^k` on `(kπ,(k+1)π)`; endpoints `blockEndpoint α T k =
   ⌊α T/(kπ)⌋` (`= ⌊T⌋` at `k=0`).  `abs_sum_blocks_vonMangoldt_sign_sub_le`: the sum differs from
   the alternating `ψ`-telescope by `≤ K log⌊T⌋`.  The per-block lemma must take **pointwise**
   interval hypotheses, not endpoint ones — endpoint form is vacuously wrong at `k = 0`.
2. **Endpoints.** `blockEndpoint α T k = ⌊blockScale α k · T⌋` with
   `blockScale α k = min 1 (α/(kπ)) = α / max α (kπ)`; PNT gives `ψ/T → blockScale`
   (`tendsto_head_blocks`).
3. **Series.** The telescope of proportions is `∑_{k≥1} (−1)^k (1/k − 1/(k+1)) = 1 − 2 log 2`,
   built as `HTGeometry.hasSum_signedHarmonicPair`.
4. **Tails.** Chebyshev `ψ(x) ≤ Cx` and the series tail are both `O(1/K)`.  `T → ∞` first, then
   `K → ∞`, as a four-way `ε/4` split.

## New reusable corpus assets

* `HTGeometry/SignedHarmonicPair.lean` — the **ungrouped** alternating gap series
  `∑_{k≥1}(−1)^k/(k(k+1)) = 1 − 2 log 2`.  Absolutely convergent, so a genuine `HasSum`.  Value
  obtained by pairing into the pre-existing `alternatingHarmonicPair` (`log 2`) and its complement
  `evenGapPair` (`1 − log 2`), whose sum is the telescoping `oddGapPair` (`1`); absolute
  convergence transfers the even-index subsequence limit back to the full series.
* `HTGeometry/SignSinBlock.lean`, `HTGeometry/AntitoneBlockTelescope.lean`,
  `RHTower/ChebyshevPsiScaling.lean`, `RHTower/VonMangoldtSignBlock.lean` (earlier instalments).

## Lean traps hit

* `field_simp` on `αT/x = αT/y` over-cancels to `↑y = ↑x`; the rebuilt goal is nonlinear and
  `linarith` fails.  Use `div_eq_div_iff` + `mul_left_cancel₀`.
* `Real.sign_of_pos`/`_of_neg` also rewrite `(−1)^k` on the RHS.
* `Metric.ball_mem_nhds` + `Tendsto.eventually` yields `dist _ _ < ε` directly — do **not** try to
  `rw [Metric.mem_ball]` first.
* `abs_add` is gone; use `abs_add_le`.
* `Finset.card_le_card_of_injOn` states membership on the **Set coercion** — `rw [Finset.mem_coe]`
  before `Finset.mem_filter`, and `simp only []` to beta-reduce the injectivity hypothesis.
* `Nat.pow_le_iff_le_log` does not exist; it is `Nat.le_log_iff_pow_le`.
* `tendsto_finset_sum` is deprecated → `tendsto_finsetSum`.
* `summable_of_sum_range_le` cannot infer its bound `c`; pass `(c := …)`.
* Umbrella insertion: `HTGeometry.lean` is **not** globally sorted — it has small locally-sorted
  islands.  Insert next to an alphabetically adjacent sibling, not at the first order violation.
