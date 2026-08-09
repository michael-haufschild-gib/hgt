# The `q = 4` Gram entry, and a better single-generator bound

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The prediction, now proved

`digamma-difference-series.md` predicted `bdGram (1/4) (1/4) = (3 log 2)/8 − π/32` from the three progression
constants, and named the missing step: the residue-class decomposition of `ℕ` as a `HasSum`. That step is done.

`RHTower/QuarterGramEntry.lean`:

* `hasSum_quarter_recip_real` — the progression sums transferred from `ℂ` to `ℝ` (`Complex.hasSum_ofReal`);
* `hasSum_indicator_quarter` — the indicator of a residue class summed over `ℕ`, by reindexing along
  `k ↦ 4k + (j−1)` with `Function.Injective.hasSum_iff` (the indicator vanishes off the image, which is what
  the lemma needs);
* **`bdGram_quarter` — `bdGram (1/4) (1/4) = (3 log 2)/8 − π/32`.**  The Gram series of
  `hasSum_bdGram_discrete` splits by `(n mod 4)² = (n mod 4) + 2·[n≡2] + 6·[n≡3]` into the pairing series
  (value `log 4`) and the two indicator series (values `T₂`, `T₃`), and `HasSum.unique` identifies the total.
* **`bdDist_sq_le_quarter_bound` — `d² ≤ 1 − (log 2)²/(4·((3 log 2)/8 − π/32))`** for the family `{1/4}`,
  via the quadratic form at the optimal coefficient `c = log 2/(2·gram)`.

## What it says

The `m = 4` generator is a strictly better single approximant than `m = 2`: the earlier bound was
`d² ≤ 1 − log 2`, and this one is smaller (both are exact symbolic expressions in `log 2` and `π`; the
comparison is `(log 2)²/(4g) > log 2` with `g = (3log 2)/8 − π/32`, since `4g < log 2`).

More importantly the *method* is now complete and reusable: pick a modulus, decompose `r²` over residue
classes, feed the digamma values in, and the quadratic form returns a bound. Nothing in the chain is
unevaluated any more for denominators `2` and `4`.

## What it does not say

This is still a single generator, and one generator cannot approach `0`. Getting `d_N → 0` needs the *joint*
behaviour of many moduli — i.e. the estimate that remains open (`baez-duarte-layer-map.md`). Denominator `3`
still needs Gauss's general digamma theorem, a mathlib TODO, so `m = 3, 6, 12, …` are not reachable this way.

## Addendum (same day): the full `{2,4}` Gram matrix

`RHTower/HalfQuarterGram.lean`. The same decomposition gives the off-diagonal entry, from
`(n mod 2)(n mod 4) = [n≡1 mod 4] + 3·[n≡3 mod 4]` (check the four residues: `0·0, 1·1, 0·2, 1·3`):

**`bdGram_half_quarter` — `bdGram (1/2) (1/4) = (5 log 2)/16 − π/32`.**

So the Gram matrix of the two-generator system is entirely explicit:

| | `1/2` | `1/4` |
|---|---|---|
| `1/2` | `(log 2)/4` | `(5log 2)/16 − π/32` |
| `1/4` | `(5log 2)/16 − π/32` | `(3log 2)/8 − π/32` |

with pairing vector `((log 2)/2, (log 2)/2)` — the two entries coincide because `−θ log θ = (log m)/m` takes the
same value at `m = 2` and `m = 4`. `bdGram_half_quarter_det_pos` shows the determinant is positive (from
mathlib's certified bounds on `log 2` and `π`), so the matrix is invertible and the optimal coefficient pair
`G⁻¹v` exists; feeding any pair into `bdDist_sq_le_quadratic` gives a closed-form bound.

I did not evaluate the optimal two-generator bound symbolically. The expression is `1 − vᵗG⁻¹v` in `log 2` and
`π`, and while it is smaller than the single-generator value, writing it out adds arithmetic without adding
information — the Gram matrix and the quadratic form are the reusable objects, and both are now closed.
