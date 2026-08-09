# Digamma differences as reciprocal-difference series

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## Correction to an earlier claim

`baez-duarte-layer-map.md` and `discrete-baez-duarte-gram-evaluated.md` said closed forms beyond `m = 2` need
"digamma at rationals, which mathlib lacks". That was imprecise and is corrected here.

* mathlib **has** digamma: `Analysis/SpecialFunctions/Gamma/Digamma.lean` defines `Complex.digamma = logDeriv
  Gamma` with `digamma_one = −γ`, `digamma_one_half = −2log 2 − γ`, and the recurrence `digamma_apply_add_one`.
* the corpus **has** Gauss's series: `HTGeometry/DigammaGaussSeries.digamma_eq_neg_euler_add_tsum_gauss`,
  `ψ(s) = −γ + ∑ₙ (1/(n+1) − 1/(s+n))` on `Re s > 0`.
* the corpus **has** the quarter value: `RHTower/DigammaQuarter.digamma_quarter`,
  `ψ(1/4) = −γ − π/2 − 3log 2`, from Legendre duplication and reflection.

What was genuinely missing was the *difference* form, which is what every evaluation actually consumes.

## What is proved

`RHTower/DigammaDifferenceSeries.lean`, subtracting two Gauss series so that both `γ` and the harmonic terms
cancel:

* **`digamma_sub_eq_tsum` — `ψ(b) − ψ(a) = ∑ₙ (1/(a+n) − 1/(b+n))` for `Re a, Re b > 0`;**
* `hasSum_digamma_sub` — the same as a `HasSum`, which is the form series manipulations need.

A connector, not new analysis: the content is in the Gauss series it rests on.

## Why it matters here

Sums of reciprocals over an arithmetic progression are exactly digamma differences. Concretely, for the
Báez-Duarte Gram entries, `T_j = ∑_{n ≡ j mod q} 1/(n(n+1)) = (1/q)·(ψ((j+1)/q) − ψ(j/q))`, so with the values
above the `q = 4` entries are reachable:

`T₁ = (log 2 + π/2)/4`, hence `bdGram (1/4) (1/4) = (3 log 2)/8 − π/32`,

which would give a better single-generator bound than the `1 − log 2` of `BaezDuarteHalfBound` (the `m = 4`
generator is a strictly better single approximant). That evaluation is *not* done here — it needs the
reindexing of a residue class onto `ℕ` and the arithmetic of the three linear relations among `T₀..T₃` — but
every ingredient it needs now exists, which was not clear before.

The honest scope of the correction: closed forms need digamma at rationals with denominator `2` or `4`, which
**is** available. Denominator `3` needs `ψ(1/3)`, i.e. Gauss's general theorem, which is still a mathlib TODO.

## Addendum (same day): the arithmetic-progression sums

`RHTower/ResidueClassRecipSeries.lean` carries the connector to its intended use. Taking `a = j/q`,
`b = (j+1)/q` and dividing by `q`:

* **`hasSum_residueClass_recip` — `∑_{k≥0} 1/((qk+j)(qk+j+1)) = (ψ((j+1)/q) − ψ(j/q))/q`** for `q, j ≥ 1`;
* `hasSum_odd_recip` — `∑_{k≥0} 1/((2k+1)(2k+2)) = log 2`, from `ψ(1) − ψ(1/2) = 2 log 2`. This **re-derives
  `hasSum_mod_div_mul_succ` at `m = 2` by an independent route** (digamma rather than the Mellin pairing), so
  two unrelated computations of the same constant agree — a genuine check on the earlier chain;
* **`hasSum_quarter_recip_one` — `∑_{k≥0} 1/((4k+1)(4k+2)) = (log 2 + π/2)/4`**, from mathlib's
  `digamma_one_half` and the corpus's `digamma_quarter`.

The last is the first value in this development involving `π`, and it is exactly the ingredient the `q = 4`
Báez-Duarte Gram entries were missing (`T₁` in the notation of the map card). What still stands between this
and `bdGram (1/4) (1/4)` is the decomposition of `ℕ` into residue classes as a `HasSum` — bookkeeping, but not
yet written.

## Addendum 2 (same day): the companion value, and all three quarter constants

`RHTower/DigammaThreeQuarter.lean`. `DigammaQuarter` proves `ψ(1/4)` and, on the way, the two relations
`ψ(1/4) + ψ(3/4) = 2ψ(1/2) − 2log 2` and `ψ(1/4) − ψ(3/4) = −π`. Either gives the companion value:

* **`digamma_three_quarter` — `ψ(3/4) = −γ − 3log 2 + π/2`.**

With it the remaining progressions mod `4` evaluate:

* **`hasSum_quarter_recip_two` — `∑_{k≥0} 1/((4k+2)(4k+3)) = (π/2 − log 2)/4`;**
* **`hasSum_quarter_recip_three` — `∑_{k≥0} 1/((4k+3)(4k+4)) = (3log 2 − π/2)/4`;**
* `quarter_recip_constants_pos` — both are positive, i.e. `log 2 < π/2 < 3log 2`, from mathlib's
  `log_two_gt_d9`, `log_two_lt_d9`, `pi_gt_d2`, `pi_lt_d2`.

So all three constants `T₁, T₂, T₃` of the `q = 4` decomposition are now proved:
`T₁ = (log 2 + π/2)/4`, `T₂ = (π/2 − log 2)/4`, `T₃ = (3log 2 − π/2)/4`. Since
`(n mod 4)² = (n mod 4) + 2·[n≡2] + 6·[n≡3]`, they predict
`∑ (n mod 4)²/(n(n+1)) = log 4 + 2T₂ + 6T₃ = 6log 2 − π/2` and hence
`bdGram (1/4) (1/4) = (3log 2)/8 − π/32`.

That assembly is the one step still missing: it needs the residue-class decomposition of `ℕ` as a `HasSum`
(three reindexings along `k ↦ 4k+j`, each via `Function.Injective.hasSum_iff`). The constants are done; the
bookkeeping is not.
