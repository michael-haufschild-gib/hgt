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
