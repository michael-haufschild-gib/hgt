# Möbius short-interval mean square with a power-of-log saving (Halász lane)

- **ID:** `ROUTE-E-MOEBIUS-HALASZ-LOG-SAVING-001`
- **Stage:** 1-in-progress
- **Type:** MILESTONE / SHARED GATE FOR THREE STAGE-2 CARDS
- **RH used:** no
- **Computation used:** no

## Why this card exists

Three stage-2 Route E cards are blocked on one and the same missing input.

- `2-fully-proven/new_scientific_knowledge/route-e-reciprocal-marker-mobius-hall-law.md`
- `2-fully-proven/new_scientific_knowledge/route-e-growing-reciprocal-marker-low-breadth-transport.md`
- `2-fully-proven/new_scientific_knowledge/route-e-coprime-square-root-mobius-product-sign-law.md`

The first two need the Möbius short-interval mean square with rate `o(1/log x)`; the third needs it
at windows as short as `(log log x)^{1+η}`. The corpus proves it at windows
`exp((log x)^β)`, `β > 9/10`, with rate `Θ(1/log log x)` — enough for the third card's *published*
window range but not for its full statement, and not enough for the first two at any window.

## The obstruction, precisely

`Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius` squeezes through
`Sieve/BudgetLimit.tendsto_normalised_omegaBudget`, which is bounded by
`136·slope + 140·energy + 131·const + nonSpectral`. The first three summands are powers of `log x`.
The fourth is not: `Sieve/NonSpectralBudget.nonSpectral_div_le` gives

```
3672/W² + 120·m/W² + 480·h²/(W²√x),    m = mertensS(zhi),  W = mertensS(zhi) − mertensS(zlo)
```

and `m ≍ β log log x`, `W ≍ (β−γβ) log log x`, so the middle term is `≍ 1/((β−γβ)² log log x)`.

This is the Ramaré normalisation's `1/W`, and it is structural: the identity divides by
`W = ∑_{zlo<p≤zhi} 1/p`, the `L²` diagonal costs one factor `1/W`, and `W ≤ log log x + O(1)` for
every admissible prime range. Exploiting the weight `1/(ω_P(m)+1)` sharply would reach only
`1/(log log x)³`. No choice of `β, γ, zlo, zhi` inside this decomposition reaches a power of `log`.

## Where the power of log has to come from

Menon's `(log log L)²/(log L)²` is the square of `log log L/log L`, and that factor is Halász's:
the pretentious distance of `μ` to every archimedean character satisfies

```
D(μ, n^{it}; N)² = ∑_{p≤N} (1 + cos(t log p))/p = log log N + Re ∑_{p≤N} p^{-1-it} + O(1),
```

so a lower bound on `|ζ(1+δ+it)|` at `δ = 1/log N` converts directly into a lower bound on `D²`, and
Halász turns `M = min_{|t|≤T} D²` into `(1+M)e^{-M}`.

**The corpus already owns the distance side.** `RHTower.ZetaLineLowerBound.primeCosPlusSum` is
exactly `D(μ,n^{it};x)²`, `pretentiousDistSq_neg_one_eq` identifies it with the pretentious distance
to the Liouville character, and `primeCosPlusSum_ge_low_freq` gives the full `log log x` for
`|t| ≤ 1`. What it does **not** own is a good uniform bound: `exists_antiscale_frame` yields only
`(log log log x − C)/4` over `|t| ≤ x^B`, which is weaker than the `1/log log x` it would have to beat.

The bound that suffices is the classical δ-free one,

```
|ζ(σ + it)| ≥ c (log|t|)^{-7}        for σ ≥ 1,  |t| ≥ t₀,                      (T)
```

giving `D² ≥ log log x − 7 log log(|t|+2) − C`; over the Halász range `|t| ≤ T` polynomial in
`log L` this is `log log L − O(log log log L)`, hence `e^{-M} ≍ (log log L)^7/log L`, whose square at
`log L = (log x)^{0.99}` is `o(1/log x)` with room to spare. Pure three-four-one gives only
`δ^{3/4}(log|t|)^{-1/4}`, i.e. exponent `1/4`, which is **not** enough — the squared saving
`(log x)^{-0.495}` misses `1/log x`.

## Route to (T), and what is already owned

Titchmarsh's argument: three-four-one at `σ = 1+δ` gives `|ζ| ≥ cδ^{3/4}(log|t|)^{-1/4}`; the
derivative bound `|ζ'| ≪ log²|t|` lets one slide from `1+δ` to any `1+δ₁` with `δ₁ ≤ δ` at cost
`δ·C log²|t|`; balancing at `δ ≍ (log|t|)^{-9}` leaves `(log|t|)^{-7}`, uniformly in `δ₁ ∈ [0, δ]`,
which covers the `δ₁ = 1/log x` the prime sum forces.

| Ingredient | Status |
|---|---|
| three-four-one, usable form | owned — `Sieve/ZetaThreeFourOne.log_norm_zeta_shift_ge` |
| pole bound `‖ζ(1+x)‖ ≤ 1/x + 2` | owned — `Sieve/ZetaThreeFourOne.abs_riemannZeta_one_add_le` |
| `‖ζ(σ+it)‖ ≤ log\|t\| + 5` on `σ ≥ 1` | owned — `ZetaVerticalLineBound.norm_riemannZeta_le_log_add` |
| the same just **left** of the one-line | **landed here (2026-08-18)** — see below |
| `‖ζ'(σ+it)‖ ≪ log²\|t\|` near the one-line | missing — Cauchy estimate on radius `1/log\|t\|` |
| (T) itself | missing |
| Halász's mean value theorem | missing; Halász–Montgomery large-values machinery is owned |
| insertion into the omega budget | missing |

## `RHTower/ZetaNearOneLineBound` — the strip bound (2026-08-18)

```
norm_riemannZeta_le_log_near_one (hσ1 : 1 − 1/log |s.im| ≤ s.re) (hσ2 : s.re ≤ 2) (ht : 8 ≤ |s.im|) :
  ‖riemannZeta s‖ ≤ 8 · log |s.im| + 39
```

unconditional, axiom-clean, wired into `GaloisForLFunctions.RHTower`. The existing vertical-line
bound stops at `σ ≥ 1`, which is exactly the wrong side: a Cauchy estimate for `ζ'` at a point of the
one-line needs a disc reaching left of it. Widening costs one factor `N^{1−σ}` at the
Euler–Maclaurin truncation `N = ⌈|t|⌉`, and that factor is bounded by `exp 2 ≤ 8` throughout the
strip because `log N ≤ 2 log|t|` there (`rpow_one_sub_le_eight`). Supporting pieces:
`norm_dirichletPoly_le_near_one`, `norm_emPole_le_near_one`, `two_le_log_of_eight_le`.

Next: the Cauchy estimate for `ζ'` on radius `1/log|t|`, then (T).

## What does not substitute

The corpus's long-range Möbius savings — `Sieve/MoebiusKappaTwoRate` (exponent `1/3`),
`Sieve/MoebiusSavingKappaTwo` (width-`log^{-2}` contour) — are useless here: at window
`exp((log x)^{0.99})` the zero-free-region error `x·exp(−c(log x)^{1/3})` dwarfs the window itself.

## The `δ`-free lower bound (T) is proved (2026-08-18)

Two further modules, both unconditional, axiom-clean, wired into `GaloisForLFunctions.RHTower`.

### `RHTower/ZetaDerivNearOneLineBound`

```
norm_deriv_riemannZeta_le_log_sq (1 ≤ s.re) (s.re ≤ 3/2) (9 ≤ |s.im|) :
  ‖deriv riemannZeta s‖ ≤ 110 · (log |s.im|)²
```

Cauchy's estimate on the disc of radius `1/(2 log|t|)`. The radius is what makes the strip bound
usable throughout the disc: every `w` in it has `log|w.im| ≤ 2 log|t|` (because `|w.im| ≤ |t|+1 ≤
|t|²`), so `w.re ≥ 1 − 1/(2 log|t|) ≥ 1 − 1/log|w.im|` — the hypothesis of
`ZetaNearOneLineBound.norm_riemannZeta_le_log_near_one`. The Cauchy step itself is the corpus's
`Sieve/ZetaDerivBound.norm_deriv_riemannZeta_le`, not a new one.

### `RHTower/ZetaOneLineLogPowerLowerBound`

```
exists_lower_bound_riemannZeta_near_one_line :
  ∃ c t₀, 0 < c ∧ 9 ≤ t₀ ∧ ∀ σ t, 1 ≤ σ → σ ≤ 5/4 → t₀ ≤ |t| →
    c / (log |t|)^11 ≤ ‖riemannZeta ((σ:ℂ) + (t:ℂ)·I)‖
```

**No dependence on the abscissa.** This is the statement three-four-one alone cannot give: at
`σ = 1+δ` it yields `δ^{3/4}(log|t|)^{-1/4}`, which degenerates as `δ → 0`, and that degeneration is
exactly what capped the earlier `exists_antiscale_frame` at `log log log x`.

The proof is Titchmarsh's balance, with the constants fixed. Take `δ = (log|t|)^{-14}` and apply
`Sieve/ZetaThreeFourOne.log_norm_zeta_shift_ge` at `σ+δ`, with the pole bound
`abs_riemannZeta_one_add_le` supplying `A ≤ log 2 + 14 log L` and the one-line growth bound
`ZetaVerticalLineBound.norm_riemannZeta_le_log_add` supplying `B ≤ log 4 + log L`. That gives
`log‖ζ(σ+δ+it)‖ ≥ K − (43/4) log L` with `K = (−22 − 3log 2 − log 4)/4`, hence
`‖ζ(σ+δ+it)‖ ≥ e^K L^{-11}`. Sliding back to `σ` along the segment costs
`δ · 110 L² = 110 L^{-12}` by the derivative bound and
`Sieve/ZetaDerivBound.norm_riemannZeta_sub_le`, which is smaller than half the main term once
`L ≥ 220 e^{-K}` — the threshold `t₀ = exp(220 e^{-K})`, absurdly large but harmless, since every
consumer is asymptotic.

Exponent `11` rather than Titchmarsh's `7`: the balance is not optimised, and the exponent enters
downstream only as the constant in `log log`, so nothing is lost.

### Updated ingredient table

| Ingredient | Status |
|---|---|
| three-four-one, usable form | owned |
| pole bound `‖ζ(1+x)‖ ≤ 1/x + 2` | owned |
| `‖ζ(σ+it)‖ ≤ log\|t\| + 5` on `σ ≥ 1` | owned |
| the same just left of the one-line | **landed** — `RHTower/ZetaNearOneLineBound` |
| `‖ζ'(σ+it)‖ ≪ log²\|t\|` near the one-line | **landed** — `RHTower/ZetaDerivNearOneLineBound` |
| (T), the `δ`-free lower bound | **landed** — `RHTower/ZetaOneLineLogPowerLowerBound` |
| `D(μ,n^{it};x)² ≥ log log x − 11 log log(\|t\|+2) − C` | next |
| Halász's mean value theorem | missing; Halász–Montgomery large-values machinery is owned |
| insertion into the omega budget | missing |

Next: feed (T) into `RHTower.ZetaLineLowerBound.primeCosPlusSum` in place of the Littlewood branch
of `exists_antiscale_frame`, upgrading its `(log log log x − C)/4` to
`log log x − 11 log log(|t|+2) − C`.

## `RHTower/MoebiusPretentiousGap` — the distance bound is proved (2026-08-18)

```
primeCosPlusSum_ge_of_zeta_lower (hc0 : 0 < c) (hx : exp 2 ≤ x)
    (hz : c ≤ ‖riemannZeta (((1 + 1/log x : ℝ):ℂ) + I·(t:ℂ))‖) :
  log log x + log c + 2·meisselMertensConst − (2((2·mertensFirstConst + 1/2) + 1) + zetaDeficitConst)
    ≤ primeCosPlusSum t x

exists_primeCosPlusSum_ge_logLog :
  ∃ C t₀, 9 ≤ t₀ ∧ ∀ x t, exp 4 ≤ x → t₀ ≤ |t| →
    log log x − 11·log log |t| − C ≤ primeCosPlusSum t x
```

The first is `ZetaLineLowerBound.primeCosPlusSum_ge_low_freq` with the frequency restriction removed
— that hypothesis was used only to produce the value of `ζ` at the single point `1 + 1/log x + it`,
so supplying the value directly frees the statement of any constraint on `t`. The second feeds (T)
into it. Against the corpus's `exists_antiscale_frame`, which gave `(log log log x − C)/4` uniformly
over `|t| ≤ x^B`, this is `log log x − 11 log log|t| − C`: over a range with `log T` polynomial in
`log x` it is `log log x − O(log log log x)`, i.e. essentially the full harmonic size.

**`μ` is now quantitatively unpretentious in this corpus.** That is the input a Halász argument
needs, and it is done.

## Correction: the gate is not Halász — it is Turán–Kubilius (2026-08-18)

Reading `Sieve/OmegaSpectralFibre` settles where the `1/W` comes from, and it is not intrinsic.
Its module docstring says the chain is "the Turán–Kubilius transfer, the rescaled fibre bridge and
Plancherel", and line 44 names the third summand of `sum_sq_fibreSum_moebius_le_omegaSpectral` as
"the Turán–Kubilius variance". The transfer writes `∑ μ ≈ (1/W) ∑ μ·ω_P` and pays the variance
`∑_{n∈I}(ω_P(n) − W)² ≍ |I|·W` through Cauchy–Schwarz — which takes a **square root**, so an error
of relative size `W` in the variance becomes `1/W` in the answer. That is the whole of the
`120·mertensS(zhi)/W²` term.

Matomäki–Radziwiłł do not use Turán–Kubilius. They use the **exact** Ramaré identity: for `n` with
`ω_P(n) ≥ 1`, `1 = ∑_{p|n, p∈P} 1/ω_P(n)`, hence

```
∑_{n∈I} μ(n) = ∑_{n∈I, ω_P(n)=0} μ(n) + ∑_{p∈P} ∑_{n∈I, p|n} μ(n)/ω_P(n).
```

There is no variance and no Cauchy–Schwarz. The first term is the rough-number count, bounded by a
sieve at `≍ |I|·log z₀/log z`, and — decisively — it enters the mean square **squared**, giving
`(log z₀/log z)² ≤ (log x)^{-1.98}` at the card's parameters, comfortably `o(1/log x)`. The second
term is exactly the bilinear object the existing spectral machinery already handles, whose three
majorants (`rhoMajorant`, `slopeMajorant`, `constMajorant`) are already powers of `log x` with
dominant term `(log x)^{5/4-β-γβ}`, squared past `(log x)^{-1.1}`.

**So the whole normalised budget becomes a power of `log x` once the Turán–Kubilius transfer is
replaced by the exact identity.** No Halász theorem is required for the mean square.

The corpus already owns both halves of the replacement:

- the exact decomposition — `Sieve/RamareSquareMultiple.logPoly_moebius_eq_ramare_add_rough`
  ("the apparent square-multiple error in the three-way decomposition vanishes coefficientwise"),
  `Sieve/RamareComplex.sum_eq_ramare_add_rough_complex`,
  `Sieve/RamarePhaseBilinear.ramareCofactorCoeff` (Möbius damped by `ω_P` of the cofactor);
- `Sieve/RamareWeight.sum_inv_card_primeFactorsIn` (total weight one),
  `Sieve/SupportMeanSquare.roughSet` (the integers carrying no designated prime factor).

What must be built: a sieve upper bound for `#{n ∈ (t, t+L] : ω_P(n) = 0}` with `P` the primes in
`(z₀, z]` and `z = L^{o(1)}`, and then the analogue of `sum_sq_fibreSum_moebius_le_omegaSpectral`
routed through the exact identity instead of the variance.

The Halász lane above is not wasted — `exists_primeCosPlusSum_ge_logLog` is the sharpest uniform
unpretentiousness statement in the corpus and is the right input if a Halász argument is wanted
later — but it is no longer the critical path. **This card's target is now the Ramaré swap.**
