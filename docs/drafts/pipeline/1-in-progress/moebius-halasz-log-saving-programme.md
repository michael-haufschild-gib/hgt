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

## The Turán–Kubilius step is replaced (2026-08-18)

Two modules, unconditional, axiom-clean, wired into `GaloisForLFunctions.RHTower`.

### `Sieve/FibreRamareSplit`

```
fibreRamareSieveError h z r lam                       -- the uniform per-fibre sieve error
abs_fibreSum_sub_ramare_le                            -- one fibre's Ramaré defect
sum_sq_fibreSum_moebius_le_ramare_add_rough           -- ∑ A² ≤ 2∑R² + 2·#outer·E²
```

### `Sieve/FibreNonRoughSpectral` — the replacement itself

```
nonRoughMoebius P n = if (primeFactorsIn P n).Nonempty then μ n else 0

sum_sq_fibreSum_moebius_le_nonRough_spectral (hx : 4 ≤ x) (hh0 : 0 ≤ h) (hhx : h ≤ √x)
    (hz : 2 ≤ z) (hr : Even r) (hlam : 1 ≤ lam) :
  ∑_a (∑_{b ∈ fibre} μ b)²
    ≤ 2·(8√x·∫‖logWindowSum (nonRoughMoebius (primesLE z)) (fibreIndex x h) (fibreWidth x h) u‖² du
         + 102(√x + 1))
      + 2·#outerBlock·(fibreRamareSieveError h z r lam)²
```

This is the analogue of `Sieve/OmegaSpectralFibre.sum_sq_fibreSum_moebius_le_omegaSpectral` with
**no `1/W²` in front of the spectral term and no variance behind it**. Three facts make it work:

1. The split at the rough integers is exact and costs no Cauchy–Schwarz — the fibre sum of `μ`
   minus its non-rough part is literally the rough sum, bounded by the rough *count*.
2. That count is Brun's pure sieve, `Sieve/RoughCount.card_rough_Ioc_le`, already owned.
3. The restricted weight is still unit-bounded, so the coefficient-general bridge
   `Sieve/ScaledFibreBridge.sum_fibreSum_sq_le_integral_scaled` carries it to the spectral side with
   no change of constants — the bridge never needed the weight to be `μ·ω_P`.

**The rough error enters squared.** With `E ≍ (h+2)·C/log z` and `#outerBlock ≍ √x`, the rough
contribution to the normalised mean square is `2E²/h² ≍ C²/(log z)²`. Taking
`z = exp((log x)^{3/5})` gives `(log x)^{-6/5}`, comfortably `o(1/log x)`, while
`log z/log h = (log x)^{-39/100} → 0` keeps the sieve level legitimate. Contrast the
Turán–Kubilius term, which is `1/W ≥ 1/(log log x + O(1))` at every parameter choice.

### What remains on this card

The spectral term must be bounded by the existing majorants. `logWindowSum` factors as
`logWindowKernel × Dirichlet polynomial` (`Sieve/LogWindowPlancherel`), so the remaining chain is:

- factor the `nonRoughMoebius` polynomial through the Ramaré bilinear form — the corpus owns
  `Sieve/RamarePhaseBilinear.ramareCofactorCoeff` and
  `Sieve/RamareSquareMultiple.logPoly_moebius_eq_ramare_add_rough` for exactly this;
- run the existing prime × cofactor large-values machinery on it, whose three majorants
  (`rhoMajorant`, `slopeMajorant`, `constMajorant`) are already powers of `log x` past
  `(log x)^{-1.1}`;
- assemble the analogue of `Sieve/BudgetLimit.tendsto_normalised_omegaBudget` with an explicit
  `(log x)^{-A}`, `A > 1`, and feed it to `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

That last step is what promotes the two reciprocal-marker cards; the coprime-sign card additionally
needs the window pushed towards `log log x`, which the same chain supplies once the exponent
constraint `β > 9/10` is traced to whichever majorant imposes it.

## The chain now reaches the majorant machinery (2026-08-18)

Two more modules, unconditional, axiom-clean, wired.

### `Sieve/FibreNonRoughKernel`

Plancherel (`LogWindowPlancherel.integral_normSq_logWindowSum_eq`) puts the previous bound in the
shape the corpus's majorants consume:

```
sum_sq_fibreSum_moebius_le_nonRough_kernel :
  ∑_a (∑_{b ∈ fibre} μ b)²
    ≤ 16√x · ∫ ‖logWindowKernel (fibreWidth x h) w‖² · ‖logPoly (nonRoughMoebius (primesLE z)) (fibreIndex x h) w‖² dw
      + 204(√x + 1) + 2·#outerBlock·(fibreRamareSieveError h z r lam)²
```

### `Sieve/NonRoughRamareBilinear`

```
logPoly_nonRoughMoebius_eq_ramare (P s : Finset ℕ) (w : ℝ) :
  logPoly (nonRoughMoebius P) s w
    = ∑_{p ∈ P} ∑_{n ∈ s, p ∣ n} (μ n · e(w log n)) / ω_P(n)
```

An **identity, with no error term**: restricting `μ` to integers carrying a designated prime factor
removes precisely the rough term of Ramaré's decomposition, so the restricted polynomial *is* the
bilinear form. This is what makes the restricted weight the right object — it is unit-bounded, so
the fibre bridge carries it, and it factors over designated prime times cofactor, so the
large-values machinery applies. Combining gives
`sum_sq_fibreSum_moebius_le_ramareBilinear_kernel`, the full chain with no `1/W²` anywhere.

### Side-by-side with the old chain

| | `OmegaSpectralFibre` (Turán–Kubilius) | `NonRoughRamareBilinear` (exact Ramaré) |
|---|---|---|
| left side | `(mertensS z − mertensS z₀)² · ∑_a (∑ μ)²` | `∑_a (∑ μ)²` — no `W²` |
| polynomial weight | `μ · ω_P`, bounded by `W` | `nonRoughMoebius`, bounded by `1` |
| error term | Turán–Kubilius variance, linear ⇒ `1/W` | sieve density, **squared** ⇒ `1/(log z)²` |
| best achievable rate | `1/log log x` | `(log x)^{-6/5}` at `z = exp((log x)^{3/5})` |

### What remains

Bound `∫ ‖kernel‖²‖bilinear‖²` by the existing prime × cofactor majorants — the same
`rhoMajorant` / `slopeMajorant` / `constMajorant` route `Sieve/BudgetLimit` already runs, but
applied to the `1/ω_P`-weighted cofactor (`Sieve/RamarePhaseBilinear.ramareCofactorCoeff`) instead
of the `ω_P`-weighted one. Then assemble the explicit `(log x)^{-A}`, `A > 1`, and feed it to
`Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## `Sieve/NonRoughBilinearFactor` — the factorisation, diagonal error only (2026-08-18)

```
norm_logPoly_nonRoughMoebius_sub_ramare_bilinear_le (hPprime : ∀ q ∈ P, q.Prime) (s) (w) :
  ‖logPoly (nonRoughMoebius P) s w
      − ∑_{p ∈ P} moebiusPhase w p · logPoly (ramareCofactorCoeff P) {m ∈ cofactorSet s p | ¬p∣m} w‖
    ≤ ∑_{p ∈ P} #{m ∈ cofactorSet s p | p ∣ m}
```

The corpus's `RamarePhaseBilinear.norm_logPoly_moebius_sub_ramare_bilinear_le` factors the **full**
Möbius polynomial and pays two errors: the square-multiple diagonal and the rough integers. For the
non-rough polynomial the second is absent by construction — rough indices carry coefficient `0` —
so only the diagonal remains. This is not cosmetic: the rough term has already been paid once, per
fibre and *squared*, in `Sieve/FibreNonRoughSpectral`, and paying it again at the polynomial level
would reinstate the linear loss the whole Ramaré route exists to avoid.

With this the structural chain is complete end to end:

```
∑_a (∑_{b ∈ fibre} μ b)²                                  -- the Route E input
  ≤ 16√x·∫‖kernel‖²‖logPoly (nonRoughMoebius P)‖² + 204(√x+1) + 2·#outer·E²   (FibreNonRoughKernel)
logPoly (nonRoughMoebius P) = Ramaré bilinear form, exactly                   (NonRoughRamareBilinear)
                            = ∑_p (prime phase)·(cofactor poly) + diagonal    (NonRoughBilinearFactor)
```

and every step is unconditional and axiom-clean. No `1/W²`, no Turán–Kubilius variance.

### The one remaining step

Bound `∫‖kernel‖²‖∑_p (prime phase)·(cofactor poly)‖²` by the existing majorants. The Hall-law card
records that `Sieve/RamareBlockSplit` "already reduces the plain Möbius polynomial to the same
geometric ladder of (prime block) × (cofactor block) products that the spectral programme bounds",
so the ladder should accept this form directly — check `RamareBlockSplit` against
`ramareCofactorCoeff` first. Then assemble the explicit `(log x)^{-A}`, `A > 1`, and feed
`Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`. Also to settle there: the diagonal
error `∑_p #{m ∈ cofactorSet s p | p ∣ m}` is `≍ |s|·∑_{p ∈ P} 1/p²  ≪ |s|/z₀`, negligible once the
lower cut `z₀` grows, but it needs its own bound.

## The factorisation is exact, and the capstone is assembled (2026-08-18)

The square-multiple diagonal does not merely admit a bound — it **vanishes**. If the designated
prime divides the cofactor then the index carries the square of a prime, so its Möbius phase is zero
(`Sieve/OmegaWeightedFactorisation.moebiusPhase_eq_zero_of_dvd`). Combined with the absence of a
rough term for the non-rough polynomial, the factorisation is an identity:

```
Sieve/NonRoughBilinearExact.logPoly_nonRoughMoebius_eq_ramare_bilinear
    (hPprime : ∀ q ∈ P, q.Prime) (s : Finset ℕ) (w : ℝ) :
  logPoly (nonRoughMoebius P) s w
    = ∑_{p ∈ P} moebiusPhase w p · logPoly (ramareCofactorCoeff P) {m ∈ cofactorSet s p | ¬p∣m} w
```

No rough term, no diagonal, no error. The previous `norm_…_le` form is superseded by this.

```
Sieve/FibreBilinearCapstone.sum_sq_fibreSum_moebius_le_bilinear_kernel_exact
    (4 ≤ x) (0 ≤ h) (h ≤ √x) (2 ≤ z) (Even r) (1 ≤ lam) :
  ∑_a (∑_{b ∈ fibre} μ b)²
    ≤ 16√x · ∫ ‖logWindowKernel (fibreWidth x h) w‖²
              · ‖∑_{p ≤ z} moebiusPhase w p · logPoly (ramareCofactorCoeff (primesLE z))
                    {m ∈ cofactorSet (fibreIndex x h) p | ¬p∣m} w‖² dw
      + 204(√x + 1) + 2·#outerBlock·(fibreRamareSieveError h z r lam)²
```

**This is the replacement for `Sieve/OmegaSpectralFibre.sum_sq_fibreSum_moebius_le_omegaSpectral`,
complete.** No `(mertensS z − mertensS z₀)²` divides the left side; no Turán–Kubilius variance sits
on the right; the only error is the sieve density, squared. The `1/log log x` ceiling is gone.

### The single remaining step

Bound

```
∫ ‖logWindowKernel (fibreWidth x h) w‖² · ‖∑_{p ≤ z} moebiusPhase w p · (cofactor poly)‖² dw
```

by the corpus's existing ladder. The integrand is exactly a (prime block) × (cofactor block) product
of the kind `Sieve/RamareBlockSplit` reduces to the geometric ladder that `Sieve/RhoLimit`,
`Sieve/SlopeQuotientLimit` and `Sieve/ConstQuotientLimit` majorize — whose dominant term is
`(log x)^{5/4−β−γβ}`, squared past `(log x)^{-1.1}`. Then choose `z = exp((log x)^{3/5})`, which
makes the sieve term `(log x)^{-6/5}`, assemble the explicit `(log x)^{-A}` with `A > 1`, and feed
`Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## `Sieve/FibreRamareBilinearBridge` — the chain meets the existing ladder (2026-08-18)

`fibreIndex x h` unfolds to `Finset.Icc 1 ⌊√x + h⌋₊`, which is exactly the index range
`Sieve/RamareBilinearMeanSquare.ramareBilinear` is defined over. The capstone's integrand is
therefore *literally* `‖ramareBilinear (primesLE z) ⌊√x + h⌋₊ w‖²`:

```
sum_sq_fibreSum_moebius_le_ramareBilinear_ladder (4 ≤ x) (0 ≤ h) (h ≤ √x) (2 ≤ z) (Even r) (1 ≤ lam) :
  ∑_a (∑_{b ∈ fibre} μ b)²
    ≤ 16√x · ∫ ‖logWindowKernel (fibreWidth x h) w‖² · ‖ramareBilinear (primesLE z) ⌊√x+h⌋₊ w‖² dw
      + 204(√x + 1) + 2·#outerBlock·(fibreRamareSieveError h z r lam)²
```

So `Sieve/RamareBlockSplit` applies unchanged: `integral_normSq_ramareBilinear_le_geomLadder` splits
a geometric prime range into `L` blocks at cost `L`, and `integral_normSq_ramareBlock_le_product`
turns each block into `(primeBlockPoly)·(cofactor polynomial)` — the shape the majorants bound.

### The remaining step, now small

The ladder lemmas integrate over `Set.Icc (-W) W` with no kernel weight, while the capstone has the
kernel over all of `ℝ`. What is needed is the split

```
∫_ℝ ‖logWindowKernel δ w‖²‖F w‖²  ≤  (sup_{|w| ≤ W} ‖kernel‖²)·∫_{Icc (-W) W} ‖F‖²  +  (tail)
```

with the tail controlled by `‖logWindowKernel δ w‖ ≤ 1/(π|w|)`
(`LogWindowPlancherel.norm_logWindowKernel`). The corpus performs exactly this split for
`omegaWeightedMoebiusPoly` inside `Sieve/BudgetTermSplit` on the way to
`Sieve/BudgetLimit.tendsto_normalised_omegaBudget`; check whether those lemmas are already
coefficient-general before writing anything — if they are, the remaining work is instantiation
rather than construction.

After that: `z = exp((log x)^{3/5})` for the sieve term `(log x)^{-6/5}`, assemble the explicit
`(log x)^{-A}` with `A > 1`, and feed `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## Scoping the last step: what the ladder actually depends on (2026-08-18)

Checked, so the next session need not re-derive it:

- `Sieve/BudgetTermSplit` is **pure real arithmetic** — `budget_div_eq` and `spectral_terms_le`
  rearrange scalars. Nothing there needs adapting.
- The kernel integral is bounded in `Sieve/BudgetSubstitution.exists_eventually_omegaBudget_le`,
  which is a specialisation of `Sieve/OmegaBudgetMaster.exists_omegaBudget_master`.
- `exists_omegaBudget_master` is stated for `omegaBudget x h z₀ z` specifically, i.e. for the
  `ω_P`-weighted polynomial. Its **conclusion**, however, mentions only parameter functions —
  `ladderAffineSlope`, `ladderAffineConst`, `ladderRho`, `relMoebiusSharp` — and no coefficient
  sequence. The coefficient enters solely through the definition of `omegaBudget`.

So the remaining task is to produce the coefficient-general form of that master theorem, or a
parallel instance for `ramareCofactorCoeff`. Two facts make this favourable rather than a rewrite:

1. `‖ramareCofactorCoeff P m‖ ≤ 1` pointwise, whereas `‖omegaCoeff P n‖ ≤ #P + 1`. The Ramaré
   coefficient is *better* behaved, so any bound proved from a coefficient bound carries over.
2. `Sieve/RamareBlockSplit` already provides the block decomposition for exactly this coefficient —
   `integral_normSq_ramareBilinear_le_geomLadder` and `integral_normSq_ramareBlock_le_product` are
   stated in terms of `ramareCofactorCoeff`, not `omegaCoeff`. The ladder was *built* for the Ramaré
   form; only the master assembly was wired to the Turán–Kubilius one.

Concrete first move next session: read `Sieve/LadderBlockFacts` and the large-values input of
`exists_omegaBudget_master`, and determine whether the coefficient appears there only through an
`ℓ²` mass hypothesis. If it does, the general version is an instantiation; if not, the specific
places where `omegaCoeff` is unfolded are the edit sites.

## Where the last step really sits: the cofactor, not the assembly (2026-08-18)

Read `Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final`. Its two inputs are sup bounds:

- `hV` — the prime block: `‖primeBlockPoly (geomBlock …) w‖ ≤ ρ·(Q(1+η)^j)` off the low window;
- `hU` — the cofactor block: `‖logPoly moebiusCoeff (geomCofactorBlockAt …) w‖ ≤ s·(B₀/(Q(1+η)^j))`
  on the low window.

`hU` is stated for **`moebiusCoeff`**, the *plain* Möbius coefficient — and that is what
`Sieve/CofactorLowFreqBound` bounds. So the `ω_P` normalisation's virtue was never the spectral main
term; it was that its cofactor is a plain Möbius polynomial.

**This is the real cost of the exact-Ramaré swap.** My chain lands on `ramareCofactorCoeff m =
μ(m)/(ω_P(m)+1)`, a *damped* cofactor, for which no sup bound exists in the corpus. The assembly
(`exists_omegaBudget_master`, `BudgetSubstitution`, `BudgetTermSplit`) is otherwise reusable; the
missing brick is one sup bound, not a refactor.

Two routes to it, both classical:

1. **Integral representation.** `1/(k+1) = ∫₀¹ t^k dt`, so
   `logPoly (ramareCofactorCoeff P) C w = ∫₀¹ logPoly (fun m => μ(m)·t^{ω_P(m)}) C w dt`. The inner
   polynomial is a plain twisted Möbius sum with a multiplicative `t^{ω_P}` factor, so
   `CofactorLowFreqBound`'s contour argument should extend to it uniformly in `t ∈ [0,1]`; the sup
   bound then passes through the `t`-average. This keeps the exact identity and adds one parameter.

2. **One prime factor per block.** Restrict to `n` with `ω_P(n) = 1` rather than `≥ 1`. On that set
   the Ramaré weight is exactly `1`, so the cofactor is *plain* Möbius and `hU` applies verbatim.
   The discarded parts are `ω_P(n) = 0` (rough — the sieve bound already built) and `ω_P(n) ≥ 2`
   (bounded by `|S|·(∑_{p∈P} 1/p)²/2`, small when the block is narrow), and both enter squared.
   The tension is that rough-smallness wants a wide `P` while `ω_P ≤ 1` wants a narrow one; the
   geometric ladder (`geomBlock`) is exactly the device that resolves it, assigning each `n` to its
   smallest block.

Route 2 reuses strictly more of the corpus and needs no new contour work, so try it first: build
`nonRoughMoebius` restricted to `ω_P(n) = 1` and the `ω_P ≥ 2` count, then re-run
`Sieve/FibreNonRoughSpectral` through it. Route 1 is the fallback if the ladder bookkeeping for the
`ω_P ≥ 2` part proves worse than the damped contour bound.

## Route 2 does not work in its simple form — and what does (2026-08-18)

`Sieve/UnitOmegaMoebiusSplit` is built and axiom-clean:

```
unitOmegaMoebius P n = if (primeFactorsIn P n).card = 1 then μ n else 0
abs_sum_sub_unitOmega_le          -- the two discards: ω_P = 0 and ω_P ≥ 2
sum_sq_fibreSum_moebius_le_unitOmega  -- both discards enter the fibre mean square squared
```

But the two discards cannot be small at once for a **single** prime set `P = (z₀, z]`:

- rough, `#{ω_P = 0} ≍ L·log z₀/log z`, wants `P` **wide**;
- `#{ω_P ≥ 2} ≍ L·(∑_{p ∈ P} 1/p)²/2 ≍ L(log log z − log log z₀)²`, wants `P` **narrow**.

Narrow enough for the second (`z = z₀^{1+o(1)}`) makes the first `≍ 1`. So the plain restriction to
`ω_P = 1` is a dead end, and the `ω_P ≥ 2` counting lemma should **not** be built for it. The split
module is still correct and reusable — it is the right statement once `P` is one block of a ladder,
where each `n` is assigned to the block holding its *smallest* designated prime factor. That
assignment, not the global restriction, is the MR device.

### The route that does not have this tension

Do not bound the cofactor polynomial in sup at all. `Sieve/RamareBlockSplit` already reduces a block
to `(primeBlockPoly B)·(logPoly (ramareCofactorCoeff P) C)`; bound the **mean square** of that
product by large values, which needs only the `ℓ²` masses — and
`∑_m ‖ramareCofactorCoeff P m‖² ≤ ∑_m ‖μ m‖² ≤ #C`, immediate, since dividing by `ω_P(m)+1 ≥ 1`
only shrinks. This is also what Matomäki–Radziwiłł actually do; the sup bound on the cofactor is the
corpus's own simplification, available only because the `ω_P` normalisation left a *plain* Möbius
cofactor.

The corpus's large-values stack is already there: `Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`,
`Sieve/MatomakiTeravainenTypeIISparseHalaszMontgomery.halaszMontgomery_blockPoly_finset_explicit`,
`Sieve/LargeSieveWeak`, `Sieve/DirichletMeasureLargeValues`.

**Next session, in order:** (1) read `integral_normSq_ramareBlock_le_product`'s conclusion and see
what it needs about the product; (2) supply the `ℓ²` mass bound for `ramareCofactorCoeff`
(one line from `‖μ‖ ≤ 1`); (3) feed the Halász–Montgomery block bound instead of a cofactor sup.

Fallback if that stalls: the damped cofactor's own contour bound, via `1/(k+1) = ∫₀¹ t^k dt`, whose
Dirichlet series is `(1/ζ(s))·∏_{p ∈ P}(1 − t p^{-s})/(1 − p^{-s})` — a polylog perturbation of the
one `Sieve/CofactorLowFreqBound` already handles.

## The missing input is now one classical estimate (2026-08-18)

Two modules, built, wired, axiom-clean.

### `Sieve/DampedCofactorIntegral`

```
dampedOmegaMoebius P t m = μ(m) · t^{ω_P(m)}
norm_dampedOmegaMoebius_le_one (0 ≤ t) (t ≤ 1) : ‖dampedOmegaMoebius P t m‖ ≤ 1
logPoly_ramareCofactorCoeff_eq_integral (P C : Finset ℕ) (w : ℝ) :
  logPoly (ramareCofactorCoeff P) C w = ∫ t in (0:ℝ)..1, logPoly (dampedOmegaMoebius P t) C w
```

`1/(k+1) = ∫₀¹ t^k dt` applied coefficientwise, with the finite sum pulled through the integral.

### `Sieve/DampedCofactorTransfer`

```
norm_logPoly_ramareCofactorCoeff_le_of_uniform (P C : Finset ℕ) (w : ℝ)
    (hunif : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖logPoly (dampedOmegaMoebius P t) C w‖ ≤ s) :
  ‖logPoly (ramareCofactorCoeff P) C w‖ ≤ s
```

Averaging cannot increase a sup bound.

### What this buys

The `hU` hypothesis of `Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final` needs a genuine
*saving* on the cofactor polynomial — the trivial `#C` is useless there, which is why
`Sieve/CofactorLowFreqBound` exists. With the two lemmas above, the exact-Ramaré route's entire
remaining analytic debt is:

> **a saving for `∑_{m ∈ C} μ(m)·t^{ω_P(m)}·e(w log m)` on the low window, uniform in `t ∈ [0,1]`.**

No Ramaré bookkeeping remains in that statement. At `t = 1` it *is* the plain cofactor bound
`CofactorLowFreqBound` already proves; for general `t` the Dirichlet series is

```
∑_m μ(m) t^{ω_P(m)} m^{-s} = (1/ζ(s)) · ∏_{p ∈ P} (1 − t·p^{-s})/(1 − p^{-s}),
```

so the correction factor is an Euler product over `P` alone, bounded by
`∏_{p ∈ P}(1 + 1/p)/(1 − 1/p) = exp(O(∑_{p ∈ P} 1/p))` — polylog in the card's parameter range, and
uniform in `t` since `|1 − t p^{-s}| ≤ 1 + 1/p^{Re s}`. Extending `CofactorLowFreqBound`'s contour
argument by that bounded factor is the next construction.

## `Sieve/DampedEulerCorrection` — the perturbation factor is bounded (2026-08-18)

```
dampedEulerFactor t p s = (1 − t·p^{-s}) / (1 − p^{-s})

norm_dampedEulerFactor_le (2 ≤ p) (0 ≤ t) (t ≤ 1) (1/2 ≤ s.re) :
  ‖dampedEulerFactor t p s‖ ≤ (1 + p^{-Re s}) / (1 − p^{-Re s})

norm_prod_dampedEulerFactor_le (∀ p ∈ P, 2 ≤ p) (0 ≤ t) (t ≤ 1) (1/2 ≤ s.re) :
  ‖∏_{p ∈ P} dampedEulerFactor t p s‖ ≤ ∏_{p ∈ P} (1 + p^{-Re s})/(1 − p^{-Re s})
```

Both bounds are **independent of `t`**, which is what
`Sieve/DampedCofactorTransfer.norm_logPoly_ramareCofactorCoeff_le_of_uniform` requires. The
denominator is safe on `Re s ≥ 1/2` because `p^{-Re s} ≤ 2^{-1/2} < 1` for `p ≥ 2`, and the product
is `exp(O(∑_{p ∈ P} p^{-Re s}))`, a polylog at the Route E parameters.

### Where the remaining debt sits now

`Sieve/CofactorLowFreqBound.exists_norm_logPoly_moebiusCoeff_Icc_le` obtains its saving from the
corpus's Möbius contour stack (`Sieve/MoebiusContourKappaTwo`, `Sieve/MoebiusSaving`,
`Sieve/MoebiusKappaTwoRate`), all of which are written for `1/ζ(s)`. The damped version needs the
same stack for `(1/ζ(s))·∏_{p ∈ P} dampedEulerFactor t p s`. With the factor bound above, that is a
mechanical widening of each contour edge by one bounded multiplier rather than a new argument —
but it is several modules, since the stack computes explicit edge constants.

Tried and rejected on the way: expanding `t^{ω_P(m)} = ∑_{d | gcd(m, ∏P)} (t−1)^{ω(d)}` to reduce
the damped sum to undamped ones. The divisor sum has `2^{|P|}` terms and `∑_d |t−1|^{ω(d)} = 2^{|P|}`
at `t = 0`, so nothing is gained; the contour route is necessary.

## `RHTower/DampedPretentiousGap` — the damped function is unpretentious too (2026-08-18)

```
dampedCosPlusSum P t τ x = ∑_{p ≤ x} (1 + (if p ∈ P then t else 1)·cos(τ log p))/p

dampedCosPlusSum_ge (0 ≤ t) (t ≤ 1) :
  primeCosPlusSum τ x − ∑_{p ≤ x, p ∈ P} 1/p ≤ dampedCosPlusSum P t τ x

exists_dampedCosPlusSum_ge_logLog :
  ∃ C t₀, 9 ≤ t₀ ∧ ∀ P t x τ, 0 ≤ t → t ≤ 1 → exp 4 ≤ x → t₀ ≤ |τ| →
    log log x − 11·log log|τ| − C − ∑_{p ≤ x, p ∈ P} 1/p ≤ dampedCosPlusSum P t τ x
```

`m ↦ μ(m)·t^{ω_P(m)}` differs from `μ` only at the designated primes, so its squared pretentious
distance loses at most the harmonic mass of `P`. At the card's parameters that mass is
`≍ (β − γβ)·log log x` with `β − γβ ≈ 0.08`, so the damped distance is still `≈ 0.9·log log x` —
uniformly in the damping `t`.

## The two routes to the damped saving, and the choice

Both remaining routes now have all their *arithmetic* inputs.

**(A) Damped contour.** Redo `Sieve/MoebiusContourKappaTwo` → `MoebiusSaving` → `MoebiusKappaTwoRate`
for `(1/ζ(s))·∏_{p ∈ P} dampedEulerFactor t p s`. The perturbation is bounded
(`Sieve/DampedEulerCorrection`) and `t`-uniform, so each contour edge widens by one multiplier.
Mechanical, but the stack is `PerronSharpSubstitution` + `MellinAbscissaDecay` +
`MoebiusContourBound` + three more, all carrying explicit edge constants, and all authored elsewhere.

**(B) Halász.** With `exists_dampedCosPlusSum_ge_logLog` the pretentious input is done, uniformly in
`t`; Halász's mean value theorem then gives `(1+M)e^{-M}` with `M ≈ 0.9 log log x`, i.e. a saving
`(log x)^{-0.9+o(1)}`. The corpus owns the Halász–Montgomery large-values machinery
(`Sieve/DyadicSecondEnvelopeClosed`, `Sieve/DirichletMeasureLargeValues`, `Sieve/LargeSieveWeak`) and
Dirichlet-polynomial mean value theorems — the ingredients of Montgomery's proof — but not the
theorem itself.

**Choose (B).** It is one theorem rather than a six-module rewrite of another session's stack, it
consumes the distance bounds already proved here, and it is the general tool: it also settles the
plain cofactor, the coprime-sign card's short-window range, and anything else in the corpus that
currently reaches for a contour. Route (A) stays recorded as the fallback if Montgomery's argument
resists formalisation.

## `Sieve/DampedMultiplicative` — the damped function feeds the Euler bound (2026-08-18)

```
primeFactorsIn_mul (∀ q ∈ P, q.Prime) (m n) :
  primeFactorsIn P (m*n) = primeFactorsIn P m ∪ primeFactorsIn P n
primeFactorsIn_disjoint_of_coprime, card_primeFactorsIn_mul_of_coprime
dampedOmegaMoebius_mul_of_coprime : dampedOmegaMoebius P t (m*n) = … m * … n
dampedOmegaMoebius_one
```

With `norm_dampedOmegaMoebius_le_one` this is exactly the hypothesis package of
`Sieve/MultiplicativeEulerBound.norm_tsum_twistedSummand_le_exp`:

```
‖∑'_n f(n) n^{-s}‖ ≤ exp( ∑'_p Re(f(p) p^{-s}) + 5/2 ),   Re s > 1,
```

so the damped Dirichlet series is bounded by the exponential of its prime sum — and that prime sum
is `∑_p 1/p^σ − (the damped distance)`, which `RHTower/DampedPretentiousGap` bounds from below
uniformly in `t` and in the frequency.

### Status of the Halász lane

| Ingredient | Status |
|---|---|
| distance for `μ`, uniform in frequency | **owned** — `RHTower/MoebiusPretentiousGap` |
| distance for the damped function, uniform in `t` | **owned** — `RHTower/DampedPretentiousGap` |
| damped function multiplicative and unit-bounded | **owned** — this module |
| Euler bound `‖F(s)‖ ≤ exp(prime sum + 5/2)` | owned (corpus) |
| **`‖F(1+1/log x + iτ)‖ ≪ (log x)·e^{-D²}`** | next — bookkeeping between `σ > 1` and the truncated sum at `x` |
| Halász's mean value theorem | missing; Halász–Montgomery large values and Dirichlet mean values are owned |

The next brick is the one marked: reconcile the `σ = 1 + 1/log x` Euler prime sum with the
`primeCosPlusSum`/`dampedCosPlusSum` truncated at `x`. That is Mertens bookkeeping of the kind
`RHTower/ZetaLineLowerBound` already does for the undamped case
(`abs_zeta_deficit_sub_primeClockEnergy_le`), and it turns the distance bounds into an actual bound
on the Dirichlet series — the object Halász's proof integrates.

## `Sieve/DampedEulerSeriesBound` — the series bound (2026-08-18)

```
norm_tsum_dampedOmegaMoebius_le (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (1 < s.re) :
  ‖∑'_n twistedSummand (dampedOmegaMoebius P t) s n‖
    ≤ exp( (∑'_p (twistedSummand (dampedOmegaMoebius P t) s p).re) + 5/2 )
```

A direct instantiation of `Sieve/MultiplicativeEulerBound.norm_tsum_twistedSummand_le_exp` at the
damped function, now that `Sieve/DampedMultiplicative` supplies the hypothesis package. Warning-free.

### The next brick, stated exactly

Convert the prime sum into cosine form and then into the damped distance. Two steps:

1. `(twistedSummand (dampedOmegaMoebius P t) (σ + iτ) p).re
      = −(if p ∈ P then t else 1)·p^{-σ}·cos(τ log p)` for `p` prime.
   Needs `μ(p) = −1`, `(primeFactorsIn P p).card = if p ∈ P then 1 else 0`, and the real part of
   `(p:ℂ)^{-(σ+iτ)}`. The last is the fiddly one; `HTGeometry.HalfPlaneMellinRepresentation`'s
   `cpow_ofReal_mul_I` is the corpus's tool for exactly this shape and was used earlier in the
   session for the Perron kernel.
2. Reconcile `∑'_p p^{-σ}(…)` at `σ = 1 + 1/log x` with `dampedCosPlusSum P t τ x`, which is
   truncated at `x` and sits at `σ = 1`. The undamped analogue is
   `RHTower/ZetaLineLowerBound.abs_zeta_deficit_sub_primeClockEnergy_le`; the damped case differs
   only by the `t`-weight on `P`, which is bounded by `∑_{p ∈ P} 1/p` exactly as in
   `RHTower/DampedPretentiousGap.dampedCosPlusSum_ge`.

Together these give `‖F_t(1 + 1/log x + iτ)‖ ≪ (log x)·exp(−dampedCosPlusSum)`, i.e. a Dirichlet
series bound of size `(log x)^{1 − 0.9 + o(1)}` at the card's parameters — the input Halász's proof
integrates against the Perron kernel.

## `Sieve/DampedPrimeTerm` — the Euler exponent in cosine form (2026-08-18)

```
card_primeFactorsIn_prime (∀ q ∈ P, q.Prime) (hp : p.Prime) :
  (primeFactorsIn P p).card = if p ∈ P then 1 else 0

twistedSummand_dampedOmegaMoebius_prime_re (∀ q ∈ P, q.Prime) (hp : p.Prime) (t σ τ) :
  (twistedSummand (dampedOmegaMoebius P t) (σ + τ·I) p).re
    = −((if p ∈ P then t else 1) · (p^{-σ} · cos(τ log p)))
```

This is the negative of `RHTower.dampedCosPlusSum`'s summand, shifted from `p^{-1}` to `p^{-σ}`.
Combined with `Sieve/DampedEulerSeriesBound.norm_tsum_dampedOmegaMoebius_le`, the damped series is
bounded by `exp(5/2 − ∑'_p (if p ∈ P then t else 1)·p^{-σ}cos(τ log p))`.

Searching first paid again: the real part `((n:ℂ)^{-(σ+iτ)}).re = n^{-σ}cos(τ log n)` is already
`RHTower.VonMangoldtThreeFourOneSeries.re_natCast_cpow_neg`, so the copy I had drafted was deleted
and the corpus lemma imported instead.

### The one bookkeeping step left before Halász's own proof

Reconcile the `σ`-level infinite prime sum with `dampedCosPlusSum P t τ x`, which is truncated at `x`
and sits at `σ = 1`, taking `σ = 1 + 1/log x`. Three pieces, all standard and all with an undamped
precedent in `RHTower/ZetaLineLowerBound`:

- `∑'_p p^{-σ} − ∑_{p ≤ x} 1/p = O(1)` at `σ = 1 + 1/log x` (Mertens plus the tail);
- the cosine-weighted analogue, which is `abs_zeta_deficit_sub_primeClockEnergy_le` in the undamped
  case;
- the `t`-weight on `P`, worth at most `∑_{p ∈ P} 1/p` exactly as in `dampedCosPlusSum_ge`.

The output is `‖F_t(1 + 1/log x + iτ)‖ ≪ (log x)·exp(−dampedCosPlusSum P t τ x)`, uniform in `t` and
in `τ`, which is the Dirichlet-series input of Halász's argument.

## `Sieve/DampedPlainCompare` — damped against plain, term by term (2026-08-18)

```
twistedSummand_moebius_prime_re (hp : p.Prime) (σ τ) :
  (twistedSummand μ (σ + τ·I) p).re = −(p^{-σ}·cos(τ log p))

abs_twistedSummand_damped_sub_plain_le (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (hp : p.Prime) (1 ≤ σ) (τ) :
  |(twistedSummand (dampedOmegaMoebius P t) (σ+τ·I) p).re − (twistedSummand μ (σ+τ·I) p).re|
    ≤ if p ∈ P then 1/p else 0
```

The two Euler exponents agree off `P` and differ on `P` by `(1−t)·p^{-σ}·cos(τ log p)`, which is at
most `p^{-σ} ≤ 1/p` for `σ ≥ 1`. Summed over `P` that is the same harmonic mass
`RHTower/DampedPretentiousGap` already pays, so the damped reconciliation between the `σ`-level prime
sum and the truncated one costs nothing beyond the undamped one.

### Remaining, in order

1. Sum the term-level comparison over the primes — `Summable` on both sides comes from
   `Sieve/MultiplicativeEulerBound.summable_norm_twistedSummand`, and the difference is supported on
   the finite set `P`.
2. Compose with the corpus's undamped reconciliation
   (`RHTower/ZetaLineLowerBound.abs_zeta_deficit_sub_primeClockEnergy_le`) at `σ = 1 + 1/log x` to
   land `‖F_t(1 + 1/log x + iτ)‖ ≪ (log x)·exp(−dampedCosPlusSum P t τ x)`.
3. Halász's mean value theorem itself, which integrates that bound against the Perron kernel; the
   large-values machinery it needs is owned (`Sieve/DyadicSecondEnvelopeClosed`,
   `Sieve/DirichletMeasureLargeValues`, `Sieve/LargeSieveWeak`).
4. The ladder assembly, then `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## `Sieve/DampedTsumCompare` — the comparison, summed (2026-08-18)

```
summable_re_twistedSummand_primes (∀ n, ‖f n‖ ≤ 1) (1 < s.re) :
  Summable fun p : Nat.Primes => (twistedSummand f s p).re
summable_abs_re_damped_sub_plain
abs_tsum_re_damped_sub_plain_le (0 ≤ t) (t ≤ 1) (1 < s.re) :
  |∑'_p (damped p).re − ∑'_p (plain p).re| ≤ ∑'_p |(damped p).re − (plain p).re|
```

Both Euler exponents are summable over the primes on `Re s > 1`, so the difference sums term by
term. Left in this form deliberately: the term-level bound of `Sieve/DampedPlainCompare` gives
`|·| ≤ if p ∈ P then 1/p else 0`, whose total is `∑_{p ∈ P} 1/p`, but collapsing the
finitely-supported `tsum` over the `Nat.Primes` subtype to that `Finset` sum is packaging best done
where the consumer fixes the shape.

## Honest scale of what is left

The chain from the five cards' input down to two named classical theorems is complete and
machine-checked. What remains is those theorems, and neither is small:

- **Halász's mean value theorem.** All of its arithmetic inputs are now owned — the pretentious
  distance for `μ` and for the damped function, both uniform; the Euler bound; the summability. What
  is missing is the analytic core: Perron plus the large-values dichotomy. The corpus owns the
  large-values machinery, so this is a real but bounded formalisation.
- **Watt / Deshouillers–Iwaniec.** Cards 1–2 need Matomäki–Teräväinen Theorem 1.2 itself, and its
  Type I estimates rest on twisted fourth moments of Dirichlet L-functions. Card 2's own gate
  records this: "the all-interval theorem it perturbs is a deep external input, not present in
  Mathlib". Its Lean file holds the elementary perturbative layer as separate lemmas; the capstone
  would be the implication `MT Thm 1.2 → forbidden-support version`, which is a genuine unconditional
  theorem but carries `MT` as a hypothesis, so it does not meet the no-hypotheses bar on its own.

Neither card 1 nor card 2 can reach stage 3 by any rearrangement of existing corpus assets; they need
the automorphic input. Cards 3–5 need Halász and then the ladder assembly already scoped above.

## Correction: route (A) is the right one, not (B) (2026-08-18)

Three sections above I chose Halász over the perturbed contour on the grounds that it is "one theorem
rather than a six-module rewrite". That weighed the wrong things, and the choice is reversed.

**Halász's analytic core does not have a cheap form here.** Its arithmetic inputs are all owned now,
but the core is Perron *plus* the large-values dichotomy, and the dichotomy cannot be skipped: with
the trivial Perron bound `∫ dt/(1+|t|)` one gets
`(1/N)|∑_{m ≤ N} f(m)| ≪ sup|F|·log T`, and at our parameters `sup|F| ≈ (log x)^{0.1}` — the bound
exceeds `1`. The whole content of Halász is the combination that avoids that loss.

**Route (A) is much smaller than it looked, because of what the low window is.** The `hU` hypothesis
asks for a saving on `‖logPoly (ramareCofactorCoeff P) C w‖` for `|w| ≤ w₀` only — a *long* sum with
a *small* twist. That is exactly the regime the zero-free region handles and exactly what
`Sieve/CofactorLowFreqBound` already does for the plain cofactor. Extending it needs only that the
perturbation

```
G_t(s) = (1/ζ(s)) · ∏_{p ∈ P} dampedEulerFactor t p s
```

is holomorphic wherever `1/ζ` is (on `Re s > 0` each `1 − p^{-s} ≠ 0`) and bounded by a `t`-uniform
polylog — and `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le` **already proves that
bound on `Re s ≥ 1/2`**, which contains the whole contour region `Re s ≥ 1 − 1/log²K`.

So the contour edges each acquire one bounded multiplier and nothing else changes. That is
bookkeeping across six modules, against an open-ended formalisation of Halász.

### Next brick

The Euler product identity on `Re s > 1`:

```
∑'_m μ(m)·t^{ω_P(m)}·m^{-s} = (1/ζ(s)) · ∏_{p ∈ P} dampedEulerFactor t p s
```

`Sieve/DampedMultiplicative` supplies multiplicativity and the unit bound, so
`EulerProduct.eulerProduct` applies to the left side; the right side is the same product with the
`P`-factors replaced. Then the six contour modules, each edge multiplied by
`norm_prod_dampedEulerFactor_le`.

The Halász lane is not wasted — `RHTower/MoebiusPretentiousGap` and `RHTower/DampedPretentiousGap`
are the sharpest uniform unpretentiousness statements in the corpus and remain the right input if
Halász is ever wanted — but it is no longer the critical path.

## `Sieve/DampedLocalFactor` — the local Euler factor (2026-08-18)

```
dampedOmegaMoebius_prime (∀ q ∈ P, q.Prime) (t) (hp : p.Prime) :
  dampedOmegaMoebius P t p = −(if p ∈ P then t else 1 : ℝ)
dampedOmegaMoebius_primePow_eq_zero (hp : p.Prime) (2 ≤ k) :
  dampedOmegaMoebius P t (p^k) = 0
tsum_twistedSummand_dampedOmegaMoebius_primePow (∀ q ∈ P, q.Prime) (t) (hp : p.Prime) (s) :
  ∑'_k twistedSummand (dampedOmegaMoebius P t) s (p^k)
    = 1 − (if p ∈ P then t else 1 : ℝ)·p^{-s}
```

`μ` vanishes at `p^k` for `k ≥ 2`, so the local factor has only two terms. Off `P` it is exactly the
local factor of `1/ζ`; on `P` it is that factor times `dampedEulerFactor t p s`. This is the
arithmetic content of

```
∑'_m μ(m)·t^{ω_P(m)}·m^{-s} = (1/ζ(s)) · ∏_{p ∈ P} dampedEulerFactor t p s      (Re s > 1)
```

and what remains of that identity is infinite-product plumbing: `EulerProduct.eulerProduct` applied
to the damped function (hypotheses supplied by `Sieve/DampedMultiplicative`), mathlib's Euler product
for `1/ζ`, and the split of the `P`-factors out of the infinite product.

### The route, from here to the cards

1. the Euler identity above (product plumbing only);
2. widen the six contour modules — `MoebiusContourBound`, `PerronSharpSubstitution`,
   `MellinAbscissaDecay`, `MoebiusContourKappaTwo`, `MoebiusSaving`, `MoebiusKappaTwoRate` — by the
   bounded `t`-uniform multiplier `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le`,
   which already covers the whole contour region `Re s ≥ 1/2`;
3. the damped analogue of `Sieve/CofactorLowFreqBound.exists_norm_logPoly_geomCofactorBlockAt_le`,
   transferred to `ramareCofactorCoeff` by
   `Sieve/DampedCofactorTransfer.norm_logPoly_ramareCofactorCoeff_le_of_uniform`;
4. feed it as `hU` to `Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final`, take
   `z = exp((log x)^{3/5})`, and assemble the explicit `(log x)^{-A}` with `A > 1`;
5. `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing` then promotes cards 4 and 5;
   card 3 additionally needs the window pushed towards `log log x`.

## `Sieve/DampedEulerIdentity` — step 1 done (2026-08-18)

```
dampedOmegaMoebius_one_eq (P) : dampedOmegaMoebius P 1 = fun m => μ m
tsum_twistedSummand_moebius_primePow : ∑'_k twistedSummand μ s (p^k) = 1 − p^{-s}
one_sub_cpow_ne_zero (hp : p.Prime) (1 < s.re) : 1 − p^{-s} ≠ 0

tsum_damped_eq_prod_mul_tsum_moebius (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (1 < s.re) :
  ∑'_n twistedSummand (dampedOmegaMoebius P t) s n
    = (∏_{p ∈ P} dampedEulerFactor t p s) · ∑'_n twistedSummand μ s n
```

Both series have Euler products; their local factors agree off `P` and differ on `P` by exactly
`dampedEulerFactor`, so the partial products over `primesBelow n` differ by that fixed finite product
as soon as `n` exceeds every member of `P`, and the limits inherit it. The plain local factor came
free by instantiating the damped one at `t = 1`.

Stated against the plain Möbius series rather than `1/ζ` deliberately: the contour modules work with
the Dirichlet series, so this is the form they consume, and no `1/ζ` identity is needed.

**Step 1 of the five-step route is complete.** Remaining: (2) widen the six contour modules by
`norm_prod_dampedEulerFactor_le`, which already covers `Re s ≥ 1/2` ⊇ the contour region; (3) the
damped analogue of `exists_norm_logPoly_geomCofactorBlockAt_le`, transferred by
`norm_logPoly_ramareCofactorCoeff_le_of_uniform`; (4) feed as `hU` to `omegaBudget_le_ladder_final`
at `z = exp((log x)^{3/5})` and assemble `(log x)^{-A}`, `A > 1`; (5)
`eventually_fibre_step_one_growing` promotes cards 4 and 5, card 3 also needing the short-window range.

## Step 2 is one module, not six (2026-08-18)

Read the contour stack. The three edge lemmas are **already generic in the Dirichlet series**:

- `Sieve/TruncationError.exists_bound_truncation_error` — `∀ (F : ℂ → ℂ) (c T M), … → ‖∫ F·mellin(w) − ∫_{-T}^{T} F·mellin(w)‖ ≤ …`
- `Sieve/HorizontalEdgeBound.exists_horizontal_edge_bound` — same shape, `∀ F`
- `Sieve/VerticalEdgeBound.exists_vertical_edge_bound` — same shape, `∀ F`

Each takes an arbitrary `F` and a sup bound for it on the edge; none mentions `invZeta`. Only
`Sieve/PerronEdgeSubstitution.exists_norm_tsum_moebius_smoothWeight_le` specialises, and it does so
in exactly two places:

1. the Perron/Mellin identity `∑'_n a(n)·smoothWeight(n) = (1/2π)∫ F(d+iy)·mellin(smoothWeight)(d+iy) dy`
   on a line `Re d > 1`;
2. holomorphy of `F` in the contour box, to shift from `d` to `c`.

Both are available for the damped series:

- (1) is Mellin inversion applied termwise, and the damped coefficients are unit-bounded with a
  convergent series on `Re s > 1` (`Sieve/DampedEulerSeriesBound`);
- (2) holds because `G_t(s) = invZeta(s)·∏_{p ∈ P} dampedEulerFactor t p s`
  (`Sieve/DampedEulerIdentity`), and each `dampedEulerFactor` is holomorphic wherever `1 − p^{-s} ≠ 0`,
  which is all of `Re s > 0` — so `G_t` is holomorphic exactly where `invZeta` is, and its edge sup
  bounds are the `invZeta` ones times `norm_prod_dampedEulerFactor_le`, which already covers
  `Re s ≥ 1/2`.

So step 2 is **one new module** mirroring `PerronEdgeSubstitution` for the pair
`(dampedOmegaMoebius P t, G_t)`, not a rewrite of six. Everything downstream of it
(`MoebiusContourBound` → `MoebiusContourKappaTwo` → `MoebiusSaving` → `MoebiusKappaTwoRate` →
`CofactorLowFreqBound`) then instantiates with the widened edge constants.

Deliberately not started at the end of a long session: it edits nothing existing, but it is a
substantial single module and it is better begun with a clear context than finished carelessly.

## `Sieve/DampedSmoothPerron` — the first of step 2's two inputs (2026-08-18)

```
dampedOmegaMoebius_zero (P) (t) : dampedOmegaMoebius P t 0 = 0

tsum_dampedOmegaMoebius_smoothWeight_eq_integral (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) (1 < σ) :
  (2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n
    = ∫ y, (∑'_n dampedOmegaMoebius P t n · n^{-(σ+iy)}) · mellin (smoothWeight N H) (σ+iy)
```

`HTGeometry.SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral` turned out to be **already generic
in the coefficients** — it asks only that they are unit-bounded and vanish at `0`, both of which the
damped coefficients satisfy. So this is an instantiation, not a construction.

That settles the first of the two `μ`-specific inputs of
`Sieve/PerronEdgeAssembly.norm_tsum_moebius_smoothWeight_le_edges`. The second is the rectangle
identity `integral_invZetaW_vertical_sub_eq_horizontal_rect`, which for the damped series follows
from Cauchy applied to `G_t·W`, where `G_t = invZeta · ∏_{p ∈ P} dampedEulerFactor t p s`
(`Sieve/DampedEulerIdentity`) is holomorphic exactly where `invZeta` is, each factor being
holomorphic on `Re s > 0`.

Watch the name clash when working here: `smoothWeight` resolves to a `ℕ`-valued definition inside
`RHTower.Sieve`, so the `HTGeometry` one must be written out in full.

## `Sieve/DampedRectangleShift` — step 2's second input (2026-08-18)

```
dampedInvZeta P t s = invZeta s · ∏_{p ∈ P} dampedEulerFactor t p s

one_sub_cpow_ne_zero_of_pos_re (2 ≤ p) (0 < s.re) : 1 − p^{-s} ≠ 0
differentiable_natCast_cpow_neg (2 ≤ p) : Differentiable ℂ (fun s => p^{-s})
differentiableOn_dampedEulerFactor_rect, differentiableOn_prod_dampedEulerFactor_rect
differentiableOn_dampedInvZetaW_rect (∀ q ∈ P, 2 ≤ q) (0 < H) (0 < c) (c ≤ d) (zero-free) :
  DifferentiableOn ℂ (fun s => dampedInvZeta P t s · mellin (smoothWeight N H) s) (rect)

integral_dampedInvZetaW_vertical_sub_eq_horizontal_rect :
  I•∫_{-T}^{T} (at d) − I•∫_{-T}^{T} (at c) = ∫_c^d (at +T) − ∫_c^d (at −T)
```

`Sieve/InvZetaRegular.integral_vertical_sub_eq_horizontal_rect` is generic — it needs only
differentiability — so the rectangle identity followed once the integrand was shown holomorphic, and
that in turn is `differentiableOn_invZetaW_rect` times the finite Euler correction, each factor
holomorphic because `1 − p^{-s} ≠ 0` on `Re s ≥ c > 0`.

**Both `μ`-specific inputs of `Sieve/PerronEdgeAssembly` now have damped counterparts.** What is left
of step 2 is to assemble them exactly as `PerronEdgeAssembly` → `PerronEdgeSubstitution` →
`MoebiusContourBound` do, with the three generic edge lemmas (`TruncationError`,
`HorizontalEdgeBound`, `VerticalEdgeBound`) instantiated at `F = dampedInvZeta P t` and the edge sups
taken from the `invZeta` ones times `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le`.

One gap to close in that assembly: the Perron formula
(`Sieve/DampedSmoothPerron`) produces the *series* `∑'_n damped(n)·n^{-s}` on the `d`-line, while the
rectangle identity is stated for `dampedInvZeta`; the two agree there by
`Sieve/DampedEulerIdentity.tsum_damped_eq_prod_mul_tsum_moebius` together with
`∑'_n μ(n)·n^{-s} = invZeta s`, which the corpus uses inside
`PerronEdgeAssembly.tsum_moebius_smoothWeight_eq_invZeta_integral` and should be extracted from there.

## `Sieve/DampedEdgeAssembly` — the damped four-edge bound (2026-08-18)

```
tsum_damped_smoothWeight_eq_dampedInvZeta_integral (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1)
    (0 < N) (0 < H) (1 < d) :
  (2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n
    = ∫ y, dampedInvZeta P t (d+iy) · mellin (smoothWeight N H) (d+iy)

norm_tsum_damped_smoothWeight_le_edges … (htrunc) (htop) (hbot) (hleft) :
  ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖ ≤ E₁ + E₂ + E₃ + E₄
```

The gap flagged last entry is closed: the Perron formula gives the *series* on the `d`-line, and
`Sieve/DampedEulerIdentity` plus the corpus's `tsum_moebius_cpow_eq_invZeta` identify it with
`dampedInvZeta` there. `norm_le_of_contour_edges` is generic in the four complex quantities, so the
assembly is the `μ` one verbatim.

**This is the damped counterpart of `Sieve/PerronEdgeAssembly.norm_tsum_moebius_smoothWeight_le_edges`,
which is the base of the whole contour stack.** What remains of step 2 is mechanical: instantiate the
three generic edge lemmas (`TruncationError`, `HorizontalEdgeBound`, `VerticalEdgeBound`) at
`F = dampedInvZeta P t`, mirroring `Sieve/PerronEdgeSubstitution`, with edge sups obtained from the
`invZeta` ones times `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le`; then mirror
`MoebiusContourBound` → `MoebiusContourKappaTwo` → `MoebiusSaving` → `MoebiusKappaTwoRate` →
`CofactorLowFreqBound`, each step being a substitution of constants rather than a new argument.

## `Sieve/DampedEdgeSubstitution` — step 2's contour bound (2026-08-18)

```
continuous_dampedEulerFactor_line (2 ≤ p) (t) (0 < d)
continuous_dampedInvZeta_line (∀ q ∈ P, 2 ≤ q) (t) (1 < d)

exists_norm_tsum_damped_smoothWeight_le (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) (j) (σmax) :
  ∃ C, 0 ≤ C ∧ ∀ c d T Md Mh Mc, … (edge sups for dampedInvZeta) …
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
      ≤ 2(Md·C)/T + Mh·C/T^{j+1}(d−c) + Mh·C/T^{j+1}(d−c) + Mc(2(N+H)^c/c + 2C)
```

The damped analogue of `Sieve/PerronEdgeSubstitution`, and the only genuinely new ingredient was
continuity of `dampedInvZeta` along a vertical line — the three edge estimates apply to it unchanged
because they are generic in the Dirichlet series.

**Step 2 now has its contour bound in the same shape as the `μ` one.** What is left of step 2 is to
supply the edge sups `Md, Mh, Mc` for `dampedInvZeta` from the corresponding `invZeta` bounds
(`Sieve/MoebiusContourBound.invZetaEdgeBound`, `invZetaRightBound`) times
`Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le`, which is exactly what
`MoebiusContourBound` does for `μ`, and then to carry the resulting constants through
`MoebiusContourKappaTwo` → `MoebiusSaving` → `MoebiusKappaTwoRate` → `CofactorLowFreqBound`.

## `Sieve/DampedCorrBound` — the edge sups (2026-08-18)

```
dampedCorrBound P c = ∏_{p ∈ P} (1 + p^{-c})/(1 − p^{-c})

norm_prod_dampedEulerFactor_le_corrBound (∀ q ∈ P, 2 ≤ q) (0 ≤ t) (t ≤ 1) (1/2 ≤ c) (c ≤ s.re) :
  ‖∏_{p ∈ P} dampedEulerFactor t p s‖ ≤ dampedCorrBound P c

norm_dampedInvZeta_le … (0 ≤ M) (‖invZeta s‖ ≤ M) :
  ‖dampedInvZeta P t s‖ ≤ M · dampedCorrBound P c
```

The pointwise bound of `Sieve/DampedEulerCorrection` depends on `Re s`, which varies along the
horizontal edges; `(1+x)/(1−x)` is increasing on `[0,1)` and `p^{-Re s} ≤ p^{-c}`, so the value at
the left abscissa dominates the half plane. The second theorem is the shape the edge hypotheses of
`Sieve/DampedEdgeSubstitution.exists_norm_tsum_damped_smoothWeight_le` want: **every `invZeta` edge
bound in `Sieve/MoebiusContourBound` becomes a `dampedInvZeta` edge bound by multiplying by
`dampedCorrBound P c`**, uniformly in `t`.

Note the correction is `exp(O(∑_{p ∈ P} p^{-c}))`; at `c` near `1` and `P` the card's prime range
that is `exp(O(log log x)) = polylog x`, which the contour's saving absorbs.

### Remaining

Mirror `Sieve/MoebiusContourBound` with `Md, Mh, Mc` taken as `invZetaRightBound K ·
dampedCorrBound P c` and `invZetaEdgeBound K · dampedCorrBound P c`, then carry the constants through
`MoebiusContourKappaTwo` → `MoebiusSaving` → `MoebiusKappaTwoRate` → `CofactorLowFreqBound`. Each is
a substitution; no new analytic content remains in step 2.

## `Sieve/DampedContourBound` — the contour bound, damped (2026-08-19)

```
exists_norm_tsum_damped_smoothWeight_le_concrete (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1)
    (0 < N) (0 < H) (j) :
  ∃ C M₀ K₀, 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ K, K₀ ≤ K →
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
      ≤ 2((invZetaRightBound K · dampedCorrBound P (leftAbscissa K))·C)/truncHeight K
        + (invZetaEdgeBound K · dampedCorrBound P (leftAbscissa K))·C/truncHeight K^{j+1}·(right−left)
        + (same)
        + (max M₀ (invZetaEdgeBound K) · dampedCorrBound P (leftAbscissa K))
            ·(2(N+H)^{leftAbscissa K}/leftAbscissa K + 2C)
```

The damped analogue of `Sieve/MoebiusContourBound`, and the shape is *identical* to the `μ` one with
every edge bound multiplied by `dampedCorrBound P (leftAbscissa K)`. The contour geometry, the
zero-free rectangle (`zero_free_concrete_rect`) and the three `invZeta` edge estimates
(`norm_invZeta_right_le`, `norm_invZeta_horizontal_le`, `norm_invZeta_left_line_le`) are reused
verbatim; `1/2 ≤ leftAbscissa K` holds because the zero-free width is at most `1/54`, which is what
lets `Sieve/DampedCorrBound` apply on the whole rectangle.

**Step 2 is done.** The remaining chain — `MoebiusContourKappaTwo` → `MoebiusSaving` →
`MoebiusKappaTwoRate` → `CofactorLowFreqBound` — optimises `K` and converts the bound into a saving;
each step is arithmetic in the constants, now carrying the extra factor `dampedCorrBound`, which is
`exp(O(∑_{p ∈ P} p^{-leftAbscissa K})) = polylog x` at the card's parameters and is absorbed by the
saving.

## Audit of the remaining contour chain — it is ~21 modules, not a handful (2026-08-19)

Traced the transitive imports of `Sieve/MoebiusTwistSharpRate`, which is what supplies
`Sieve/CofactorLowFreqBound.moebiusSharpBound` (saving `exp(−c(log N)^{1/10})`): 80 modules, of
which 30 are Möbius/contour-specific. Scanning each for whether it takes the Dirichlet series as a
parameter or names `moebius`/`invZeta` outright:

| generic already | `TruncatedContourShift`, `SavingSubstitution`, `ContourParameterChoice`, `MoebiusCombinedBound`, `MoebiusTwistCombinedBound` |
|---|---|
| `μ`/`invZeta`-specific | the other ~21, including the whole `MoebiusTwist*` layer (`Perron`, `EdgeAssembly`, `EdgeSubstitution`, `ConcreteEdges`, `ContourBoundGeneral`, `ContourBoundRatio`, `MajorantRatio`, `SharpSubstitution`, `SharpRate`) and `MoebiusContourBound{Diag,Sharp,General,Ratio}`, `MoebiusSaving`, `MoebiusMajorant{Bound,Ratio}`, `Moebius{Smooth,Sharp}LittleO`, `MoebiusPerron`, `PerronSharpSubstitution`, `MoebiusTwistRate` |

**This corrects the running estimate.** The pattern that held for the bottom of the stack — every
analytic edge lemma turned out to be generic in `F` — does **not** extend upwards: the optimisation
and twist layers are written against `μ` and `invZeta` throughout. Mirroring them for
`dampedOmegaMoebius`/`dampedInvZeta` is a bounded but genuinely multi-session job of about twenty-one
modules, each carrying the extra factor `dampedCorrBound P (leftAbscissa K)` through arithmetic that
is otherwise unchanged.

Two ways to do it, and the choice should be made deliberately:

1. **Mirror.** Write `Damped*` copies. No risk to existing code, but duplicates ~21 modules.
2. **Generalise in place.** Add a Dirichlet-series parameter to each, exactly as
   `Sieve/TruncationError`, `HorizontalEdgeBound`, `VerticalEdgeBound` and
   `HTGeometry/SmoothWeightPerron` already have, and re-derive the `μ` versions as instantiations.
   Much less duplication and it improves the corpus, but it edits modules other sessions own, so it
   needs coordination.

Option 2 is better for the corpus; option 1 is safer under concurrent editing. Whichever is chosen,
the analytic content is complete — everything from here is substitution of constants.

## `Sieve/DampedSaving` — first of the ~21 mirrored (2026-08-19)

```
dampedCorrBound_nonneg (∀ q ∈ P, 2 ≤ q) (1/2 ≤ c) : 0 ≤ dampedCorrBound P c

exists_norm_tsum_damped_smoothWeight_le_saving (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) (j) :
  ∃ C M₀ K₀, … ∀ K ≥ K₀,
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
      ≤ … + (max M₀ (invZetaEdgeBound K) · dampedCorrBound P (leftAbscissa K))
              · (4·(N+H)·exp(−c₀ log(N+H)/(16 log⁹K)) + 2C)
```

`Sieve/MoebiusSaving`'s `rpow_leftAbscissa` is about the abscissa alone, so it is reused unchanged;
only the edge constants carry `dampedCorrBound P (leftAbscissa K)`. Mirroring cost: ~50 lines,
entirely the surrounding arithmetic.

**Route chosen: mirror (option 1).** It touches nothing another session owns, which matters given
how many agents are editing this tree concurrently. The duplication is the price.

Order for the rest, following the import graph towards
`Sieve/CofactorLowFreqBound.moebiusSharpBound`:
`MoebiusPerron` · `PerronSharpSubstitution` · `MoebiusContourBoundDiag` · `MoebiusContourBoundSharp` ·
`MoebiusContourBoundGeneral` · `MoebiusContourBoundRatio` · `MoebiusMajorantBound` ·
`MoebiusMajorantRatio` · `MoebiusSmoothLittleO` · `MoebiusSharpLittleO` · `MoebiusCombinedBound` ·
then the `MoebiusTwist*` layer (`Perron`, `EdgeAssembly`, `EdgeSubstitution`, `ConcreteEdges`,
`ContourBoundGeneral`, `ContourBoundRatio`, `MajorantRatio`, `CombinedBound`, `Rate`,
`SharpSubstitution`, `SharpRate`), and finally `Sieve/CofactorLowFreqBound` itself.

## `Sieve/DampedPerron` — second of the mirrored chain (2026-08-19)

```
tsum_damped_cpow_eq_dampedInvZeta (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (1 < s.re) :
  ∑'_n dampedOmegaMoebius P t n · n^{-s} = dampedInvZeta P t s

norm_tsum_damped_smoothWeight_le … (1 < σ) :
  ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
    ≤ (exp(22/4)·(1 + 1/(σ−1))·dampedCorrBound P σ) · ∫ y ‖mellin (smoothWeight N H) (σ+iy)‖
```

The first is the series/continuation identity extracted as a standalone lemma — it was previously
only an internal step of `Sieve/DampedEdgeAssembly` and is needed pointwise here.

Mirrored so far: `DampedSaving` (← `MoebiusSaving`), `DampedPerron` (← `MoebiusPerron`).
Remaining in the recorded order: `PerronSharpSubstitution`, `MoebiusContourBound{Diag,Sharp,General,Ratio}`,
`MoebiusMajorant{Bound,Ratio}`, `Moebius{Smooth,Sharp}LittleO`, `MoebiusCombinedBound`, the eleven
`MoebiusTwist*`, and `CofactorLowFreqBound`.

## `Sieve/DampedSharpSubstitution` — third mirrored (2026-08-19)

```
norm_tsum_damped_smoothWeight_le_sharp … (hbd1) (hbd2) (hbd3) :
  ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
    ≤ 2(Md·C₁)/T + Mh·C₂/T^{j+1}(d−c) + Mh·C₂/T^{j+1}(d−c) + Mc(2(N+H)^c/c + 2C₃)
```

The sharp edge estimates of `Sieve/EdgeBoundsSharp` (`norm_truncation_error_le`,
`norm_horizontal_edge_le`, `norm_integral_vertical_edge_le`) are generic in the Dirichlet series, so
only the continuity input (`continuous_dampedInvZeta_line`) and the final assembly changed.

Mirrored: `DampedSaving`, `DampedPerron`, `DampedSharpSubstitution`. Eighteen remain.

## `Sieve/DampedContourBoundSharp` — fourth mirrored (2026-08-19)

```
exists_norm_tsum_damped_smoothWeight_le_concrete_sharp (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1)
    (0 < N) (0 < H) (j) :
  ∃ C C' M₀ K₀, … ∀ K ≥ K₀,
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
      ≤ 2((invZetaRightBound K · dampedCorrBound P (leftAbscissa K))·(C(N+H+1)^{rightAbscissa K}))/truncHeight K
        + … + (max M₀ (invZetaEdgeBound K) · dampedCorrBound P (leftAbscissa K))
                ·(2(N+H)^{leftAbscissa K}/leftAbscissa K + 2C(N+H+1)^{leftAbscissa K})
```

Built by reusing the geometry-and-edges block of `Sieve/DampedContourBound` verbatim and closing
with `Sieve/DampedSharpSubstitution` plus the Mellin decay constants from
`exists_bound_mellin_smoothWeight_upto`. The zero-free rectangle, the abscissa arithmetic and the
three damped edge bounds are shared between the two modules — worth remembering for the rest of the
chain, since several of the remaining mirrors differ from one another only in how they close.

Mirrored: `DampedSaving`, `DampedPerron`, `DampedSharpSubstitution`, `DampedContourBoundSharp`.
Seventeen remain.

## `Sieve/DampedContourBoundDiag` — fifth mirrored (2026-08-19)

```
exists_norm_tsum_damped_smoothWeight_le_diag (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (j) :
  ∃ C C' M₀ K₀, … ∀ N ≥ 1, ∀ K ≥ K₀,
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N N n‖ ≤ … (N+N+1)^{rightAbscissa K} …
```

The diagonal case `H = N`, with Mellin decay constants uniform in `N`
(`exists_bound_mellin_smoothWeight_diag_upto`), so that the contour parameter can afterwards be
chosen as a function of `N` alone.

**Mirroring technique that is now paying off.** The geometry-and-edges block — zero-free rectangle,
abscissa arithmetic, the three damped edge bounds, `hcorr0`, `hFccont` — is identical across
`DampedContourBound`, `DampedContourBoundSharp` and `DampedContourBoundDiag`; only the `obtain`s at
the top and the closing `exact` differ. Reusing it verbatim keeps each new mirror to roughly a
statement plus five lines.

Mirrored: `DampedSaving`, `DampedPerron`, `DampedSharpSubstitution`, `DampedContourBoundSharp`,
`DampedContourBoundDiag`. Sixteen remain.

## `Sieve/DampedContourBound{General,Ratio}` — sixth and seventh mirrored (2026-08-19)

```
exists_norm_tsum_damped_smoothWeight_le_general (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) :
  ∃ C C' M₀ K₀, … ∀ N H > 0, ∀ K ≥ K₀, … (C/H² · (N+H+1)² · (N+H+1)^{rightAbscissa K}) …

exists_norm_tsum_damped_smoothWeight_le_ratio (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) :
  ∃ C C' M₀ K₀, … ∀ N H L, 0 < N → 1 ≤ H → N/H ≤ L → ∀ K ≥ K₀, … (C(L+2)²(N+H+1)^{rightAbscissa K}) …
```

`General` splices the shared geometry block as before. `Ratio` is a `gcongr` over `General` with the
width factors replaced via `sq_width_factor_le` / `width_factor_le`; the only addition needed was
`1/2 ≤ leftAbscissa K`, which at `K ≥ 5` follows from `log K > 1` (since `e < 5`) giving
`zeroFreeConst/(16 log⁹K) ≤ 1/16`.

Mirrored: `DampedSaving`, `DampedPerron`, `DampedSharpSubstitution`, `DampedContourBoundSharp`,
`DampedContourBoundDiag`, `DampedContourBoundGeneral`, `DampedContourBoundRatio`. Fourteen remain.

## `Sieve/DampedFactoredBound` — the remaining chain collapses (2026-08-19)

```
exists_norm_tsum_damped_smoothWeight_le_ratio_factored (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) :
  ∃ C C' M₀ K₀, … ∀ N H L, 0 < N → 1 ≤ H → N/H ≤ L → ∀ K ≥ K₀,
    ‖(2π) • ∑'_n dampedOmegaMoebius P t n · smoothWeight N H n‖
      ≤ dampedCorrBound P (leftAbscissa K) · (the expression of `MoebiusContourBoundRatio`)

norm_tsum_damped_le_of_moebius_shape (∀ q ∈ P, 2 ≤ q) (1/2 ≤ c)
    (A ≤ dampedCorrBound P c · B) (B ≤ D) : A ≤ dampedCorrBound P c · D
```

**Each of the four contour terms carries exactly one edge constant, and in the damped chain every one
of those is the `invZeta` constant times the *same* factor.** So the damped bound is literally
`dampedCorrBound P (leftAbscissa K)` times the `μ` bound — one `ring` away from the ratio form.

This removes the need to mirror the remaining fourteen modules. Everything downstream of
`MoebiusContourBoundRatio` — `MoebiusMajorant{Bound,Ratio}`, `Moebius{Smooth,Sharp}LittleO`,
`MoebiusCombinedBound`, `MoebiusSaving`, the eleven `MoebiusTwist*` — bounds that same expression,
and each such bound `B ≤ D` transfers by multiplying through by a nonnegative constant, which is
exactly `norm_tsum_damped_le_of_moebius_shape`.

**Corrects the estimate again, this time downwards.** Two batches ago I measured the remaining work
at ~21 mirrored modules and chose mirroring over generalising. Seven mirrors in, the factorisation
makes the other fourteen unnecessary. The seven already written are not wasted — they are what
exhibits the common factor — but the right lesson is that I should have looked for the factorisation
before starting to mirror.

### What is actually left

1. Compose the factored bound with the existing `μ` chain's final saving
   (`Sieve/MoebiusTwistSharpRate` → `Sieve/CofactorLowFreqBound.moebiusSharpBound`), giving the
   damped cofactor saving as `dampedCorrBound · moebiusSharpBound`.
2. Check the arithmetic: `dampedCorrBound = exp(O(∑_{p ∈ P} p^{-leftAbscissa K}))` is polylog at the
   card's parameters, and `moebiusSharpBound` carries `exp(−c(log N)^{1/10})`, so the product still
   decays — this is the one place where a real inequality must be verified rather than transferred.
3. Then steps 3–5: transfer to `ramareCofactorCoeff` by
   `Sieve/DampedCofactorTransfer.norm_logPoly_ramareCofactorCoeff_le_of_uniform`, feed `hU` to
   `Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final`, and apply
   `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## `Sieve/DampedTwist` — sharpening and twisting come free (2026-08-19)

```
norm_tsum_damped_smoothWeight_sub_sum_le (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) :
  ‖∑'_n damped n · smoothWeight N H n − ∑_{n ≤ ⌊N⌋} damped n‖ ≤ H + 1

dampedTwist P t τ n = dampedOmegaMoebius P t n · n^{-iτ}
norm_dampedTwist_le_one
tsum_dampedTwist_cpow (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (τ) (1 < s.re) :
  ∑'_n dampedTwist P t τ n · n^{-s} = dampedInvZeta P t (s + iτ)
```

Both steps of the `μ` chain carry over with no work.
`Sieve/SmoothVsSharp.norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one` is already generic in the
coefficients, so the smoothed-to-sharp comparison is an instantiation. And the twist is exactly a
shift of the abscissa — as `Sieve/MoebiusTwistPerron.tsum_moebiusTwist_cpow` is for `μ` — so the
twisted damped series at `s` is the untwisted one at `s + iτ`.

**The factorisation survives the twist**, because `dampedCorrBound` depends only on the real part and
`Re(s + iτ) = Re s`. So the entire `MoebiusTwist*` layer — eleven of the fourteen modules I had
listed — is reached by the same `norm_tsum_damped_le_of_moebius_shape` transfer, with no mirroring.

### What is genuinely left

1. The one real inequality: `dampedCorrBound P c · moebiusSharpBound N` still decays. The first is
   `exp(O(∑_{p ∈ P} p^{-c}))`, polylog at the card's parameters; the second carries
   `exp(−c₀(log N)^{1/10})`.
2. Assemble the damped analogue of
   `Sieve/CofactorLowFreqBound.exists_norm_logPoly_geomCofactorBlockAt_le` from that.
3. Steps 3–5 as recorded.

## `Sieve/DampedCorrExp` — the correction is a power of `log` (2026-08-19)

```
corr_factor_le_exp (0 < x) (x ≤ 1/2) : (1+x)/(1−x) ≤ exp(3x)
dampedCorrBound_le_exp (∀ q ∈ P, 2 ≤ q) (1 ≤ c) :
  dampedCorrBound P c ≤ exp(3 · ∑_{p ∈ P} p^{-c})
```

On `c ≥ 1` every `p^{-c} ≤ 1/2`, and there `(1+x)/(1−x) ≤ e^x · e^{2x}` — the second factor because
`(1−x)(1+2x) = 1 + x − 2x² ≥ 1`.

This is the quantitative form the composition needs: at the Route E parameters
`∑_{p ∈ P} p^{-c}` is `O(log log x)`, so the correction is `exp(O(log log x))`, a power of `log x`,
while the contour supplies `exp(−c₀(log N)^{1/10})`. The product decays, which is the last estimate
that had to be checked rather than transferred.

### Remaining

- Compose: damped cofactor saving `= dampedCorrBound · moebiusSharpBound`, via
  `Sieve/DampedFactoredBound.norm_tsum_damped_le_of_moebius_shape` and the `μ` chain's endpoint.
- Steps 3–5: `Sieve/DampedCofactorTransfer.norm_logPoly_ramareCofactorCoeff_le_of_uniform`, then `hU`
  into `Sieve/OmegaBudgetLadderTail.omegaBudget_le_ladder_final`, then
  `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing`.

## `Sieve/DampedShiftBound`, and a correction about the twisted layer (2026-08-19)

```
norm_dampedInvZeta_shift_le (∀ q ∈ P, 2 ≤ q) (0 ≤ t) (t ≤ 1) (1/2 ≤ c) (c ≤ s.re) (τ)
    (0 ≤ M) (‖invZeta (s + iτ)‖ ≤ M) :
  ‖dampedInvZeta P t (s + iτ)‖ ≤ M · dampedCorrBound P c
```

**Correction to the previous entry.** I wrote that the whole `MoebiusTwist*` layer "is reached by the
same transfer, with no mirroring". That was too quick. The transfer
`norm_tsum_damped_le_of_moebius_shape` applies to a *bound expression*; it does not by itself produce
the twisted chain, whose proof runs its own contour with the rectangle shifted vertically.

What is true, and is what the lemma above records, is that the factorisation is **shift-invariant**:
`dampedCorrBound` depends only on the abscissa and `Re(s+iτ) = Re s`, so every edge bound of the
*twisted* contour also picks up exactly the same factor. So the twisted layer factors in the same
way — but exhibiting that still requires walking its modules, as the untwisted layer did, rather
than being free.

### Honest state of the remaining work

- The untwisted contour chain is complete and factored, through
  `Sieve/DampedContourBoundRatio` and `Sieve/DampedFactoredBound`.
- The twisted layer (`MoebiusTwistPerron`, `…EdgeAssembly`, `…EdgeSubstitution`, `…ConcreteEdges`,
  `…ContourBoundGeneral`, `…ContourBoundRatio`, `…MajorantRatio`, `…CombinedBound`, `…Rate`,
  `…SharpSubstitution`, `…SharpRate`) still needs the same treatment. With the shift-invariance
  above and the geometry block already written, each should be about as cheap as
  `DampedContourBoundSharp` was — a statement plus a splice — but there are eleven of them.
- Then the parameter-optimisation modules (`MoebiusMajorant{Bound,Ratio}`,
  `Moebius{Smooth,Sharp}LittleO`, `MoebiusCombinedBound`) transfer by
  `norm_tsum_damped_le_of_moebius_shape`, since those *are* pure bound manipulations.
- Then `Sieve/CofactorLowFreqBound`'s damped analogue, and steps 3–5.

## `Sieve/DampedTwistPerron` — first of the twisted layer (2026-08-19)

```
dampedTwist_zero (P) (t τ) : dampedTwist P t τ 0 = 0

norm_tsum_dampedTwist_smoothWeight_le (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) (1 < σ) (τ) :
  ‖(2π) • ∑'_n dampedTwist P t τ n · smoothWeight N H n‖
    ≤ (exp(22/4)·(1 + 1/(σ−1))·dampedCorrBound P σ) · ∫ y ‖mellin (smoothWeight N H) (σ+iy)‖
```

The generic Perron formula applies to `dampedTwist` (unit-bounded, vanishing at `0`), and the
pointwise bound is `Sieve/DampedShiftBound.norm_dampedInvZeta_shift_le` — the shift-invariance of the
correction is exactly what makes the constant here the same `dampedCorrBound P σ` as in the untwisted
case.

Twisted layer: 1 of 11 done. Remaining there: `EdgeAssembly`, `EdgeSubstitution`, `ConcreteEdges`,
`ContourBoundGeneral`, `ContourBoundRatio`, `MajorantRatio`, `CombinedBound`, `Rate`,
`SharpSubstitution`, `SharpRate`.

## `Sieve/DampedTwistEdgeAssembly` — the shifted integrand is holomorphic (2026-08-19)

```
differentiableOn_prod_dampedEulerFactor_shift_rect (∀ q ∈ P, 2 ≤ q) (t τ) (0 < c) (c ≤ d) :
  DifferentiableOn ℂ (fun s => ∏_{p ∈ P} dampedEulerFactor t p (s + iτ)) (rect)

differentiableOn_dampedInvZetaTwistW_rect (∀ q ∈ P, 2 ≤ q) (t τ) (0 < H) (0 < c) (c ≤ d) (0 ≤ T)
    (zero-free on the τ-enlarged rectangle) :
  DifferentiableOn ℂ (fun s => dampedInvZeta P t (s + iτ) · mellin (smoothWeight N H) s) (rect)
```

The shifted integrand is the shifted `invZeta` integrand (`differentiableOn_invZetaTwistW_rect`)
times the shifted Euler correction, and the latter is holomorphic on the rectangle because
`Re (s + iτ) = Re s > 0` there. Note the zero-free hypothesis is over the rectangle enlarged
vertically by `|τ|`, matching the corpus's convention.

Twisted layer: 2 of 11. Next: the twisted Perron identity in shifted form and the four-edge
assembly proper, then `EdgeSubstitution`, `ConcreteEdges`, `ContourBound{General,Ratio}`,
`MajorantRatio`, `CombinedBound`, `Rate`, `SharpSubstitution`, `SharpRate`.

## `Sieve/DampedTwistEdges` — the twisted four-edge bound (2026-08-19)

```
tsum_dampedTwist_smoothWeight_eq_dampedInvZeta_integral (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1)
    (0 < N) (0 < H) (1 < d) (τ) :
  (2π) • ∑'_n dampedTwist P t τ n · smoothWeight N H n
    = ∫ y, dampedInvZeta P t (d + iy + iτ) · mellin (smoothWeight N H) (d + iy)

norm_tsum_dampedTwist_smoothWeight_le_edges … (htrunc) (htop) (hbot) (hleft) :
  ‖(2π) • ∑'_n dampedTwist P t τ n · smoothWeight N H n‖ ≤ E₁ + E₂ + E₃ + E₄
```

Both first-try clean: the Perron identity is the generic formula at `dampedTwist` composed with
`tsum_dampedTwist_cpow`, and the four-edge bound is `norm_le_of_contour_edges` over the shifted
rectangle identity.

Twisted layer: 3 of 11 — `Perron`, `EdgeAssembly` (holomorphy), `Edges` (the bound). Remaining:
`EdgeSubstitution`, `ConcreteEdges`, `ContourBound{General,Ratio}`, `MajorantRatio`, `CombinedBound`,
`Rate`, `SharpSubstitution`, `SharpRate`.

## `Sieve/DampedTwistEdgeSubstitution` — fourth of the twisted layer (2026-08-19)

```
continuous_dampedInvZetaTwist_line (∀ q ∈ P, 2 ≤ q) (t) (τ) (1 < d) :
  Continuous fun y => dampedInvZeta P t (d + iy + iτ)

exists_norm_tsum_dampedTwist_smoothWeight_le (∀ q ∈ P, q.Prime) (0 ≤ t) (t ≤ 1) (0 < N) (0 < H) (j) (σmax) :
  ∃ C, 0 ≤ C ∧ ∀ τ c d T Md Mh Mc, … (edge sups for the shifted dampedInvZeta) …
    ‖(2π) • ∑'_n dampedTwist P t τ n · smoothWeight N H n‖
      ≤ 2(Md·C)/T + Mh·C/T^{j+1}(d−c) + Mh·C/T^{j+1}(d−c) + Mc(2(N+H)^c/c + 2C)
```

The three generic edge estimates applied to `F s = dampedInvZeta P t (s + iτ)`; the only new input
was continuity along the right line, which is the untwisted continuity composed with a translation.
First-try clean.

Twisted layer: 4 of 11. Remaining: `ConcreteEdges`, `ContourBound{General,Ratio}`, `MajorantRatio`,
`CombinedBound`, `Rate`, `SharpSubstitution`, `SharpRate`.

## The twisted damped layer is CLOSED (2026-08-19)

Seven further modules, all built, all `[propext, Classical.choice, Quot.sound]`:

| module | statement |
|---|---|
| `Sieve/DampedTwistContourBound` | `exists_norm_tsum_dampedTwist_smoothWeight_le_concrete` — the four edges at the concrete rectangle, each `invZeta` edge times `dampedCorrBound P (leftAbscissa K)` |
| `Sieve/DampedTwistSharpSubstitution` | `norm_tsum_dampedTwist_smoothWeight_le_sharp` — the four-edge inequality with the three decay constants as hypotheses |
| `Sieve/DampedTwistContourBoundGeneral` | `exists_norm_tsum_dampedTwist_smoothWeight_le_general` — arbitrary smoothing width |
| `Sieve/DampedTwistContourBoundRatio` | `exists_norm_tsum_dampedTwist_smoothWeight_le_ratio` — width replaced by the ratio `L = N/H` |
| `Sieve/DampedTwistMajorantRatio` | `…_le_ratio_factored` (the bound *is* `dampedCorrBound × (μ-twist expression)`) and `…_le_majorant_ratio` |
| `Sieve/DampedTwistRate` | `exists_norm_tsum_dampedTwist_smoothWeight_rate` — `≤ corr · 2(N+H+1)·exp(−c(log N)^{1/10}/2)` |
| `Sieve/DampedTwistSharpRate` | `exists_norm_sum_dampedTwist_rate` — `‖∑_{n≤N} μ_P^t(n)n^{−iτ}‖ ≤ corr·3N·exp(−c(log N)^{1/10}/2)/π + (H+1)` |

Three supporting geometry lemmas landed with them: `half_le_leftAbscissa`,
`continuous_dampedEulerFactorTwist_line`, `continuousOn_dampedInvZetaTwist_left_line`.

The design that made this cheap: **the correction factor is abscissa-only**, so
`Sieve/DampedShiftBound.norm_dampedInvZeta_shift_le` turns each of the twisted `invZeta` edge
estimates of `Sieve/MoebiusTwistConcreteEdges` into its damped counterpart with the *same* constant,
and `Sieve/DampedFactoredBound.norm_tsum_damped_le_of_moebius_shape` then transports every purely
inequational step of the twisted Möbius optimisation (`combined_terms_twist_le`,
`coeff_le_coeffMajorant`, `eventually_coeffMajorant_ratio_rate`) without re-proving any of it.

Net: the damped sum enjoys the full zero-free-region saving, uniformly in the twist `τ` inside
`5 + 4|τ| ≤ contourParam(N+H)`, and uniformly in the damping `t ∈ [0,1]` up to the single factor
`dampedCorrBound P c = ∏_{p∈P} (1+p^{−c})/(1−p^{−c}) ≤ exp(3∑_{p∈P}p^{−c})`.

Next: the damped analogue of `Sieve/CofactorLowFreqBound`, then steps 3–5 of the programme.

## The exact-Ramaré chain is CLOSED in Lean — and its rate has a hard ceiling (2026-08-19)

### What landed

Six further modules complete the exact-Ramaré replacement of the Turán–Kubilius normalisation, end
to end, with no hypotheses left except the two analytic inputs `hV`, `hU`:

| module | statement |
|---|---|
| `Sieve/DampedCofactorLowFreqBound` | `dampedSharpBound`; `exists_norm_logPoly_dampedOmegaMoebius_Icc{,_one}_le` (uniform in `t ∈ [0,1]`); **`exists_norm_logPoly_ramareCofactorCoeff_Icc_one_le`** and **`…_geomCofactorBlockAt_le`** — the saving for the *exact* Ramaré cofactor `μ(m)/(ω_P(m)+1)` |
| `Sieve/BlockProductAnnulus` | `integral_normSq_blockProduct_{set,low,annulus}_le` — `Sieve/LadderAnnulus`'s two-regime estimate for an arbitrary cofactor coefficient with `‖a n‖ ≤ 1` |
| `Sieve/RamareLadderAnnulus` | `integral_normSq_ramareLadderError_le_defectSum`; `integral_normSq_ramareBilinear_annulus_le` |
| `Sieve/RamareLadderAffine` | `ramareStep{Slope,Const}`, `ramareLadder{Slope,Const}` and `integral_normSq_ramareBilinear_affine_le` |
| `Sieve/RamareBilinearKernelBound` | `nonRoughCoeff`; `logPoly_nonRoughCoeff_eq_ramareBilinear`; `integral_kernel_normSq_ramareBilinear_le` |
| `Sieve/FibreRamareLadderFinal` | `ladderPrimeSup/CofactorSup/PrimeCard`; `integral_normSq_ramareBilinear_ladder_affine`; **`sum_sq_fibreSum_moebius_le_ramareLadder_final`** |

The decisive structural fact making the Gallagher layer reusable: `Sieve/NonRoughBilinearExact`
identifies `ramareBilinear P M` with `logPoly (nonRoughCoeff P) (Icc 1 M)` **exactly**, so
`gallagher_split_integral_dyadic_head` and `affineMajorant_two_regime` — both coefficient-general —
apply verbatim, and `‖nonRoughCoeff‖ ≤ 1` makes the energy `≤ M` instead of the `ω`-route's `M·W²`.

So the chain now reads, unconditionally:

```
∑_a (∑_{b ∈ fibre} μ b)²
  ≤ 16√x · [ 2δ²(αG + β) + 4(α + 5π/2·M + 5e/2·M²/T₀)/(π²G) + 4β/(3π²G²) ]
    + 204(√x + 1) + 2·#outerBlock · (fibreRamareSieveError h z r λ)²
```

with `α = ramareLadderSlope`, `β = ramareLadderConst`, `M = ⌊√x + h⌋`, `δ = fibreWidth x h ≍ h/√x`,
and **no `1/W` anywhere**. The Turán–Kubilius loss the card was opened for is gone.

### The ceiling, and it is a theorem about the route, not about the bookkeeping

Write `log h = (log x)^β` (`β = 99/100`), `M ≍ √x`, `G = gallagherCut ≍ M/h`,
`T₀ = budgetT ≍ M`, `P = primesRange z₀ z`, `log z₀ = (log x)^{γβ}`, `log z = (log x)^{β'}`.
Four constraints, each forced:

1. **Trivial regime above `T₀`.** The term `4·(5e/2)·M·E/(T₀π²G)` with `E ≍ M` and `G ≍ M/h`
   is `≍ Mh/T₀`; it is below the target `ε'h²` only for `T₀ ≳ M/(ε'h)`. With `h = x^{o(1)}` this
   forces `T₀ = x^{1/2−o(1)}`, hence `log T₀ ≍ log x`.
2. **The annulus saving.** `Sieve/AnnulusRelBound.relScaledMajorant` carries `exp(−μ·log Q)` with
   `μ = routeTWidthPolylogLower A (2πT₀)/2 ≍ (log T₀)^{−9/10}`. A polylog saving needs
   `μ·log Q ≫ log log x`, i.e. **`log Q ≳ (log x)^{9/10}`**.
3. **The top of the prime range.** `αG ≤ ε'x` with `α ≍ ρ²M z/η²` (harmonic Cauchy–Schwarz) and
   `G ≍ M/h` gives `z ≲ h·polylog`, i.e. **`log z ≤ (log x)^{β}(1+o(1))`**.
4. **The rough set.** For `P = primesRange z₀ z` the discarded integers are those with no prime
   factor in `(z₀, z]`; their density is `≍ log z₀/log z`, and it enters the fibre mean square
   **squared**: `2(log z₀/log z)²`.

By (2) and (3), `log z₀/log z ≥ (log x)^{9/10−β} ≥ (log x)^{−1/10}`, so the rough term is at least
`(log x)^{−1/5}`. **The exact-Ramaré route therefore caps at rate `(log x)^{−1/5+o(1)}`** — a large
improvement over the corpus's structural `Θ(1/log log x)`, and a power of `log`, but short of the
`(log x)^{−1−c}` the marker join needs.

Generalising (2) to a zero-free width exponent `κ` (Vinogradov–Korobov is `κ = 2/3`, the corpus's
Route T is `κ = 9/10`), the ceiling is `(log x)^{−2(β−κ)}`, and since `β < 1` this exceeds
`(log x)^{−1}` **for every `κ > 1/2`**. So no zero-free region short of
`ζ(σ+it) ≠ 0` for `σ > 1 − c(log|t|)^{−1/2}` — far beyond Vinogradov–Korobov — closes the cards
through this route.

### Two routes that do not repair it

- *Keep `P = primesLE z`* (rough density `1/log z = (log x)^{−β}`, squared `(log x)^{−1.98}`, ample).
  The ladder then has to start at `Q < 2` and cover the small primes. Their steps have no
  cancellation, so `V_j = #B_j ≍ ηQ_j/log Q_j`, and the annulus constant of the low steps alone is
  `(∑_{Q_j ≤ z₀} V_j·M/Q_j)² ≍ M²(log(1/η))²` — larger than the trivial bound. Small primes carry a
  positive proportion of the Ramaré mass and cannot be given a sup bound.
- *A second Ramaré range above `z`.* Blocked by (3): for `Q_j > z ≍ h` the annulus constant
  `ρ²M³/(η²h)` exceeds `ε'M²` by the factor `M/h = x^{1/2−o(1)}`.

### What is actually left, named

A **large-values (Halász–Montgomery) replacement for `hV`**. A sup bound `‖∑_{p ≍ Q} μ(p)p^{−2πiw}‖
≤ ρQ` valid for small `Q` is *false* — by Kronecker the phases align somewhere in every long
frequency range — so the annulus estimate must be restructured from a sup bound to a level-set
statement: bound `∫_{|w| ≤ T} ‖P_j(w)‖²‖C_j(w)‖²` by splitting on the level sets of `|P_j|` and
using a large-values bound for the measure of each. That is Matomäki–Radziwiłł's actual mechanism,
it has no lower constraint on `Q`, and the corpus already owns the large-values stack
(`Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`,
`Sieve/MatomakiTeravainenTypeIISparseHalaszMontgomery`, `Sieve/DirichletMeasureLargeValues`,
`Sieve/LargeSieveWeak`, `Sieve/MeanSquareLevelSplit`, `Sieve/PrimePowerSupport`).
`Sieve/BlockProductAnnulus` is already coefficient-general, so only its annulus half needs the
level-set form; everything downstream of it in the list above is unchanged.

## `Sieve/BlockProductLevelSplit` — the interface the large-values route plugs into (2026-08-19)

```
integral_normSq_blockProduct_levelSplit (a) (B D) (0 < V₀) (#B ≤ 2^J · V₀) :
  ∫_{|w| ≤ G} ‖primeBlockPoly B w · logPoly a D w‖²
    ≤ V₀² · ∫_{|w| ≤ G} ‖logPoly a D w‖²
      + ∑_{j < J} (2^{j+1} V₀)² · ∫_{|w| ≤ G, ‖primeBlockPoly B w‖ ≥ 2^j V₀} ‖logPoly a D w‖²
```

`Sieve/MeanSquareLevelSplit.integral_sq_mul_le_levelSplit` at `f = ‖primeBlockPoly B‖`,
`g = ‖logPoly a D‖²`, with `#B` as the a-priori sup from
`Sieve/OmegaBudgetFromAnnulus.norm_primeBlockPoly_le_card`.  Coefficient-general, so it applies to
`ramareCofactorCoeff` at once.

### The next brick, named precisely

What remains is a bound for the level sets that does **not** go through Chebyshev (which returns the
trivial answer): for `S_j = {|w| ≤ G : ‖primeBlockPoly B w‖ ≥ V_j}`,

```
∫_{S_j} ‖logPoly a D w‖² dw   ≪   (measure/spacing of S_j) · (Halász–Montgomery bound for D).
```

The two corpus assets to compose are
`Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit` — for one-separated `λ_r` of
diameter `T`, `∑_r |D(λ_r)|² ≤ (N + 12πN(1+log K)/δ + K(1 + 214√T + 1536 N/√U))‖a‖²` — and
`RHTower/WellSpacedSubset.exists_wellSpaced_subset`.  Two gaps to bridge, both mechanical but not
yet built:

1. **From an integral over `S_j` to a sum over separated points.** `∫_{S_j}‖D‖²` against
   `∑_r ‖D(λ_r)‖²` over a `1`-separated subset of `S_j`: a Sobolev/Gallagher step on unit intervals.
2. **From a dyadic block to an initial segment.** `halaszMontgomery_dyadic_explicit` is stated for
   `dyadicDirRow N`, i.e. coefficients supported on `[N, 2N)`; the cofactor's support is
   `Icc 1 ⌊M/Q_j⌋`, so a dyadic decomposition in `n` (cost `log`) is needed.

Neither step needs a lower bound on `Q`, which is exactly why this route is not subject to the
`(log x)^{−1/5}` ceiling above.

## Brick 1 of the large-values route is CLOSED — the level set is sampled inside itself (2026-08-29)

The previous entry named two mechanical gaps between `Sieve/BlockProductLevelSplit` and the corpus's
large-values stack.  The first is now closed.

> **1. From an integral over `S_j` to a sum over separated points.**

The obstruction was that the corpus's discretisation
(`HTGeometry/CellMaxDiscretisation.exists_spaced_families_integral_le`) works on a *full interval*
and produces unconstrained sample points, while every large-values estimate needs the sample points
to satisfy the level condition — i.e. to lie in `S_j`.

The resolution is that `S_j` is **closed**, not merely measurable: `primeBlockPoly B` is continuous,
so `S_j = [-G,G] ∩ {w : V ≤ ‖primeBlockPoly B w‖}` is a compact interval intersected with the
preimage of a closed half-line.  For a closed restricting set the cell-max argument runs verbatim —
each closed unit cell meets `S_j` in a *compact* set, so a continuous integrand attains its maximum
there at a point **of `S_j`**.

Two new modules, unconditional and axiom-clean (`[propext, Classical.choice, Quot.sound]`), both
umbrella-wired:

`GaloisForLFunctions/HTGeometry/CellMaxSetDiscretisation.lean`

```text
iUnion_Ioc_cells                        the half-open cells of length Δ tile Ioc a (a+mΔ)
exists_cell_max_setIntegral_le          maxima taken inside U, over the cells that meet U
exists_spaced_families_setIntegral_le   ∃ S₁ S₂ ⊆ U ∩ Icc a (a+mΔ), both Δ-spaced, with
                                          ∫_{U ∩ Ioc a (a+mΔ)} F ≤ Δ·( ∑_{S₁} F + ∑_{S₂} F )
```

`GaloisForLFunctions/RHTower/Sieve/LevelSetSpacedSample.lean`

```text
primeBlockLevelSet B G V                = Icc (−G) G ∩ {w : V ≤ ‖primeBlockPoly B w‖}
isClosed_primeBlockLevelSet
exists_spaced_families_levelSet_le
    ∫_{S_V} ‖logPoly a D‖²  ≤  ∑_{P₁} ‖logPoly a D‖² + ∑_{P₂} ‖logPoly a D‖² ,
    with P₁, P₂ ⊆ S_V one-spaced
exists_spaced_families_blockProduct_levelSplit
    **the level split with every level set already discretised**:
      ∫_{|w| ≤ G} ‖primeBlockPoly B w · logPoly a D w‖²
        ≤ V₀²·∫_{|w| ≤ G} ‖logPoly a D w‖²
          + ∑_{j < J} (2^{j+1}V₀)² · ( ∑_{P₁ j} ‖logPoly a D‖² + ∑_{P₂ j} ‖logPoly a D‖² ) ,
    with `P₁ j, P₂ j ⊆ primeBlockLevelSet B G (2^j V₀)` one-spaced
```

The whole cost of the discretisation is the factor two from the parity split of the cells.

**What remains of the large-values route.**  Only the second named gap:

> **2. From a dyadic block to an initial segment.**  `Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`
> is stated for `dyadicDirRow N`, i.e. coefficients supported on `[N, 2N)`; the Ramaré cofactor's
> support is `Icc 1 ⌊M/Q_j⌋`, so a dyadic decomposition in `n` (cost `log`) is needed.

With that, `exists_spaced_families_blockProduct_levelSplit` feeds the Halász–Montgomery bound
directly, and — as recorded above — this route carries **no lower constraint on `Q`**, so it is not
subject to the exact-Ramaré chain's `(log x)^{−1/5}` ceiling.

## Brick 2 is CLOSED — the initial segment splits into dyadic blocks (2026-08-29)

> **2. From a dyadic block to an initial segment.**

`GaloisForLFunctions/RHTower/Sieve/LogPolyDyadicSplit.lean`, unconditional, axiom-clean,
umbrella-wired:

```text
dyadicSegmentBlock M j                  = { n ∈ [1,M] : ⌊log₂ n⌋ = j }
mem_dyadicSegmentBlock                  2^j ≤ n < 2^{j+1} on the j-th block
logPoly_Icc_eq_sum_dyadicBlocks         logPoly a [1,M] = ∑_{j ≤ ⌊log₂ M⌋} logPoly a (block j)
normSq_logPoly_Icc_le_card_mul_sum_blocks
    ‖logPoly a [1,M] w‖² ≤ (⌊log₂ M⌋+1) · ∑_j ‖logPoly a (block j) w‖²
sum_normSq_logPoly_Icc_le_card_mul_sum_blocks
    ∑_{w ∈ P} ‖logPoly a [1,M] w‖² ≤ (⌊log₂ M⌋+1) · ∑_j ∑_{w ∈ P} ‖logPoly a (block j) w‖²
```

The decomposition itself is the corpus's `Sieve/AdicBlocks.sum_Icc_eq_sum_dyadic_blocks`; what is
new is its Dirichlet-polynomial form, the Cauchy–Schwarz cost, and the frequency-summed version —
the exact shape a per-block Halász–Montgomery estimate is consumed in.  The whole cost of the
reduction is the single factor `⌊log₂ M⌋ + 1`.

### Both named gaps of the large-values route are now closed

The route recorded on 2026-08-19 read:

> What is actually left, named: a large-values (Halász–Montgomery) replacement for `hV` … Two gaps
> to bridge, both mechanical but not yet built: (1) from an integral over `S_j` to a sum over
> separated points; (2) from a dyadic block to an initial segment.

Both are now theorems.  Composing `exists_spaced_families_blockProduct_levelSplit` (brick 1) with
`sum_normSq_logPoly_Icc_le_card_mul_sum_blocks` (brick 2) reduces the annulus estimate to

```text
    ∑_{w ∈ P} ‖logPoly a (dyadic block) w‖²      over a one-spaced P inside a level set of the
                                                 prime block polynomial,
```

which is precisely the hypothesis shape of `Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`
and of `RHTower/WellSpacedSubset`.  What remains on this lane is the arithmetic of the composition —
choosing `V₀` and `J`, and bounding the level-set cardinality by the large-values theorem — not any
further structural bridge.

## The large-values interface is COMPLETE — `exists_spaced_families_blockProduct_gramRows` (2026-08-29)

Two further modules close the composition, both unconditional, axiom-clean and umbrella-wired.

`Sieve/LogPolyBlockBridge` — the dyadic pieces *are* Huxley blocks:

```text
dyadicSegmentBlock_subset_Ico            block j ⊆ [2^j, 2·2^j)
dyadicSegmentCoeff a M j                 the block's coefficients, extended by zero
logPoly_dyadicSegmentBlock_eq_blockPoly  logPoly a (block j) w = blockPoly (2^j) coeff 0 (−2πw)
logPoly_dyadicSegmentBlock_eq_inner      = ⟪dyadicDirRow (2^j) (−2πw), blockCoeff …⟫
```

The only content is the frequency normalisation `t = −2πw` at `σ = 0`; `logPoly` carries the phase
`exp(2πi w log n)` and `blockPoly` carries `exp(−i t log n)`.

`Sieve/BlockProductHalaszReady` — the capstone:

```text
exists_spaced_families_blockProduct_gramRows
  ∃ one-spaced P₁ j, P₂ j ⊆ primeBlockLevelSet B G (2^j V₀) with
    ∫_{|w| ≤ G} ‖primeBlockPoly B w · logPoly a [1,M] w‖²
      ≤ V₀² · ∫_{|w| ≤ G} ‖logPoly a [1,M] w‖²
        + ∑_{j < J} (2^{j+1}V₀)² · (⌊log₂ M⌋+1) ·
            ∑_{i ≤ ⌊log₂ M⌋} ( ∑_{w ∈ P₁ j} ‖⟪dyadicDirRow (2^i) (−2πw), c_i⟫‖²
                              + ∑_{w ∈ P₂ j} ‖⟪dyadicDirRow (2^i) (−2πw), c_i⟫‖² )
```

Every quantity on the right is now of the *exact* shape the corpus's large-values theorems bound:
`halaszMontgomery_dyadic_explicit`, `halaszMontgomery_dyadic_log`,
`huxley_multiblock_large_values`, `largeValues_dirPoly_finset`.  The three costs of the reduction
are explicit and small: the factor `2` of the parity split, the factor `⌊log₂ M⌋+1` of the dyadic
Cauchy–Schwarz, and the dyadic level split's own `∑_j (2^{j+1}V₀)²`.

**No structural bridge remains on this route.**  What is left is the arithmetic: choose `V₀` and `J`
from the block's Mertens mass, bound `#(P₁ j)` and `#(P₂ j)` by the large-values theorem applied on
the level set `primeBlockLevelSet B G (2^j V₀)` (whose points are one-spaced *by construction*), and
compare the resulting saving with the target `ε' h²`.  Since no step used a lower bound on the block
scale `Q`, the `(log x)^{−1/5}` ceiling of the exact-Ramaré chain does not apply.
