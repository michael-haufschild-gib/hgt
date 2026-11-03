# The two-collar recursion of the window tower (review-0311 §2.5.1)

- **ID:** R0311-25-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.1
- **Statement:** The frozen two-collar form of every stage in closed form, its evolution law, and its
  collar coupling at the first two prime stages.

## Answer

Stage `n`, `ℓ = log n`, `w = Λ(n)/√n`, `log n + ε < log(n+1)`; collars `L = [−ℓ−ε, −ℓ]`,
`R = [−ε, 0]`, interior `I = [−ℓ, −ε]`.

1. **Coupling of ordered tests.** If `f = 0` right of `a` and `g = 0` left of `a`,
   `Q(f+g) = Q(f) + Q(g) + 2(∫_0^∞ κ c_{fg} − Σ_n w_n c_{fg}(log n))`, `c_{fg}(x) = ∫f(u)g(u+x)`,
   `κ(x) = 2cosh(x/2) − ω(x) = e^{x/2} − e^{−x/2}/(e^{2x}−1) = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}`:
   the trivial divisor of `ζ` (pole `s=1`, trivial zeros `s=−2k`); the Gamma pole `s=0` cancels
   against the pole term.
2. **Transmission.** `∫_0^∞ κ c_{fg} = μ_1(f)ν_1(g) − Σ_{k≥1} μ_{−2k}(f)ν_{−2k}(g)`,
   `μ_s(f) = ∫f e^{(½−s)u}`, `ν_s(g) = ∫g e^{(s−½)v}`.
3. **Gluing and the two-collar identity.** `Q(x_L+y+x_R) = F − 2w⟨x_L, τ_ℓ x_R⟩`,
   `F = Q(x_L+y) + Q(y+x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩`, and `F = Q_N` (the stage datum).
   `S^N_ε = inf_y F`; stage positivity ⟺ `2w⟨x_L, τ_ℓx_R⟩ ≤ F` on all stage tests.
4. **Closed form.** `F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L),ν(y)⟩ + ⟨μ(y),ν(x_R)⟩ + ⟨μ(x_L),ν(x_R)⟩)
   − 2Σ_{m<n} w_m(⟨x_L,τ_m y⟩ + ⟨y,τ_m x_R⟩)`. Stage 1: no earlier fold; `F − Q(x_L) − Q(x_R)`
   depends on the collars only through their moment sequences. Stage 2: the only earlier fold
   `T₂` adds `−2w₂(⟨x_L,τ₂y⟩ + ⟨y,τ₂x_R⟩)`.
5. **Evolution.** Window growth by `ε` is a translation contraction:
   `Q ≥ 0` on `W_{ℓ+ε}` ⟺ `Q ≥ 0` on `W_ℓ` and `W(τ_εu, v)² ≤ Q(u)Q(v)` for all `u, v` on `W_ℓ`.
   At a stage `W(τ_εu, v) = W_N(τ_εu, v) − w c_{uv}(ℓ−ε)`: the fold lies in the Carathéodory disk of
   centre the frozen pairing and radius `√(Q(u)Q(v))`; in `ε` the centre moves by translation, the
   impulse is the fold entering at lag `ℓ − ε`; composite stages carry none.
   RH ⟺ every growth step is a translation contraction.

## Proof

1: polarize the Lévy form of `Q` (`weilQuad_eq`); for ordered tests `fg = 0`, the mixed Lévy
integrand is `−ω c_{fg}`, the pole cross term is `4∫ c_{fg} cosh(x/2)` (exponential moments factor,
Fubini), the prime cross term is `2Σ w_n c_{fg}(log n)`. `κ`: algebra in `e^{x/2}`. 2: geometric series
of `ω − e^{−x/2}` and monotone interchange (the series is dominated by `ω|c|`, integrable as the mixed
Lévy integrand). 3: the chain law from 1 and additivity of the coupling; the collars see each other
only at `log n` (`log(n+1) + log(n−1) ≤ 2log n`); `Q_N = Q + 2w∫H(u)H(u+ℓ)` (`markovForm_succ`) and on
stage tests that correlation is `⟨x_L, τ_ℓx_R⟩`. 4: each adjacent pair spans less than `log n`, so
only folds `m < n` enter. 5: smooth partition of unity on `[−ℓ, −ε]`, `weilQuad_plane`, discriminant;
RH direction by induction on `⌈2000A⌉` from `weilQuad_ge_of_short`.

## Lean

Folder `formal/GaloisForLFunctions/CanonicalSystemOfTheWindowTower/`, umbrella
`CanonicalSystemOfTheWindowTower.lean` (in `MainTheorems`):

- `TheTrivialDivisorCouplesOrderedTests`: `two_mul_cosh_sub_archLevyDensity`, `hasSum_collarKernel`,
  `weilQuad_add_of_ordered`, `OrderedAt.integral_collarKernel_mul_eq_moments`,
  `weilQuad_add_of_ordered_of_primeFree`.
- `TheFrozenFormGluesTwoWindows`: `weilQuad_chain_three`, `weilQuad_stageTest`, `stage_nonneg_iff`,
  `stageForm_stageTest`.
- `TheFrozenFormInClosedForm`: `frozenTwoCollar_eq_transmitted`, `firstStage_frozenTwoCollar_eq`,
  `firstStage_frozen_congr`, `secondStage_frozenTwoCollar_eq`.
- `WindowGrowthIsATranslationContraction`: `window_nonneg_iff_contraction`, `weilPair_stage_eq`,
  `stage_nonneg_iff_disk`, `riemannHypothesis_iff_translation_contraction`.

Each module passes `lake --old env lean` individually; no `sorry`, no axioms.
