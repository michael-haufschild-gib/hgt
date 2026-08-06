# kappa = 1 zero-free region: PROVED and formalized

`RHTower.Sieve.exists_zero_free_region` in
`formal/GaloisForLFunctions/RHTower/Sieve/ZeroFreeRegionKappaOne.lean`. Unconditional,
`[propext, Classical.choice, Quot.sound]`. Card:
`docs/drafts/pipeline/3-formalized/zero-free-region-exponent-one.md`.

```lean
∃ c T : ℝ, 0 < c ∧ 3 ≤ T ∧
  ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 → 1 - c / Real.log |γ| < β →
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0
```

**This supersedes `mem:zero-free-region-exponent-is-the-mr-wall`'s "corpus and PNTPlus both own only
kappa = 9".** That is now stale: the corpus owns `kappa = 1`. The mean-value route really was
capped at 9 (`mem:route_e/zero_free_kappa9_is_structural_2026_08_06`); the log-derivative route is
what breaks it.

## Chain (all new this session)

`AnalyticBallZeroSet` → `AnalyticBallFactorization` → `AnalyticBallFinsetFactorization`
(HTGeometry) → `BorelCaratheodoryLogDeriv` → `LandauLemma` → `LandauRealPart`
+ `ZetaLogDerivThreeFourOne` + `ZetaPoleLogDeriv` + `ZetaCrudeGrowth` → `ZetaLandauInput`
→ `DeLaValleePoussinInequality` → `ZeroFreeRegionKappaOne` (RHTower/Sieve).

See `mem:route_e/landau_lemma_proved_2026_08_06` and
`mem:route_e/dlvp_inequality_proved_2026_08_06` for the two key sub-results and their traps.

## Parameters actually used

`c₀ = 1/500` (the `delta` scale), `c = 1/10000` (the region width), `R = 1/4`, `R₀ = 3/8`,
Landau constant `64` at that radius. The bracket `4/(c₀+c) - 3/c₀ - 400 = 100/21 > 0` is what
makes it work; the threshold `T = exp(u₀²)` with `u₀ = max 202 (K+1)` is astronomically large but
explicit in `K = max (3A + 400 log 15 + 240 log 501) 0`.

## Still open (for Route E)

The **Littlewood refinement**: substitute `RHTower/Sieve/ZetaLineRate.lean`
(`||zeta(1+it)|| = O(log t/loglog t)`, see `mem:route_e/littlewood_exponent_proved_2026_08_06`) for
`ZetaCrudeGrowth` inside `zeta_landau_at`. That sharpens `c/log|gamma|` to
`c loglog|gamma|/log|gamma|` — the form Route E's corridor licenses. The obstruction: `ZetaLineRate`
holds on the line `Re s = 1`, whereas `zeta_landau_at` needs a bound on a **disc** of fixed radius
`3/8`, which reaches `Re w = 5/8`. So the refinement needs the rectangle version
(`DirichletSigmaCapstone`) extended to a fixed-width strip, or a shrinking-radius Landau with
`R ≍ 1/log t` (which costs a factor `log t` in the Landau constant — check the arithmetic before
building).
