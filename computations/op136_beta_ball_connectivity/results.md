# Task #136 pre-certification: ball-complement connectivity at β — results (2026-07-02)

**Question.** For real `c`, is `B(β, ρ) ∖ K_c` connected (i) at every small `ρ`
(`OneSidedAt`, the ∀-form) / (ii) at arbitrarily small `ρ` (the cofinal form)?
Multiplier `2β` at β is real > 1, so the Julia germ at β is log-periodic in scale:
whatever happens at one scale recurs at scale `/λ`, `λ = 2β`.

**Method.** Rasterized escape test (bail 9, maxit 800–8000, grids 401²–1601²) on
`B(β,ρ)`, 4-connected component count of the complement inside the disk, ρ log-spaced
over 5 periods (`beta_ball_connectivity.py`); stability matrix in resolution × maxit at
the split phases (`stability_check.py`). Raw outputs: `results_scan_401x800.txt`,
`results_stability.txt`.

**Results.**

- `c = 0.2, 0.24, −0.5, −1.0`: single component at every sampled phase over 5 periods.
- `c = −0.9` (period-2 window): mirror-pair extra components (conjugation symmetry) at a
  recurring phase — detected at `ρ ≈ 0.0962` and `ρ ≈ 0.0306` in the coarse scan
  (ratio `3.1448 = λ` exactly), confirmed at depth at `ρ ≈ 0.00973` (pair size 382/side,
  n=1601, maxit=4000) and `ρ ≈ 0.00309` (pair 363/side, maxit=8000). Area fraction
  stable (~2–4·10⁻⁴ of the ball) across maxit 800→3200 (identical counts — NOT
  slow-escape artifacts) and across grid 401→1601; pocket positions scale self-similarly
  toward β and sit at the ball rim (dist ≈ ρ): complement regions cut off inside the
  ball by K-limbs, rejoining Ω only outside the ball.
- A second, smaller pocket pair appears at a nearby phase (`frac = 6.25`), so the "bad"
  bands have some width; the clean bands still dominate each period.

**Verdicts.**

1. **The ∀-form `OneSidedAt` is FALSE at β for `c = −0.9`** — disconnection recurs at
   every depth in periodic ρ-bands. Hence OP6's Known Fact 3 gloss "one access ⟹
   one-sided (ball sense)" is invalid (correction added to the problem file), and the
   `OneSidedDense` Prop (∀-form density) is in doubt for such parameters.
2. **The cofinal form is comfortably TRUE at β for all tested `c`** (clean bands each
   period; for `c ∈ {0.2, 0.24, −0.5, −1}` every sampled phase was clean). This is the
   form the Lean re-cut (`OneSidedCofinal.lean`) consumes, and the remaining #136
   mathematics: prove cofinal punctured-ball connectivity at β for real `c`.

**Caveats.** Raster tests can miss sub-pixel fjords (would only ADD bad phases — cannot
un-refute the ∀-form) and cannot certify the cofinal claim, only support it; the Lean
target stays a theorem to be proven, not promoted from this data.
