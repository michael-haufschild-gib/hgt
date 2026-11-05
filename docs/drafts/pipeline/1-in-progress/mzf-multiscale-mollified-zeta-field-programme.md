# Multiscale analysis of the mollified zeta field

- **ID:** MZF
- **Stage:** 1-in-progress
- **Type:** CONJECTURES
- **Source:** [Obstacles summary §2.7.2](../../../reports/review-0511/obstacles-summary.md), [route-wd §1](../../../reports/review-0511/route-wd.md), card [WD-LONG-MOEBIUS-SLOPE-LAW](../2-fully-proven/wd-long-moebius-second-moment-slope-law.md)
- **Statement:** Develop the multiscale field programme; attack the residual of the slope law.
- **Lean:** `formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/`, umbrella `MultiscaleMollifiedZetaField.lean`.

## Goal

Answer the central question of §2.7.2 and the residual of the slope-law card. The card's Lean belongs to another agent
(`ArithmeticProduction/PrefixCancellationAmplifiesTheZeroFloor.lean`, `LongMoebiusSecondMomentSlopeLaw.lean`): do not duplicate it.

## Gates
- [x] 0 → 1  in-progress: targets stated
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Residual: status

Closing the θ-slope from `2·zetaZeroWidth` to `0` is RH. It cannot be closed by formalization. Target: its weakest equivalent form.

### Paper proof: the logarithmic floor

Let `E = ζM − 1` where `ζM` has coefficients `δ_{n,1}` for `n ≤ y`, and let `ρ = ½+δ+iγ` be a zero with `δ > 0`.

`G(z) = (y+1)^{z−½}(z−1)E(z)` is entire of polynomial growth on `Re z ≥ ½`: on `Re z ≥ 3` the coefficients of `E` start after `y`,
so `(y+1)^z E(z)` is bounded. Half-plane Jensen gives `log|G(ρ)| ≤ ∫P_ρ log|G(½+iu)|du`. Here `|G(ρ)| = (y+1)^δ|ρ−1|` and
`|½+iu−1| = |½+iu|`, whose Poisson mean is `log|ρ|`. Hence

`∫P_ρ(u) log|E(½+iu)| du ≥ δ log(y+1) − log(|ρ|/|1−ρ|)`.

### Paper proof: exponent rigidity

Let `width > 0` and `E_X = ζM_X − 1`. Cap: `log⁺|E_X(½+iu)| ≤ (width+ε) log X + C log(2+|u|)` from the Mertens bound and
`|ζ(½+iu)| ≪ 1+|u|`. Pick a zero with `δ > width − ε`. The nonnegative function
`(width+ε) log X + C log(2+|u|) − log|E_X(½+iu)|` has `P_ρ`-mean `≤ 2ε log X + C′`. By Markov, on any compact window `J`,

`|{u ∈ J : |E_X(½+iu)| < X^{width−κ}}| → 0` as `X → ∞`, for every `κ > 0`.

Consequence: `zetaZeroWidth ≤ β` iff there are a window `J` and `ν > 0` such that for every `ε > 0` and arbitrarily large `X`,
`|{u ∈ J : |E_X(½+iu)| ≤ X^{β+ε}}| ≥ ν`. One window, positive proportion, sparse lengths, no moment and no height parameter.
The forward direction follows from the cap.

### What this does and does not do

These are RH equivalences, not progress on the sign of `M`. They locate the residual in the compact-window regime `X → ∞`, where primes are
not independent (a prime block at bounded height is nearly one rotating phase), so the barrier method does not apply there.

## Log
- 2026-11-05 — created; README first draft written.
