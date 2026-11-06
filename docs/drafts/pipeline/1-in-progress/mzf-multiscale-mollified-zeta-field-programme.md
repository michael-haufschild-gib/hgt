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
`(width+ε) log X + C log(2+|u|) − log|E_X(½+iu)|` has `P_ρ`-mean `≤ 2ε log X + C′`, so the `P_ρ`-mass of
`{|E_X| ≤ X^κ}` is at most `(width−δ)/(width−κ) + o(1)`.

The Poisson weight of a zero of depth `δ` on a window `J` depends on `ρ`. Fixed-window vanishing of the low set therefore follows
only when a zero attains the width (`tendsto_volume_lowSet_of_top_zero`). When the width is not attained, the criterion needs a uniform `ν` on
every window (`zetaZeroWidth_le_iff_positive_proportion`): `zetaZeroWidth ≤ β` iff there is `ν > 0` such that for every window, every
`ε > 0` and arbitrarily large `X`, `|{u ∈ J : |E_X(½+iu)| ≤ X^{β+ε}}| ≥ ν`.

One window does suffice for the moment form, through Sobolev and Abel: RH iff `∀ε ∃B ∀X≥1, ∫_0^1 |ζM_X(½+iu)|² ≤ B X^{2ε}`
(`riemannHypothesis_iff_unit_window`).

### What this does and does not do

These are RH equivalences, not progress on the sign of `M`. They locate the residual in the compact-window regime `X → ∞`, where primes are
not independent (a prime block at bounded height is nearly one rotating phase), so the barrier method does not apply there.

### Paper insights not in Lean

- Size detection cannot separate holes (`|E| ≥ 1`) from zeros: the model `exp(f)` has holes and no zeros, `1+f` has zeros at the last scale. The union over `≈ log V` independent cells at fixed `A` is unavoidable for size methods.
- Rate-one wall: any `ζ`-involving `k`-th moment needs `2kθ ≤ 1`, so `N(a) ≪ T L e^{−a}` and the occupancy threshold is `A ≈ log log V`.
- Near-line second moment: a bound `∫_T^{2T}(Σ_ρ m_ρ/(1+δ²(γ_ρ−t)²))² ≪ T/c²` would carry `exists_card_zeros_without_deep_companions_le` from rate one to rate two. The camera at centre `0` bounds the positive kernel `Σ m v̂(δ(γ−t))` in `L²` by `T/c²`, and dyadic widths give the Lorentzian, but camera weights of deep zeros at centre `0` have no sign, and their `L¹` bound only returns rate one.
- Newton ladder `E → E²` is Vaughan's identity, `E_{X²} = E_X² + ζ·(bilinear sawtooth)`; neutral for the slope.
- The window second moment is the bilinear Möbius correlation `Σ μ(m)μ(n)(mn)^{−½} ŵ(log m/n)`.
- Torus against Cauchy flow: `∫ log⁺|P_X| dHaar = O(log log X)` on the torus; on the flow measure RH iff `o(log X)`.
- At a zero `E_X(ρ) = −1`, `E_X′(ρ) = ζ′(ρ) M_X(ρ)`, and `M_X(ρ) ≈ log X/ζ′(ρ)` above the window: the link to negative moments.
- Jentzsch–Szegő: zeros of `M_X` should condense on `Re s = Θ`; the Hurwitz half is easy, the rest open.

## Proved in Lean

All unconditional; each named module compiles with no errors.

| Item of §2.7.2 | Statement | Module |
|---|---|---|
| (a)1 | Selberg's CLT with dyadic prime decomposition | `SelbergsCentralLimitTheorem`, `ThePrimeFieldIsGaussian` |
| (a)2 | twisted second moments against Euler pieces, length `≤ U^{21/50}` | `TheTwistedMomentFactorsOverBlocks` |
| (a)3 | barrier estimates with the Gaussian rate | `ThePrimeWalkObeysItsBarrier` |
| (b)1 | barrier data does not decide occupancy; no short weight lowers the defect | `BarriersAreBlindToPurity`, `TheLastScaleSurvivesEveryShortWeight` |
| (b)2 | floor `c e^{−2θa}/a` from the primes above the mollifier: no polynomial detector below `(1−ε) log log V/(2θ)` | `TheLastScaleSetsTheDefect` |
| (b)3 | long-Möbius energy with log-slope `S` bounds `Σ|ρζ′(ρ)|^{−2}` by `4S` | `TheLongMollifierPaysForNegativeMoments` |
| Central question | negative as an implication; occupancy `≪ (L/a) e^{−22a/25}` | `BarriersAreBlindToPurity`, `TheOccupiedWindowsLoseOneLogarithm` |
| Residual | weakest RH equivalents: one window, one point, positive proportion, any moment | `TheWidthIsReadInOneWindow`, `TheExponentOfTheMollifiedErrorIsRigid` |

## Positive survivors of the barrier no-go

The route barrier → `D_win` fails as an implication. Survivors:

1. **Last-scale law.** The defect of every normalized polynomial mollifier is set by the primes just above it, at rate `2θ` with mass `1/a`, and survives every short weight.
2. **Prime camera.** `Z_{y,δ}(t) + C(t) = O(1 + log t/δ)`, mean square `≪ T/c²`, uniform in width and centre. Separated dominant zeros: `≪ T L (4+α) e^{−2α}`.
3. **Turán camera.** Clusters of at most `N` zeros in the sector, with small outside mass: `≪_{c,N} T L e^{−2(1−4c)α}`.
4. **Near-line zeros cannot block.** Competitors at most `N` in the sector and small mass deeper than `A/L`: `≪_{c,N} T L e^{A−(1−4c)α}`, rate above `22/25`.

Paper proofs: the module docstrings carry them in full; each is formalized.

## Open

Fixed-depth `ε(A)`. Second moment of the Lorentzian mass. Comparably deep pairs at scale `1/(cL)`. Sharp second-moment rate. Barrier at the last scale. Closing the slope is RH.

## Log
- 2026-11-05 — created; README first draft written.
- 2026-11-06 — all items of §2.7.2 addressed in Lean; camera modules added; README complete.
