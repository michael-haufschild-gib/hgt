# Positivity does not certify 70% at bandwidth 4/3

- **ID:** positivity-seventy-percent-four-thirds
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/fable.md`, §12.1 row 3 and §12.3.
- **Statement:** There is a continuous even nonnegative form factor `F`, equal to `|α|`
  on `[-1,1]`, with nonnegative Fourier-dual pair density, for which
  `I(F,4/3)>7/45` and `frobeniusFormFactor F (4/3)>13/10`.
  Moreover, `F≥1` outside `[-1,1]` and `F−1` is integrable.

## Construction and proof

Put `w=1/10000`, `b=10001/10000` and

`P(x)=1−sin²(x)/3−sin⁴(x)/18−sin⁶(x)/36−5sin⁸(x)/288`.

Cusa–Huygens and the identity

`1−(1−c²)/2−(1−c²)²/8−(1−c²)³/16−5(1−c²)⁴/128−c`
`=(1−c)⁵(5c³+25c²+47c+35)/128`

give `sinc²(x)≤b²P(bx)` for every `b≥1`. Cusa–Huygens follows by three
derivatives from `x sin x≥0` on `[0,π]`; outside the central interval,
`|sin x|≤1` and `π>3` give the bound.

The constant Fourier coefficient of `P` is `3273/4096`. Its positive-frequency
coefficients are `p₁=991/9216`, `p₂=−49/6144`, `p₃=1/1024`,
`p₄=−5/73728`, and zero thereafter. Set

`r=1−b²·3273/4096`, `aₖ=b²pₖ+r(1−k/101)` for `1≤k≤100`.

Every `aₖ` is nonnegative and `a₁>61/200`. The nonnegative Fejér kernel gives

`1+2Σ aₖ cos(2kbx)=b²P(bx)+rK₁₀₀(2bx)≥sinc²(x)`.

Let `Λw(u)=max(1−|u|/w,0)` and

`F(α)=min(|α|,1)+Σ(aₖ/w)[Λw(α−kb)+Λw(α+kb)]`.

Its pair density is

`p(ξ)=1−sinc²(πξ)+2sinc²(πwξ)Σaₖ cos(2πkbξ)`.

Writing `q=sinc²(πwξ)∈[0,1]`, this is the convex combination of
`1−sinc²(πξ)` and `1+2Σaₖcos(2πkbξ)−sinc²(πξ)`, hence nonnegative.
The triangle Fourier transform proves `Fourier(F−1)=p−1` exactly.
The first spike and the baseline alone give

`I(F,4/3)≥1/18+(4/3−b−w)a₁>1/18+(4/3−b−w)·61/200>7/45`.

## Lean and scope

- `TransThresholdPairCorrelation/PeriodicSincMajorant.lean`:
  `sinc_sq_le_scaled_periodicMajorant`, `periodicSincMajorant_fourier`.
- `TransThresholdPairCorrelation/FejerSpikePairDensity.lean`:
  `positivity_does_not_reach_seventy_percent_at_four_thirds`.
- Direct `lake --old env lean` checks passed; both modules imported by the umbrella.
- **Positive survivor:** explicit continuous admissible Fourier pairs with large first-spike
  mass, and the global dilated periodic majorant that preserves positivity under triangular
  smoothing. Both construction and majorant are formalized.
- **Remaining scope:** this settles bandwidth `4/3`, not every bandwidth. A fixed integrable
  perturbation has Frobenius value tending to one, so this witness cannot close the
  all-bandwidth question.
