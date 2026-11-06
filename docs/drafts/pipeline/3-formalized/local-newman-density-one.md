# Vanishing normalized local Newman constant on a density-one set

- **ID:** B73-DENSITY-ONE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Obstacles summary §2.5.6](../../../reports/review-0511/obstacles-summary.md#256-route-zcg--the-saddle-on-almost-all-heights-b73)
- **Statement:** There is a measurable density-one set `S` with `localNewmanConstant X * log X → 0` as `X→∞` within `S`.

## Exact consequence

On the same set `S`, for every `κ>0` and every sufficiently large `X∈S`,
all zeros of `H_τ` with `|Re z−X|≤1` are real simultaneously for every
`τ≥κ/log X`. This uses the actual all-future-time local Newman constant.

## Proof

Fix `0<η≤1/8` and write `L=1+log(4T)`. Outside a set of measure `o(T)`
in `[T,2T]`, the zeta source has no zero on the fixed right-hand box and
has the polylogarithmic bounds of `TypicalZetaBoxBounds`. Throughout a
nearby height interval these give

`|F′(w)−aF(w)|≤B|F(w)|`, `a=α+iπ/4`, `α=log(X/(2π))/2`,

for `w≥2η`, where `F(w)=ξ(1/2+w+iX)` and `B=O_η(log log T)`.
The lower source interval has a relative bound polynomial in `log T`.
At `w=9/2` this model joins the unconditional distant-source estimate.

For `8η≤τα≤1`, put `u=y+2τα` and `P=|F(u)|exp(−τα²)`.
The literal half-Gaussian transform `Q(y)` and its derivative `D(y)` obey

`|Q(y)−Main(y)|≤P S₁`, `|D(y)−aQ(y)|≤P S₂`,

uniformly for `−4η≤y≤1/2`. For `4η≤y≤1/2`, also `|Q(−y)|≤P S₃`.
Here `|Main|=P exp(−τ(π/4)²)≥23P/25` when `τ≤1/8`.

The bounds `L≤8α` and `8η/α≤τ≤1/α` make all errors uniform:
`B√τ→0`; the local model error is `2q exp((1+q)²)`, `q=B√τ`;
the lower tail contains `exp(−25η²/τ)`, which absorbs its source and
inverse-heat factors; the far tail is bounded by
`O_η(α exp(α−α²))`. Consequently, eventually

`S₁≤1/5`, `S₂<18α/25`, `S₃≤1/2`.

Thus `|Q(y)|≥18P/25`. Near the axis, `Re(D(y) conjugate(Q(y)))>0`
makes `|Q(y)|>|Q(−y)|`. Away from the axis, the opposite-half bound
proves the same strict inequality directly. The identity
`H_τ(X+iy)=Q(−y)+conjugate(Q(y))` excludes every nonreal zero.

This covers all `τ≤1/8` with `8η≤τα≤1`. For `τα>1`, the global
large-height reality horizon overlaps this interval. For `τ≥1/8`,
the global Newman bound gives reality. Hence every later heat time
is covered.

A finite `η`-net of `[-1,1]` supplies the same control at every height
of a unit window. The bad windows lie in finitely many translates of
the typical-height exception, together with two bounded endpoint
strips. Their measure is still `o(T)`. For every good window,

`Λ_X≤16η/log((X−1)/(2π))`, hence eventually `Λ_X log X≤32η`.

Taking `η=min(ε/64,1/16)` proves density zero for every positive level
set `{X:Λ_X log X>ε}`. Dyadic-to-prefix summation gives the same result
on `[0,H]`.

To obtain one measurable set, let `B_n={X:f(X)>1/(n+1)}` for
`f(X)=Λ_X log X`. Choose `R_n` so `μ(B_n∩[0,H])≤2^(-n)H` for
`H≥R_n`, and set `C_n=B_n∩(R_n,∞)`, `E=⋃n C_n`.
For each `N`,

`E∩[0,H] ⊆ (B_N∩[0,H]) ∪ ⋃m(C_(N+m)∩[0,H])`.

The first term has density zero; the remaining union has measure at
most `2^(1−N)H` for every `H≥0`. Thus `E` has density zero. Its
measurable hull has the same measure on every bounded prefix, so
`S=(toMeasurable E)ᶜ` is measurable and has density one. On `S`,
`X>R_n` implies `0≤f(X)≤1/(n+1)` once `X≥1`, proving the limit.

Finally, a nonreal zero at heat `τ` in the unit window implies
`τ≤Λ_X`. This contradicts `Λ_X log X<κ≤τ log X`, giving the stated
all-future-time consequence.

## Lean status

The analytic bound and density-zero level-set theorem passed Lean with
only `propext`, `Classical.choice`, and `Quot.sound`:

- `ZeroConfigurationGeometry.eventually_localNewmanConstant_le_of_zetaPolylogTypicalWindow`.
- `ZeroConfigurationGeometry.eventually_volume_localNewman_scaled_gt_inter_Icc_le`.

The measurable extraction and both exact capstones passed Lean with the
same standard axioms:

- `ArithmeticHarmonicAnalysis.exists_measurable_densityOne_tendsto_zero_of_density_zero`.
- `ZeroConfigurationGeometry.exists_densityOne_localNewman_scaled_tendsto_zero`.
- `ZeroConfigurationGeometry.exists_densityOne_eventual_local_heat_reality`.

All supporting leaf modules and both capstones passed direct
`lake --old env lean` checks. Umbrella imports are wired.
