# The order of the verification height

- **ID:** A132
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §2.1; walls Σ171.

## Statement

There is `C` such that RH verified through `H(a) = exp(exp(C a))` gives Weil positivity on `[−a, a]` for every
`a ≥ 1`: `log log H(a) = O(a)`. (`windowHeight` of `WindowEntries` has `log log log windowHeight(a) ≍ a^{4/3}`.)

## Mechanism

`W(f,f) = κ⁻¹W(f,g) + ∫|h_f|²(1 − q²/κ)(μ + P_X)` must pay `D·∫_{|τ|≤T₁}|h_f|²`, `T₁ ≈ exp(68e^{a+2})`, by
values at verified zeros: `|h_f(τ)|² ≤ K Σ_{|γ|≤R}|h_f(γ)|² + O(48^{−4n})`, and `log log H = O(log log K)`.
`WindowEntries` interpolates once from nodes above the gap height, so `n ≍ T₁` and `K` is double exponential.
Here each `τ` is sampled from `n + 1` separated zeros in a window next to it, so `n ≍ (t_* + e^{2Y})/σ + log T₁`.
The window supply needs a gap theorem at resolution `σ ≍ 1/a` with test width `Y ≍ 1/σ`; the derivative minorant
gives it, since clusters of zeros only lower the form. The prolate count (`2e^{2a}` missing degrees of freedom below
`2πe^{2a}`) forces `K ≥ exp(c e^{2a}/a)` for any such sampling inequality, so `O(a)` is the order of this method.

## Proof: the derivative minorant

**Test.** `φ` a smooth bump, `0 ≤ φ ≤ 1`, `φ = 1` on `[−½, ½]`, support in `[−1, 1]`; `g(u) = φ(u/Y)`,
`g' = Y⁻¹φ'(·/Y)`. Then `ĝ(z) = Yφ̂(Yz)`, `ĝ'(z) = φ̂'(Yz) = −izĝ(z)`; `|φ̂(w)|, |φ̂'(w)| ≤ Be^{|Im w|}/(1+|Re w|)²`;
`‖g‖₂² = YE₀` (`E₀ ≥ 1`), `‖g'‖₂² = E₁/Y`. Write `t = −2πξ`, `x_ρ = γ − t`,
`D(ξ) = σ²W(S_ξg, S_ξg) − W(S_ξg', S_ξg')`.

**Zero side.** Let `0 < σ ≤ 1 ≤ Y`, RH for `|x_ρ| ≤ e^Y`, no zero with `|x_ρ| < σ`. At an on-line zero the
summand is `m(σ² − x²)|ĝ(x)|² ≤ 0`. At `|x| > e^Y` it is at most
`m(σ²Y² + 1)B²e^Y(1+Yx)^{−4} ≤ 16mB²Y^{−2}(1+x)^{−3}` (`e^Y ≤ x`). With `Σ m(1+|x_ρ|)^{−3} ≤ 5760 log(|t|+3)`:
`Re D ≤ 16·5760 B² Y^{−2} log(|t| + 3)`.

**Symbol side.** `W(S_ξf) = A_f(ξ) − Π_f(ξ)` for `f = g, g'`, and
`σ²Re A_g − Re A_{g'} = σ²P_g − P_{g'} + ∫(σ² − s²)|ĝ(s)|² μ(s + t) ds`. With `|μ(s+t) − μ(t)| ≤ D_μ|s|`,
`|s||ĝ|² ≤ B²Y(1+Y²s²)^{−1}`, `|s|·s²|ĝ|² = |s||ĝ'|² ≤ B²Y^{−1}(1+Y²s²)^{−1}` and Plancherel:
`σ²Re A_g − Re A_{g'} ≥ F·(L − 10) − πD_μB²(σ² + Y^{−2}) − 64e^YY²N²(1+|t|)^{−4}`,
`F = σ²YE₀ − E₁/Y`, `L = log(1 + |t|/4)`, `N = Σ_{k≤3}‖φ^{(k)}‖₁` (poles: `abs_re_pole_terms_heightShift_le_decay`).

**Gap theorem.** Take `σY = κ ≥ 1`, `κ² ≥ 2E₁`, `κ³ ≥ 2949120B²` (so `F ≥ σ²Y/2`, `σ²Y³ ≥ 2949120B²`). If
`L ≥ 40 + 32πD_μB²`, `|t| ≥ 1024e^YY³N²`, `‖Π_g‖ ≤ YE₀L/32` and `‖Π_{g'}‖ ≤ σ²YE₀L/32`, the symbol side gives
`Re D ≥ FL/4`, the zero side `Re D ≤ FL/8`: a zero lies within `σ` of `t`. No cluster assumption enters.

**Rare bad heights.** By the windowed Chebyshev bound (any test of support `[−Y, Y]`, windows of length
`≥ 2e^{2Y}`) with `V_g ≤ 4Y⁴E₀²(2+C₀)`, `V_{g'} ≤ 4E₁²(2+C₀)`, each bad set has density `≤ 1/80` once
`log(1 + t_*/4) ≥ C Y`. So `t_* = 4e^{C_*Y}`.

**Height.** `σ = nodeStep a/4`, `Y = κ/σ = 36·48⁴κ a`. Cut a window of length `10(m+1)·nodeStep ≥ 2e^{2Y}` into
`5(m+1)` slots of length `2·nodeStep`; good heights in the middle half-units give `4(m+1)` zeros with gaps
`nodeStep·|i − j|`. For `|τ| ≤ T₁` such a window lies within `12(m+1)·nodeStep` of `τ` (above `t_*`, or at `t_*` when
`|τ| < t_* ≤ (m+1)·nodeStep`), and the modulated Taylor–Lagrange bound gives `|h_f(τ)|² ≤ KΣ|h_f(γ)|² + O(48^{−4n})`
with `n = 4m + 3 ≍ (t_* + e^{2Y})/nodeStep + log T₁ = e^{O(a)}`, `K = e^{O(n)}`. `window_numeric` then needs
`b ≍ K^{−1/2}` and `H ≍ b^{−8}`: RH through `exp(exp(C a))` gives Weil positivity on `[−a, a]`.

## Lean

`exists_doubleExp_windowPositive` (`VerifiedHeightRungs/TheVerificationHeightIsDoubleExponential`): there is `C` with
RH verified through `exp(exp(C a))` ⇒ Weil positivity on `[−a, a]`, `a ≥ 1`. Modules: `TheDerivativeMinorant`
(test, decay, zero side `re_minorantForm_le_of_gap`), `TheDerivativeMinorantFindsZeros` (symbol side
`re_minorantForm_ge`, gap theorem `exists_zero_near_of_minorant`, window supply `exists_spread_zeros_minorant`),
`ThePrimePolynomialIsRarelyLarge` (windowed Chebyshev), `SeparatedZerosInEveryLongWindow` (slots),
`SpreadNodesControlTheTransform` (modulated Taylor–Lagrange), `LocalSamplingFromVerifiedZeros` (`spreadHeight`).
