# The order of the verification height

- **ID:** A132
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §2.1; walls Σ171.

## Target

RH verified through `H(a)` with `log log H(a) = O(a)` gives Weil positivity on `[−a, a]`
(currently `windowHeight`, `log log log windowHeight(a) ~ c a^{4/3}`).

## Where the triple exponential comes from

`windowPositiveAt_of_rhVerifiedThrough` writes `W(f,f) = κ⁻¹W(f,g) + ∫|h_f|²(1 − q²/κ)(μ + P_X)`
and must control the mass of `h_f` on `|τ| ≤ T₁`, `T₁ = 4e^{E+2π} ≈ exp(4e^a)`, by values at
verified zeros. Two steps are each triple exponential:

1. **Gaps.** Nodes need a zero in every interval of length `σ = 48⁻⁴/(9a)`. The gap theorem
   (`exists_zero_near_of_onLine`) supplies this only above
   `gapHeight σ ≈ exp(c·e^{Y})`, `Y = gapScale σ ≍ σ^{−4/3}`: the test of width `Y` must beat
   the primes up to `e^Y`. So nodes start at `exp(exp(c a^{4/3}))`.
2. **Extrapolation.** One Taylor–Lagrange polynomial of degree `n ≈ (node height)/σ` covers
   `|τ| ≤ T₁` from those nodes, with constant `48^{2n}`.

## Why double exponential needs a new input

Splitting the range does not suffice. Above the gap-guarantee height `G` local Lagrange blocks
have polynomial constants, but `[0, G]` must be reached by extrapolation from nodes near `G`,
at cost `exp(c a G)`; `G` is at least double exponential because a Nyquist-type gap
(`< π/a`) is guaranteed by the RH gap bound `(2π + o(1))/log log t` only for
`log log t > 2a`, i.e. above `exp(e^{2a}) ≫ T₁`. Below `T* ≈ 2πe^{2a+1}` the zeros are
sub-Nyquist for type `a` (`N(T)` versus `2aT/π`), and the margin ceiling
`exp(11a/2 − πe^{2(a−2)})` is attained there.

So `log log H = O(a)` requires one of: maximal zero gaps `≤ (π − ε)/a` at heights
`exp(e^{O(a)})` below `T₁` (beyond the RH-conditional gap bound), a finite gap certificate on
`[e^{Ca}, 2T₁]` (a premise, not a theorem), or a positivity argument that does not sample the
low band at the zeros. None is in the corpus.

## What the margin bound must be

In `W(f,f) = κ⁻¹W(f,g) + ∫|h_f|²(1 − q²/κ)(μ + P_X)` the zero side must pay `D·∫_{|τ|≤T₁}|h_f|²`
up to a fixed fraction of `∫|f|²`: `∫_{|τ|≤T₁}|h|² ≤ K Σ_γ q(γ)²|h(γ)|² + c₀‖h‖²` on `PW_a`. Then
`b ≍ K^{−1/2}` and the tail `b⁻⁶H⁻⁴` give `log log H = O(log log K)`; so `K = exp(e^{O(a)})` is the
target. The prolate bound (`2e^{2a}` missing degrees of freedom below `T* = 2πe^{2a}`) shows
`K ≥ exp(c e^{2a}/a)`, so the order is right. Any single interpolation from nodes at height `G`
costs `exp(caG)`; `K` must come from local sampling. Local sampling needs separated zeros at
density `> a/π` in windows of bounded length: Counting alone cannot supply it: clusters of size `K = C log t/log log t` at spacing
`2πK/log t > π/a` are compatible with `S(t) ≪ log t/log log t`, and on such a lattice
`sin(πu/s)φ(u)` (`φ` of type `a − π/s`) vanishes at every zero.

The explicit formula excludes that adversary: for `h ∈ PW_a`,
`Σ_γ |h(γ)|² = ∫|h|²S/2π + poles − tail`, `S = log-density − 2P`, `P` the prime sum of length
`e^{2a}`. So at resolution `1/(2a)` the zero measure is the symbol, and a Beurling–Selberg
minorant of type `2a` (integral `2δ − π/a`) puts a zero in every interval of length `π/a + ε` wherever
the smoothed symbol is `≥ η log τ`: exactly Nyquist, so gap-based sampling stays borderline and
the margin is the smallest eigenvalue of the symbol form `∫|h|²S/2π + poles` on `PW_a`. The margin is then governed by the near-zero set of the smoothed symbol
in `[T*, T_a]`, i.e. by how closely `2P(τ)` can approach `log τ` there (simultaneous
approximation of `τ log p`, `p ≤ e^{2a}`). Missing: a lower bound `exp(−e^{O(a)})` for that
eigenvalue, i.e. quantitative Weil positivity at scale `a`; RH through `H` only gives `≥ −tail`.
Not in the corpus.

## Possible survivor

A test with Fourier decay of growing order in the gap theorem lowers `gapScale` from `σ^{−4/3}`
to `σ^{−1} log(1/σ)`, giving `log log log windowHeight(a) = O(a log a)`; still triple
exponential. Not formalized.

## Route to a double exponential (in progress)

The triple exponential comes from one global interpolation: `n ≥ max(T₁, gapHeight)/σ`, and
`gapHeight` is double exponential only because the gap theorem pays the prime polynomial by its
maximum `68e^{Y}` and the poles by `sinh Y` at every height. Local version:

1. **Rare bad heights.** `W(S_ξ g) ≥ (log(1+π|ξ|/4) − 10)‖g‖² − tails − Re Π_g(ξ)` with pole term
   `≤ 2e^Y B²/(1+2π|ξ|)⁴` (`zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial_decay`). The
   windowed variance law (`integral_windowed_sq_deviation_eq`, window width `r = e^{−2Y}/2`) and
   `V_g ≤ 4‖g‖⁴Y(2Y+C)` give, by Chebyshev, bad measure `≤ 1/16` of every `t`-window of length
   `2e^{2Y}` once `log t ≥ C₁Y`.
2. **Good heights carry zeros.** If `Re W(mod_t g) ≥ ‖g‖²L/2` and RH holds within `e^Y` of `t`, a zero
   lies within `σ` (zero side of `exists_zero_near_of_onLine`).
3. **Spread nodes.** Every `|τ| ≤ T₁` has `n+1` zeros, pairwise `≥ nodeStep` apart, within
   `8(n+1)·nodeStep`, for `n ≍ max(e^{C₁Y}, e^{2Y}, log T₁)/nodeStep`; Taylor–Lagrange around `τ` gives
   `|h(τ)|² ≤ K Σ_{γ∈S}|h(γ)|² + R`, `K = exp(O(n))`.
4. The rest of `re_W_nonneg_of_rhVerifiedThrough` is unchanged: `log log windowHeight = O(Y) = O(a^{4/3})`.

Lean status: formalized with `Y = κ a^{4/3}`: `exists_doubleExp_windowPositive`
(`VerifiedHeightRungs/TheVerificationHeightIsDoubleExponential`): there is `C` with RH verified through
`exp(exp(C a^{4/3}))` ⇒ Weil positivity on `[−a, a]`, `a ≥ 1`. Chain: `SpreadNodesControlTheTransform`
(modulated Taylor–Lagrange), `ZerosNearMostHeights` (windowed Chebyshev), `SeparatedZerosInEveryLongWindow`
(slots: `4(m+1)` separated zeros in windows of length `10(m+1)σ ≥ 2e^{2Y}` above `t_* = e^{O(Y)}`),
`LocalSamplingFromVerifiedZeros` (`spreadHeight`, window positivity).

## Route to `O(a)`: the derivative minorant (paper proof)

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

**Height.** `σ = nodeStep a/4`, `Y = κ/σ = 36·48⁴κ a`. The slot argument, local Taylor–Lagrange and
`window_numeric` are those of the `a^{4/3}` proof, with `n ≍ (t_* + e^{2Y})/σ + log T₁ = e^{O(a)}`,
`K = e^{O(n)}`: RH through `exp(exp(C a))` gives Weil positivity on `[−a, a]`.

Lean status: in progress.
