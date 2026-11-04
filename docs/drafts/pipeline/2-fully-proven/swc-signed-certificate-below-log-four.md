# Resolution of Signed Window Certificates Below `log 4`

- **ID:** swc-signed-certificate-below-log-four
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.8
- **Statement:** Every variance-dropping odd pole-charged supersolution (`ω ∈ C²_c(ℝ)`) and odd theta-gauge outside-charge certificate (`translateSpan s α b`, including every shifted ground state `ω_a`) fails on windows of length `2c ∈ (273/200, log 4)`, and every nonnegative even theta gauge with positive tail mass fails the cosh-charged defect inequality on every bounded window; the mandatory retained term is the pole-charge variance `2V_s^S(u) = ∫∫_{S²} m_s(x)m_s(y)(u(x) − u(y))² dx dy`, and for every `0 < c < log 2` (`2c < log 4`), `ZetaWindowPositive c` is unconditionally equivalent to the retained-variance Doob–theta certificate in both parity sectors and to the prime-free half-window `{2, 3}` trivial-zero Hankel band `|𝓗_0(f) − w_2(f ⋆ f)(−log 2) − w_3(f ⋆ f)(−log 3)| ≤ W_∞(f)`.

## Goal
Resolve §2.8 ("Is there an exact signed certificate of Weil positivity on every window of length `< log 4`?") unconditionally in both directions:
1. Refute the natural variance-dropping signed certificate classes (`J_{Φω}(u) ≥ 0` with `ω · 𝒢_S(ω) ≥ 0`, odd theta-gauge outside-charge certificates, shifted ground state lower bounds, and cosh-charged positive-cone even theta gauges) strictly below `log 4`.
2. Identify the exact omitted term `2V_s^S(u)` (the pole jump conductance `4 sinh(x/2) sinh(y/2)` completing `J_{Φω}` into the odd light cone `c_−`) and establish the unconditional equivalence between `ZetaWindowPositive c` (`0 < c < log 2`), the retained-variance Doob–theta certificate, the prime-free half-window `{2, 3}` trivial-zero Hankel band, and the scaling-subsurface Hodge index and Künneth effectivity at aperture `c`, together with the sharp prime-free half-window boundary at `c = log 2` (`2c = log 4`) and convexity of the two-prime weight band.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/`, individual `lake --old env lean` checks green, `#print axioms` PASS

## Approach & Complete Proof (`[PROVED HERE]`)

### 1. Gauge-extension invariance and the universal two-profile `L^{1/2}` obstruction
1. **Local gauge-sum law.** For `ω, u ∈ C²_c(ℝ)` with `F = Φωu` odd (`evenPoleMoment F = 0`, `coshCharge ω S = 0` on `S = (−c, c)`), `markovEnergy_phiDoob_mul_eq_signedJump_add_defect` and the definition of `poleChargedDefect` give
   $$J_{\Phi\omega}(u) + \int_{\mathbb{R}} u(x)^2 \omega(x)\,\mathcal{G}_S(\omega)(x)\,dx = \operatorname{markovEnergy}(F) - 2\,\sigma_s(\omega, S)\int_{\mathbb{R}} u(x)^2\,\Phi(x)\omega(x)\sinh(x/2)\,dx.$$
   When `u` vanishes off `S`, both `σ_s(ω, S) = ∫_S Φω sinh(x/2)` and the weighted integral depend solely on `ω|_S`: modifying `ω` outside `S` transfers potential between `J_{Φω}(u)` and `∫ u²ω 𝒢_S(ω)` while leaving their sum invariant. For any non-compact odd theta gauge `ω = translateSpan s α b`, `fullZeroForm_thetaGauge_eq` gives the identical sum `J_M(u) + 2τ_s^S ∫ u²M sinh(x/2) = markovEnergy(F) − 2σ_s(ω, S) ∫ u²M sinh(x/2)`.
2. **Exact pole-conductance identity for `2V_s^S(u)`.** For any continuous weight `m` on `S = (−c, c)` and `u ∈ C²_c` vanishing off `S`,
   $$2\,\operatorname{chargeVariance}(m, S, u) = \int_S \int_S m(x)m(y)(u(x) - u(y))^2\,dx\,dy.$$
   For odd `M = Φω` and even `u`, folding `S = (−c, c)` to `(0, c)` gives `2V_s^S(u) = 4 ∫_0^c ∫_0^c M(x)M(y) sinh(x/2) sinh(y/2) (u(x) − u(y))² dx dy`, supplying the `2cosh((x+y)/2) − 2cosh((x−y)/2)` conductance that completes the folded Markov kernel into the odd light-cone conductance `c_−(x, y) = κ(|x − y|) − κ(x + y)`.
3. **Zero `H^{1/2}` capacity of the origin on odd `C²_c` profiles.** Given odd `F ∈ C²_c(ℝ)` supported in `[−c′, c′]` (`0 < c′ < c`), `F(0) = 0` and `|F(x)| ≤ K|x|`. Setting `d_ε(x) = −smoothPlateau 1 (x/ε) · F(x)` (`0 < ε ≤ 1/2`), `F_ε = F + d_ε` is odd, `C²_c`, vanishes on `[−ε, ε]` and outside `[−c′, c′]`, while `d_ε` is supported in `[−2ε, 2ε]` with `‖d_ε‖_1 = O(ε²)`, `‖d_ε‖_2² = O(ε³)`, and global Lipschitz constant `(4Λ + 1)K` independent of `ε`. By `SSHA.levyEnergy_le_lipschitz` and `SSHA.weilQuad_add_le`, `markovEnergy(F_ε) → markovEnergy(F)` and `∫ √(F_{1,ε}² + F_{2,ε}²)|sinh(x/2)| → ∫ √(F_1² + F_2²)|sinh(x/2)|` as `ε → 0⁺`.
4. **Universal two-profile `L^{1/2}` Cauchy–Schwarz bound.** If `F_1, F_2 ∈ C²_c(ℝ)` are odd, vanish on `[−ε, ε]` and outside `[−c′, c′]` (`0 < ε < c′ < c`), and `ω` is `C²` with `ω(x) sinh(x/2) > 0` on `(−c, c) \ {0}`, then `u_i(x) = F_i(x)/(Φ(x)ω(x))` (extended by `0` on `[−ε/2, ε/2]`) is even, `C²_c`, and vanishes off `S = (−c, c)`. Cauchy–Schwarz against `m_s = Φω sinh(x/2) > 0` on `S \ [−ε, ε]` yields
   $$\left(\int_S \sqrt{F_1(x)^2 + F_2(x)^2}\,|\sinh(x/2)|\,dx\right)^2 \le \sigma_s(\omega, S)\int_{\mathbb{R}} (u_1^2 + u_2^2) m_s,$$
   so `∑_{i=1}^2 (J_{Φω}(u_i) + ∫ u_i² ω 𝒢_S(ω)) ≤ M(F_1) + M(F_2) − 2(∫_S √(F_1² + F_2²)|sinh(x/2)|)²`. Passing `ε → 0⁺` removes the `[−ε, ε]` vanishing hypothesis.

### 2. Explicit two-profile refutation below `log 4` and even-sector obstruction
1. **Two-profile witness at `c_0 = 17/25` (`2c_0 = 34/25 = 1.36 ∈ (log 3, log 4)`).** On `u = x/c_0 ∈ [−1, 1]`, put
   $$G_1(x) = p_1(x/c_0), \quad G_2(x) = \frac{9}{2}\,p_2(x/c_0), \qquad p_1(u) = u\max(1 - u^2, 0)^2,\quad p_2(u) = u\left(u^2 - \frac{1}{4}\right)\max(1 - u^2, 0)^2.$$
   For `s ∈ [0, 2]`, `∫ G_i(x) G_i(x + c_0 s) dx = a_i² c_0 C_i(s)` with exact rational correlation polynomials `C_1` (degree 11) and `C_2` (degree 15) satisfying `D_i(0) = 0` (`D_i = C_i(0) − C_i`). Using the algebraic hyperbolic bound
   $$2\,\omega_{\mathrm{Levy}}(y) = \frac{1}{2\sinh(y/2)} + \frac{1}{2\cosh(y/2)} \le \frac{1}{y} + \frac{1}{2} - \frac{y}{24} - \frac{y^2}{16} + \frac{y^3}{576} + \frac{y^4}{128} \quad (y > 0),$$
   the tail antiderivative bound `Ω(y) = ∫_0^{e^{−y/2}} 2/(1 − t⁴) dt ≤ 2z + (2/5)z⁵/(1 − z⁴)` at `y = 34/25`, rational enclosures of `γ`, `π`, `log 2`, `log 3`, `√2`, `√3`, and the three Pythagorean chords `(105/137, −88/137)` on `[0, 7/20]`, `(24/25, −7/25)` on `[7/20, 1/2]`, and `(21/29, 20/29)` on `[1/2, 1]` with `sinh(z) ≥ z + z³/6`, we obtain `M(G_1) + M(G_2) − 2(∫ √(G_1² + G_2²)|sinh(x/2)|)² < −3.4 × 10⁻⁴ < 0`.
2. **Smoothing to `C²_c` on `(273/400, log 2)`.** Mollifying `G_1, G_2` by `CHMDDoobGraph.smooth · k` (`k ≥ 100`, radius `≤ 1/404 < 1/400`) preserves oddness, lands inside `[−273/400, 273/400]`, and preserves the strict inequality by `re_weilFullFunctional_smooth_tendsto` and dominated convergence. Hence for every `c ∈ (273/400, log 2)` (`2c ∈ (273/200, log 4)`), **no** odd pole-charged supersolution `ω ∈ C²_c(ℝ)` with `ω > 0` on `(0, c)` and `J_{Φω}(u) ≥ 0` on even `u ∈ C²_c((−c, c))` exists, and **no** odd theta-gauge outside-charge certificate (`J_M(u) + 2τ_s^S ∫ u²M sinh ≥ 0`, including `2S_a(u) − D_a(u) + 8τ_c(a) ∫_{x>0} u² m_a sinh ≥ 0` for any `a > 0`) holds on `(−c, c)`.
3. **Even-sector outside-cosh obstruction.** For any `c > 0` and any even theta gauge `ω = translateSpan s α b` with `M = Φω ≥ 0` and `∃ x₀, c < |x₀| ∧ 0 < M x₀` (in particular every nonzero nonnegative combination `α_j ≥ 0`), `τ_c^S = A/2 − coshCharge ω (−c, c) = ∫_{(−c, c)ᶜ} M cosh(x/2) > 0`. Since `twoSidedGenerator ω − Φ cosh(x/2) ω = −A Φ cosh(x/2)`, the cosh-charged defect on `S = (−c, c)` equals `−2τ_c^S Φ cosh(x/2) < 0` everywhere, violating the cosh-charged subsolution inequality wherever `ω(x) > 0`.

### 3. Sharp phase boundary at `log 4` and exact retained-variance / Hankel-band equivalences
1. **Sharp prime-free half-window boundary at `2c = log 4` (`c = log 2`).**
   - For `0 < c ≤ log 2` and every `C²` test `f` vanishing off `[−c, 0]`, `primeSum f = 0`, so `weilQuad f = archForm f + 2 coshHalfMoment f ^ 2 − 2 sinhHalfMoment f ^ 2` is purely archimedean-polar.
   - Conversely, for every `c > log 2`, a smooth nonnegative two-bump test supported in `(−c, 0)` achieves `primeSum f > 0`.
2. **Exact `{2, 3}` truncation of `centreCoupling` below `log 4`.** For `0 < c < log 2` and `f ∈ C²` vanishing off `[−c, 0]`, `selfConv f (−log n) = 0` for every `n ≥ 4`, so
   $$\mathcal{C}_0(f) = \mathcal{H}_0(f) - \frac{\log 2}{\sqrt{2}}(f \star f)(-\log 2) - \frac{\log 3}{\sqrt{3}}(f \star f)(-\log 3).$$
3. **Unconditional multi-way equivalence on every window `< log 4`.** For every `0 < c < log 2`:
   `ZetaWindowPositive c`
   `↔` retained-variance Doob–theta positivity in both sectors (`0 ≤ J_Φ(u) − 2V_c^S(u) − 2τ_even(c) ∫ u² Φ cosh` and `∀ a > 0`, `0 ≤ 2S_a(u) − D_a(u) + 8V_c^{(0,c)}(u) + 8τ_c(a) ∫_{x>0} u² m_a sinh` for all even `u ∈ C²_c` vanishing off `(−c, c)`)
   `↔` prime-free half-window `{2, 3}` trivial-zero Hankel band (`∀ f ∈ C²` on `[−c, 0]`, `|𝓗_0(f) − w_2(f ⋆ f)(−log 2) − w_3(f ⋆ f)(−log 3)| ≤ archForm f + 2 coshHalfMoment f ^ 2 − 2 sinhHalfMoment f ^ 2`)
   `↔` Markov–Hankel `{2, 3}` sector pair on `[−c, 0]`
   `↔` `(scalingSubsurface (realTestsAt c)).HodgeIndex`
   `↔` Künneth effectivity of `scalingSubsurface (realTestsAt c)`.
   Moreover, the admissible two-prime weight set `belowLogFourBandWeights c ⊆ ℝ × ℝ` is convex, and for `21/40 ≤ c < log 2` (`21/20 ≤ 2c < log 4`) it excludes `(0, 0)` and `(−w_2, 0)`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** On windows `S = (−c, c)` with `c ∈ (273/400, log 2)` (`2c ∈ (273/200, log 4)`), the outside-extension-invariant sum `∑_{i=1}^2 (J_{Φω}(u_i) + ∫ u_i² ω 𝒢_S(ω))` is bounded above uniformly over all positive odd gauges `ω` by `M(F_1) + M(F_2) − 2(∫_S √(F_1² + F_2²)|sinh(x/2)|)²`, which evaluates to `< −3.4 × 10⁻⁴ < 0` on the explicit smooth odd pair `(F_1, F_2)` obtained by mollifying `u(1 − u²)²` and `(9/2)u(u² − 1/4)(1 − u²)²` at `c_0 = 17/25`. In the even sector, positive outside cosh charge forces strict negativity of the cosh-charged defect of every positive-cone even theta gauge.
- **Strongest positive survivor:** Retaining the rank-one-per-lag pole variance `2V_s^S(u) = ∫∫_{S²} m_s(x)m_s(y)(u(x) − u(y))² dx dy` (which completes `J_{Φω}` into the odd light-cone conductance `c_−`) and `−2V_c^S(u)` gives an exact unconditional signed certificate template on every window `2c < log 4`, equivalent to the prime-free half-window `{2, 3}` trivial-zero Hankel band and to the scaling-subsurface Hodge index at aperture `c`, with `2c = log 4` proved to be the sharp prime-free half-window boundary.
- **New insight:** Non-compact gauge extensions outside `(−c, c)` (including all theta-gauge outside-charge slacks) cannot rescue variance-dropping supersolutions below `log 4`, because they leave `J_{Φω}(u) + ∫_S u²ω 𝒢_S(ω)` strictly unchanged; positivity on two orthogonal odd modes forces retention of the nonlocal pole-jump conductance `2V_s^S` alongside the trivial-zero Hankel squares.
- **Status:** Dependency-closed paper proof complete; proceeding directly to Lean 4 formalization in `GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/`.
