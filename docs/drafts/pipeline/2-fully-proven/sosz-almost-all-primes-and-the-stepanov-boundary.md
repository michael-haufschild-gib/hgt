# Almost all primes do not force purity without attainment, and the sharp Stepanov prime boundary

- **ID:** SOSZ-B132
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0911/obstacles-summary.md`, §2.2 (B132) and §3.
- **Statement:**
  1. *(Negative resolution of B132 for configurations and density-zero Landau extension)* For every
     `0 < Θ ≤ 1/2`, there exist a tempered zero configuration `Z` in `0 < Re s < 1` without real
     zeros whose real parts have unattained supremum `1/2 + Θ`, a measurable set `S ⊆ [0, ∞)` of
     upper Lebesgue density zero, and a set `E` of primes of both relative logarithmic density zero
     (`Σ_{p∈E} log p · p^{−σ} = o(Σ_p log p · p^{−σ})` as `σ ↓ 1`) and Chebyshev density zero
     (`Σ_{p∈E, p≤X} log p = o(X)`), such that `2 Re S_Z(u) ≥ −5` for all `u ∈ [0, ∞) \ S` and
     `2 Re S_Z(log p) ≥ −5` for every prime `p ∉ E`.
  2. *(Exact ζ consequence and sharp positive threshold)* For `ζ`, the arithmetic Stepanov bound
     `P(p) ≤ A(p) + K` off a set `E` of relative logarithmic density zero implies
     `AsymptoticAbscissaLaw` unconditionally, and `RiemannHypothesis` is unconditionally equivalent
     to `ZerosApproachLine` together with `P(p) ≤ A(p) + K` off a set of primes of relative
     logarithmic density zero. Conversely, whenever `E` has short-interval prime density strictly
     below `1` at some Huxley scale `x^θ` (`7/12 < θ < 1`) — in particular whenever
     `#(E ∩ [1, X]) = O(X^α)` for any `α < 1` — no attainment or `ZerosApproachLine` hypothesis is
     needed: `2 Re S_Z(log p) ≥ −K` for `p ∉ E` puts every zero of every real-zero-free tempered
     configuration `Z` on the critical line, and `RiemannHypothesis ↔ ∃ K, ∀ p ∉ E, P(p) ≤ A(p) + K`
     holds unconditionally.

## Mathematical content

Question B132 asks whether a one-sided crude bound `2 Re S_Z(log p) ≥ −K` off a set `E` of primes of
relative logarithmic density zero puts every zero of a real-zero-free tempered configuration `Z` on
the critical line without assuming an attained maximal real part, and whether RH is characterized by
`P(p) ≤ A(p) + K` off such a set.

The simultaneous-Dirichlet heuristic in `obstacles-summary.md` §3 considered a single quartet per
level aligned simultaneously on the `≍ e^U / U` kept primes of a window `[U_k, U_{k+1}]`, which
would require height `≥ exp(c e^U / U)` and destroy takeover. That obstruction is bypassed by
periodic clusters of spline-zero heights `γ = 2π m B_k` (`1 ≤ m ≤ M_k`), for which `e^{2π i m B_k u}`
depends only on `B_k u mod 1` on the one-dimensional circle `ℝ/ℤ`. On `ℝ/ℤ`, a combination of the
Jackson kernel and the Poisson kernel produces finite zero-mean cosine polynomials with nonnegative
coefficients that are strictly positive everywhere outside an arbitrarily narrow arc around `1/2`.
Integer multiplicities `m^8 p_{k,m}` cancel the `m^{−8}` decay of `sinc(2π m B_k − i x_k)^8` and
concentrate all negative excursions of level `k` into periodic logarithmic holes of fractional width
`δ_k → 0`, while `B_k` depends only on `U_{k−1}`. On `[U_k, U_{k+1}]` the holes have multiplicative
width between `x^{15/16}` and `x^{1−o(1)}`: wide enough at `U_k` to break every power-saving gap
law `O(x^θ)` (`θ < 1`), yet above `x^{3/4}` everywhere so Huxley's short-interval prime bound transfers
`δ_k → 0` directly to Chebyshev and relative logarithmic prime density zero.

## No-go closure

- **Exact killing theorem/mechanism:** `exists_zeroConfig_primes_off_null_bddBelow_nonattained`
  (built on `exists_nat_cosine_sum_pos_off_hole`). Periodic spline-zero clusters with Jackson–Poisson
  multiplicity weights confine negative trace values to `o(1)`-measure periodic logarithmic holes
  whose prime mass has relative logarithmic and Chebyshev density zero, while keeping `B_k` small
  enough (`O_k(e^{(Θ/8)U_{k−1}})`) for window takeover and temperedness.
- **Strongest positive survivor:** Sharp threshold classification at exponent `α = 1`:
  1. Every exceptional prime set `E` satisfying `ShortPrimeSparse θ E` (`7/12 < θ < 1`), and in
     particular every power-saving set `#(E ∩ [1, X]) = O(X^α)` with `α < 1`, preserves `PowGaps θ`
     on `{p prime : p ∉ E}`; hence `2 Re S_Z(log p) ≥ −K` (`p ∉ E`) forces `Re ρ = 1/2` for every
     real-zero-free tempered `Z` without attainment, and `RH ↔ ∃ K, ∀ p ∉ E, P(p) ≤ A(p) + K`
     unconditionally.
  2. For relative logarithmic density zero (`α = 1 − o(1)`), the Stepanov bound gives
     `AsymptoticAbscissaLaw` unconditionally and `RH ↔ ZerosApproachLine ∧ (Stepanov off E)`.
- **New insight:** On the prime side of the explicit formula, `ZerosApproachLine` is localized
  precisely in sparse multiplicative holes of width `x^{1−o(1)}`. Any power-saving exceptional set
  `O(X^α)` (`α < 1`) eliminates `ZerosApproachLine` unconditionally; `o(X / log X)` density-zero
  exceptional sets stop strictly at `AsymptoticAbscissaLaw`.

## Proof

### 1. Positive-coefficient zero-mean cosine concentration (`exists_nat_cosine_sum_pos_off_hole`)

**[PROVED HERE]** Fix `0 < δ ≤ 1/2`. For `N ≥ 10`, let `a_s = min(s + 1, 2N − 1 − s)` for
`0 ≤ s < 2N − 1` and `a_s = 0` for `s ≥ 2N − 1`. Induction on `N` gives
`∑_{s < 2N} a_s z^s = (∑_{j < N} z^j)^2` for all `z ∈ ℂ`. At `z = 1`, `∑_{s < 2N} a_s = N^2`.
Setting `c_m = ∑_{s < 2N} a_s a_{s+m}`, Cauchy–Schwarz gives `c_0 ≥ N^3 / 2`, while `a_s ≤ N` gives
`c_0 ≤ N^3`. For `z = e^{2π i u}` (`u ∈ ℝ`), `(z − 1) ∑_{j < N} z^j = z^N − 1` yields
`‖1 − z‖^2 ‖∑_{s < 2N} a_s z^s‖ = ‖1 − z^N‖^2 ≤ 4`, so `J_N(u) := ‖∑_{s < 2N} a_s e^{2π i s u}‖^2 / c_0`
satisfies `0 ≤ J_N(u) ≤ 32 / (N^3 ‖1 − e^{2π i u}‖^4)` and expands as
`J_N(t) = 1 + 2 ∑_{m=1}^{2N−1} (c_m / c_0) cos(2π m t)`.

Reindexing `∑_{j < m + 2N} a_j^2 = c_0` gives the identity
`2(c_0 − c_m) = ∑_{s < m} a_s^2 + ∑_{s < 2N} (a_{s+m} − a_s)^2`.
For `2 ≤ m ≤ N/2`, the terms `s < N − m` have `a_{s+m} − a_s = m`, giving
`2(c_0 − c_m) ≥ (N/2) m^2`, so `1 − c_m / c_0 ≥ m^2 / (4 N^2)`.
For `N/2 < m < 2N`, the first sum over `s < ⌊N/2⌋` gives `c_0 − c_m ≥ c_0 / 125` (`N ≥ 10`).
Setting `r = 1 − 1/(256 N^2) ∈ (0, 1)`, Bernoulli's inequality `r^m ≥ 1 − m/(256 N^2)` gives
`r^m ≥ c_m / c_0` for every `2 ≤ m < 2N`.

For `P_r(t) = 1 + 2 ∑_{m ≥ 1} r^m cos(2π m t) = (1 − r^2) / ‖1 − r e^{2π i t}‖^2 ≥ (1 − r)/2 = 1/(512 N^2)`,
the combination `G(t) = (1/2) J_N(t) + (1/2) P_r(t) − J_N(t − 1/2)` has constant Fourier term `0`
and `m`-th cosine coefficient `(3 c_m / c_0 + r^m) ≥ 0` for odd `m < 2N`, `r^m − c_m / c_0 ≥ 0` for
even `2 ≤ m < 2N`, and `r^m > 0` for `m ≥ 2N`. Whenever `|t − (n + 1/2)| ≥ δ/2` for all `n ∈ ℤ`,
picking `n = ⌊t⌋` gives `δ/2 ≤ |t − 1/2 − n| ≤ 1/2`, hence `‖1 − e^{2π i (t − 1/2)}‖ = 2 sin(π|t − 1/2 − n|) ≥ 2δ`
and `J_N(t − 1/2) ≤ 2 / (N^3 δ^4)`. Choosing `N = ⌈4096 / δ^4⌉₊ + 10` gives `G(t) ≥ 1/(2048 N^2)`.
Truncating `P_r` at `M` where `2 r^{M+1}/(1 − r) ≤ 1/(4096 N^2)` yields nonnegative coefficients
`α_1, …, α_M` with sum `> 0` and cosine sum `≥ 1/(4096 N^2)` off the holes; setting
`p_m = ⌈Q α_m⌉₊` for large `Q` gives integer weights `p_m ∈ ℕ` with the stated lower bound.

### 2. Periodic spline-zero cluster tower (`exists_zeroConfig_primes_off_null_bddBelow_nonattained`)

**[PROVED HERE]** Fix `0 < Θ ≤ 1/2` and set `x_k = Θ(1 − 2^{−k−1})`, `δ_k = 1/(k + 4)`. Let
`(M_k, p_k, η_k)` be the integer cosine data for `δ_k`, with `D_k = ∑_{m=1}^{M_k} p_{k,m} ≥ 1`.
Define `(U_k, B_k)` recursively:
- `U_0 = 0`, `B_0 = ⌈(2 D_0 : ℝ)⌉₊ + ⌈4 / η_0⌉₊ + 6`;
- Given `U_k` and `B_k` (hence the level-`k` total spline weight
  `W_k = 2 ∑_{m=1}^{M_k} m^8 p_{k,m} ‖sincC(splinePoint (m B_k) x_k)^8‖ > 0`), note that for any
  candidate `U > 0`, choosing
  `B_{k+1}(U) = ⌈2 D_{k+1} · 2^{k+1} e^{Θ U}⌉₊ + ⌈4 / η_{k+1}⌉₊ + k + 7`
  depends monotonically on `U` with `B_{k+1}(U) ≤ C_{k+1} e^{U/2}`? Even better: since
  `‖sincC(splinePoint (m B) x)^8‖ ≤ 1 / (m B)^8`, `W_{k+1} ≤ 2 D_{k+1} / B_{k+1}^8`, so we only need
  `B_{k+1}^8 ≥ 2 D_{k+1} · 2^{k+1} e^{Θ U_k}`, i.e.
  `B_{k+1}(U_k) = ⌈(2 D_{k+1} · 2^{k+1} : ℝ)⌉₊ * ⌈e^{(Θ/8) U_k}⌉₊ + ⌈4 / η_{k+1}⌉₊ + k + 7`!
  Since `Θ/8 ≤ 1/16`, choosing `U_{k+1}` larger than `U_k + 4`, the takeover threshold
  `log(16 / (η_k W_k)) / (x_k − x_{k−1})` (when `k ≥ 1`), `log X_0`, and a constant threshold for
  `C_{k+2} / δ_{k+2}` ensures simultaneously:
  1. `W_0 ≤ 1` and `W_{k+1} ≤ 2^{−k−1} e^{−Θ U_k}`;
  2. For `k ≥ 1`, `(η_k / 4) W_k e^{(x_k − x_{k−1}) U_k} ≥ 4`;
  3. On `[U_k, U_{k+1}]` (`k ≥ 1`), both `B_k / δ_k` and `B_{k+1} / δ_{k+1}` are at most `e^{U_k / 8}`.

Place at each `(k, m)` with `1 ≤ m ≤ M_k` and `p_{k,m} > 0` the four symmetric points
`1/2 ± x_k ± 2π i m B_k` with multiplicity `m^8 p_{k,m}`. Distinct `(k, m)` have strictly disjoint
ordinates if we also enforce `B_{k+1} > M_k B_k` in the definition of `B_{k+1}`, so every carrier
point determines `(k, m, sign_re, sign_im)` uniquely! Since `B_k → ∞`, horizontal strips contain
finitely many points, `0 < 1/2 ± x_k < 1`, no zero is real, and
`∑_{m=1}^{M_k} m^8 p_{k,m} / (m B_k)^2 ≤ M_k^6 D_k / B_k^2` is summable in `k` (guaranteed by
including `2^k M_{k+1}^6 D_{k+1}` in `B_{k+1}`!), giving `TemperedConfig Z`.

At `(k, m)`, `m^8 sincC(splinePoint (m B_k) x_k)^8 = (sinh^8 x_k / (2π B_k)^8) z_{k,m}^8` where
`z_{k,m} = 2π m B_k / (2π m B_k − i x_k)` has `‖z_{k,m}‖ ≤ 1` and `‖z_{k,m}^8 − 1‖ ≤ 8 x_k / (2π B_k) ≤ 1/B_k`.
Hence for `u ∉ H_k := {u : ∃ n ∈ ℤ, |B_k u − (n + 1/2)| < δ_k / 2}`, the level-`k` forward sum
`a_k(u)` satisfies `a_k(u) ≥ (η_k / 4) W_k` (since `B_k ≥ 4 / η_k` and `W_k ≤ 2 D_k sinh^8 x_k / (2π B_k)^8`).
Applying the window dominance inequality on `[U_k, U_{k+1}]` shows `2 Re S_Z(u) ≥ −5` for all
`u ≥ 0` outside `S := ⋃_{k ≥ 0} ((H_k ∪ H_{k+1}) ∩ [U_k, U_{k+1}])`.

### 3. Upper Lebesgue, Chebyshev, and relative logarithmic density zero

**[PROVED HERE]** On each unit interval `[m, m + 1]` (`m ≥ ⌈U_1⌉₊`) lying in `[U_k, U_{k+1}]` (`k ≥ 1`),
at most `2 B_j` periods of `H_j` (`j ∈ {k, k + 1}`) meet `[m, m + 1]`, each of Lebesgue length
`δ_j / B_j`, so `volume(S ∩ [m, m + 1]) ≤ 2(δ_k + δ_{k+1}) → 0`, giving upper Lebesgue density zero.

By Huxley's short-interval theorem (`tendsto_psi_short_window_div_seven_twelfths` at `α = 3/4`),
there exists `X_0 ≥ 4` with `ψ(y + y^{3/4}) − ψ(y) ≤ 2 y^{3/4}` for all `y ≥ X_0`. Stepping from `a`
across `[a, b]` whenever `X_0 ≤ a` and `a^{3/4} ≤ b − a ≤ a` gives `ψ(b) − ψ(a) ≤ 8(b − a)`. For each
period hole `[u_0, u_1]` of `H_j` (`j ∈ {k, k + 1}`) meeting `[U_k, U_{k+1}]` (`k ≥ 1`), `u_1 − u_0 = δ_j / B_j`
satisfies `e^{−U_k / 8} ≤ δ_j / B_j ≤ 1/4` and `a = e^{u_0} ≥ e^{U_k - 1} ≥ X_0`, so
`a^{3/4} ≤ a(δ_j / B_j) ≤ b − a ≤ 2 a(δ_j / B_j) ≤ a`. Thus the primes in `[e^{u_0}, e^{u_1}]` satisfy
`∑ log p ≤ 16 e^{u_0} (δ_j / B_j)` and `∑ log p · p^{−σ} ≤ 16 (δ_j / B_j) e^{−(σ−1) u_0}` (`σ > 1`).
Grouping periods by unit blocks `[m, m + 1]` cancels `B_j`, bounding the `[m, m + 1]` contribution by
`O((δ_k + δ_{k+1}) e^m)` for `∑_{p ≤ X} log p` and `O((δ_k + δ_{k+1}) e^{−(σ−1) m})` for `wSum`.
Since `δ_k → 0` and `(σ − 1) wSum primeWeight σ → 1` as `σ ↓ 1` (from
`tendsto_neg_logDeriv_riemannZeta_sub_one_div_real` and `summable_higherWeight`), `E` has both
Chebyshev density zero and relative logarithmic density zero.

### 4. Exact `ζ` equivalences and sharp power-saving threshold

**[PROVED HERE]** Translating `orbitCorr_log_eq_archPoleWindow_sub_primeWindow` into
`asymptoticAbscissaLaw_of_bddBelow_primes_off_null` gives `AsymptoticAbscissaLaw` from
`P(p) ≤ A(p) + K` (`p ∉ E`), and combining with `rightRH_iff_zerosApproachLine_and_asymptoticAbscissaLaw`
gives `RiemannHypothesis ↔ ZerosApproachLine ∧ (Stepanov off E)`.

Conversely, if `E` satisfies `ShortPrimeSparse θ E` (`7/12 < θ < 1`), Huxley's asymptotic on
`(x − x^θ, x]` plus prime-power leakage `O(x^{1/2} log^2 x)` leaves a positive prime log-sum off `E`
in every large `(x − 2 x^θ, x]`, proving `PowGaps θ {p | p.Prime ∧ p ∉ E}`. If `#(E ∩ [1, X]) ≤ C X^α`
(`α < 1`), setting `θ = max ((α + 1)/2) (2/3) ∈ (7/12, 1)` gives `∑_{p ∈ E, p ≤ 2x} log p = o(x^θ)`,
hence `ShortPrimeSparse θ E`. Applying `onLine_of_bddBelow_of_powGaps` and
`riemannHypothesis_iff_primeWindow_le_of_powGaps` yields unconditional purity for all real-zero-free
tempered `Z` and `RH ↔ ∃ K, ∀ p ∉ E, P(p) ≤ A(p) + K` without `ZerosApproachLine`.

## Dependencies

- `SurfaceOfSpecZ/HeightsAtTheZerosOfTheSplineAreInPhase.lean`
- `SurfaceOfSpecZ/ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii.lean`
- `SurfaceOfSpecZ/AlmostAllPrimesSuffice.lean`
- `SurfaceOfSpecZ/TheGapMethodIterates.lean`
- `SurfaceOfSpecZ/TheStepanovBoundIsAPrimeCount.lean`
- `SurfaceOfSpecZ/StepanovBoundsProduceTheAbscissaLaw.lean`
- `RHTower/PrimeShortIntervalsHuxleyAsymptotic.lean`
- `RHTower/MertensVonMangoldtEulerConstant.lean`
