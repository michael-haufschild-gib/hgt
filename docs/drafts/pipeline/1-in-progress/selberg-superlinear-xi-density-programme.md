# Superlinear real-Xi zero density (Selberg's positive-proportion input) in Lean

- **ID:** selberg-superlinear-xi-density-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, classical) → target THEOREM (Lean)
- **Source:** section 4 of `prime-modulated-weyl-idealizer-collapse-on-xi-sampling`
- **Statement:** `RHTower.SuperlinearSamples RHTower.xiRealDivisor`, i.e. for every `c` there is a
  height `T ≥ 1` with more than `c·T` distinct real zeros of `Ξ` in `[−T, T]`.

## Goal

This is the single named literature input of section 4 of the sampling-idealizer card: Selberg
(1942) `N₀(T) ≫ T log T`, equivalently Conrey's simple-zero refinement, combined with
Riemann–von Mangoldt.  Closing it unconditionally in Lean removes the last cited paper input from
equation `(23)` of that card.

Note the target is strictly weaker than Selberg's theorem in three separate ways, and the slack is
large enough to matter:

1. `SuperlinearSamples` is a **limsup** statement — it needs one window per rate `c`, not a bound
   valid for all large `T`;
2. it needs only **superlinear** growth `limsup N₀(T)/T = ∞`, not `≫ T log T`; a bound
   `N₀(T) ≫ T log log T` or `T (log T)^{1/100}` suffices;
3. it needs **no proportion** of `N(T)`, so no constant has to beat `1` anywhere; in particular the
   Levinson threshold `(1/R) log L(T) < 1` may be missed by `1 − o(1)`.

It is, however, strictly stronger than Hardy–Littlewood `N₀(T) ≫ T`, so it is not reachable from
the tree's Hardy machinery alone (see the dead ends below).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, axiom-clean
- [ ] 3 → 4  publication-ready

## What is already Lean-certified (2026-08-18)

The combinatorial and bookkeeping half of the whole programme is closed unconditionally, and the
target is reduced to a single named analytic `Prop`.

`formal/GaloisForLFunctions/HTGeometry/GridCancellationZeroCount.lean`

- `sign_constant_of_no_interior_zero` — a continuous real function without interior zeros on a
  cell has constant strict sign there.
- `integral_abs_le_abs_integral_of_no_interior_zero` — hence on such a cell the absolute mass
  equals the modulus of the signed integral.
- `exists_zero_of_abs_integral_lt` — **the cancellation atom**: `|∫_u^v f| < ∫_u^v |f|` forces an
  interior zero.
- `exists_finset_zeros_card_mul_ge` — **the grid count**: for a uniform grid of mesh `H` on
  `[a, a+NH]`, if `L ≤ ∫|f|`, `∑_j |∫_{I_j} f| ≤ Bsum` and `∫_{I_j}|f| ≤ Mx` for every cell, then
  `f` has a finite set of distinct interior zeros of cardinality at least `(L − Bsum)/Mx`.
  This is the sharp device: on a zero-free cell the two masses coincide, so the entire surplus of
  absolute mass over the summed cancellation is carried by the cells that do contain a zero.

`formal/GaloisForLFunctions/RHTower/XiSuperlinearFromCancellation.lean`

- `continuous_Xi_real`, `xi_eq_zero_iff_mem_xiRealDivisor`,
  `card_le_samplingCount_xiRealDivisor` — the bridge from a Finset of real `Ξ`-zeros in a window to
  `samplingCount xiRealDivisor`, using the tree's `locallyFiniteSamples_xiRealDivisor`.
- `GridCancellationSurplus f` — **the named remaining input**:
  ```
  ∀ c, ∃ a H N L Bsum Mx, 0 < H ∧ 0 ≤ a ∧ 1 ≤ a + N·H ∧ 0 < Mx ∧
    L ≤ ∫_a^{a+N H} |f| ∧ ∑_{j<N} |∫_{I_j} f| ≤ Bsum ∧ (∀ j<N, ∫_{I_j} |f| ≤ Mx) ∧
    c·(a + N H)·Mx < L − Bsum
  ```
- `superlinearSamples_xiRealDivisor_of_grid_cancellation` — for **any** continuous `f : ℝ → ℝ`
  whose zeros are `Ξ`-zeros (`Ξ` itself, `Ξ` times a positive weight, a mollified Hardy function,
  a clamp of any of these), `GridCancellationSurplus f → SuperlinearSamples xiRealDivisor`.
- `clampAt`, `abs_clampAt_le`, `clampAt_eq_zero_iff`, `integral_abs_clampAt_le`,
  `superlinearSamples_xiRealDivisor_of_clamped_grid_cancellation` — the two-sided clamp at height
  `δ` keeps every zero of `Ξ` and makes the cell bound `Mx = δ H` **automatic**, so the clamped
  reduction has only two analytic inputs instead of three.
- `xiSamplingIdealizer_collapse_of_grid_cancellation` — equation `(23)` of the parent card with the
  Selberg citation replaced by `GridCancellationSurplus`.

All declarations are axiom-clean (`propext, Classical.choice, Quot.sound`).

## Why the grid device is the right target: the scale bookkeeping

Fix a window `[T, 2T]` and mesh `H`.  Write `f = Z·w` for Hardy's `Z` and a positive weight `w`
(so the zeros are the `Ξ`-zeros).  Then:

- cancellation inside a cell requires `H` to be at least the oscillation scale of `Z`, which is
  `2π/log T`.  For `H ≪ 1/log T` one has `∫_{I_j} |f| ≈ |∫_{I_j} f|` cell by cell and the surplus
  `L − Bsum` degenerates to `0`;
- with `H ≍ 1/log T` the number of cells is `≍ T log T`.  If `Mx` is comparable to the *average*
  cell mass `L/#cells`, then `(L − Bsum)/Mx ≍ (1 − Bsum/L)·T log T`;
- so **any** surplus fraction `1 − Bsum/L ≫ 1/ω(1)` gives `N₀ ≫ T log T/ω(1)`, which is
  superlinear.  Selberg's `1 − Bsum/L ≫ 1` is far more than needed.

The role of the mollifier `w = |M(1/2+it)|²` is exactly to make `Mx` comparable to the average
cell mass — without it the large values of `|ζ(1/2+it)|` make `max_j ∫_{I_j}|f|` far exceed the
mean and the count collapses.  The clamp `clampAt δ` is an elementary alternative that forces
`Mx ≤ δ H` at the cost of destroying the Dirichlet-series structure of `Bsum`; both routes are
available through the general reduction, which is why the reduction is stated for arbitrary `f`.

## Remaining analytic inputs (this is the open part)

Target: `GridCancellationSurplus f` for `f(t) = Z(t)·|M(1/2+it)|²` with `M` a Dirichlet polynomial
of length `X = T^θ` and Möbius-type coefficients, mesh `H ≍ 1/log T`, window `[T, 2T]`.

- **(S1) mollified absolute-mass lower bound.**  `∫_T^{2T} |Z(t)| |M(1/2+it)|² dt ≫ T log T`.
  Route: mollified second moment `∫ |ζM|² ≍ T` (lower bound) together with the mollified fourth
  moment upper bound, via `∫|g| ≥ (∫|g|²)^{3/2}/(∫|g|⁴)^{1/2}`.
  Tree status: `RHTower/Sieve/InghamMollifierSecondMoment.lean` has an `O(X + V log X)` **upper**
  bound; `RHTower/DpolyBallFloor.lean` has both a critical-line Dirichlet-polynomial second-moment
  **lower** (`dirichlet_line_main_moment_lower_bound`) and **upper** bound;
  `RHTower/Sieve/InghamCriticalMoment.lean` + `SmoothAFEZetaSquareInghamCriticalMoment*.lean`
  carry the critical-line fourth moment with polylog budgets.  The missing piece is the
  *cross* moment `∫ |ζ M|²` with the AFE error handled, not either factor alone.
- **(S2) grid cancellation upper bound.**
  `∑_{j<N} |∫_{I_j} Z(t)|M(1/2+it)|² dt| ≤ (1 − δ) ∫_T^{2T}|Z||M|²` for some `δ ≫ 1/ω(1)`.
  Route: expand `|M|² = ∑_{m,n≤X} a_m a_n (mn)^{-1/2}(m/n)^{-it}` and use the twisted Hardy
  integrals `∫_{I} Z(t)(m/n)^{-it} dt`; the stationary phase of `θ(t) − t log(m/n)` sits at
  `√(t/2π) ≈ m/n`, so for `X` small compared with `√T` every cell integral is off-stationary and
  gains.  This is the genuinely hard estimate and is Selberg's computation.
  Tree status: `RHTower/HardyZ.lean`, `RHTower/HardyZPhaseAsymptotic.lean` own the exact polar
  decomposition `ζ(1/2+it) = e^{-iθ(t)} Z(t)`; `RHTower/SmoothAFEZetaExact.lean` owns a Gaussian
  smoothed exact AFE.  No stationary-phase lemma for the twisted Hardy integral exists yet.
- **(S3) uniform cell bound.**  `∫_{I_j}|Z||M|² ≤ Mx` with `Mx ≍ (∫_T^{2T}|Z||M|²)/N`.
  Route: short-interval mollified second moment, or bypass entirely with `clampAt` (already Lean,
  see above) at the cost of making (S2) harder.

## Dead ends already ruled out (do not re-attempt)

- **Hardy's theta-source blow-up alone.**  The tree owns Hardy's theorem
  (`RHTower.exists_Xi_zero_gt`) and the boundary singularity of the theta source at `|Im u| = π/2`.
  That mechanism, pushed to its quantitative limit by Hardy–Littlewood, gives a sign change in
  every interval of length `T^{1/4+ε}`, hence `N₀(T) ≫ T^{3/4−ε}`: **sublinear**, so it cannot
  reach the target.
- **Positive-definiteness of `Ξ`.**  `Ξ = 𝓕Φ` with `Φ = xiThetaSchwartzSource > 0`
  (`RHTower/XiCSchwartzRestriction.lean`), so `Ξ` is a positive-definite function.  Positive
  definiteness alone imposes no zero density: a Gaussian source gives a zero-free transform, and
  Fejér/`sinc²` sources give zero sets of linear density.  No route through Bochner.
- **Littlewood + Jensen on `ζ` directly.**  `∫_{1/2}^{1} N(σ,T)dσ ≪ T log log T` (Bohr–Landau /
  Littlewood, using `jensen_avg_log_sq` and the second moment) bounds only the zeros with
  `|β − 1/2| ≥ δ` for fixed `δ`; it says nothing about the `≍ T log T` zeros within `1/log T` of
  the line.  Almost-all-near-the-line does not give any on the line.
- **Levinson's method with a trivial mollifier.**  With `M = 1` and `σ = 1/2 − R/log T`, the mean
  square of `|G(σ+it)|` is `≍ e^{2R}`, so `(1/R) log L ≈ 2 > 1` and the Levinson bound is vacuous
  — the mollifier is not optional (Conrey–Iwaniec–Soundararajan, *Critical zeros of Dirichlet
  L-functions*, Appendix A, Corollary A).

## External frontier (audited 2026-08-18)

- Hardy (1914) infinitude; Hardy–Littlewood (1921) `N₀(T) ≫ T`.
- Selberg (1942) `N₀(T) ≫ T log T` — sign-change route with the mollifier
  `M = (partial sums of ζ^{-1/2})²`.
- Levinson (1974) `≥ 1/3`; Conrey (1989) `> 2/5`; Bui–Conrey–Young (2011) `> 41%`;
  Pratt–Robles–Zaharescu–Zeindler (2019) `> 5/12`; Conrey–Iwaniec–Soundararajan (2013) `56%` for
  the Dirichlet family.  The Levinson–Conrey line all needs the mollified second moment of
  `Q(-D/L)ζ · M` with `X = T^{θ}`, `θ < 1/2` (Conrey) — strictly more machinery than (S1)–(S3).
- Selberg's route is the cheaper one for a *superlinear-only* target because it has no threshold
  constant to beat; that is why (S1)–(S3) and not Levinson is the chosen attack.

## Log
- 2026-08-18 — created in 1-in-progress.  Grid-cancellation reduction Lean-certified
  (`GridCancellationZeroCount.lean`, `XiSuperlinearFromCancellation.lean`); target reduced to
  `GridCancellationSurplus`; dead ends recorded; (S1)–(S3) named as the open analytic core.

## The Gram-point route does not benefit from the superlinear-only slack (2026-08-18)

The classical alternative to the grid device is the Gram-point route.  With `θ(g_n) = nπ`, the AFE
gives `(−1)^n Z(g_n) = 2 + (oscillating terms in m ≥ 2)`, so `∑_{n≤N}(−1)^n Z(g_n) ≈ 2N` — a pure
diagonal main term, much softer than any cancellation estimate.  Put
`A = {n ≤ N : (−1)^n Z(g_n) > 0}`.  Cauchy–Schwarz against `∑ |Z(g_n)|² ≪ N log T` gives
`|A| ≫ N/log T ≍ T`.

But the conversion of `A` into zeros is parity-locked: `Z(g_n)` has sign `(−1)^n` for `n ∈ A`, so a
sign change is detected only between two elements of `A` at odd distance, and disjoint such pairs
exist in quantity only once `|A| > N/2`.  If `A` were exactly the even integers, `Z` would be
nonnegative at every Gram point and no zero would be detected at all.  So the Gram route needs a
**proportion above one half** at Gram points — an explicit-constant statement — and therefore gains
nothing from the three relaxations listed at the top of this card.

The grid device has no threshold: any cancellation defect `1 − Bsum/L ≫ 1/ω(1)` suffices.  That is
why the Lean reduction is built on the grid device and not on Gram points.

## The single crux

In both routes the irreducible input is the **mollified second moment on the critical line**
```text
∫_T^{2T} |ζ(1/2+it) M(1/2+it)|² dt ≪ T,   M(s) = ∑_{m≤X} μ(m) m^{-s} P(log(X/m)/log X),
```
with `X = T^θ`.  It is what flattens the log factor and makes both `Mx` (grid) and
`∑|Z(g_n)M|²` (Gram) comparable to the number of cells / Gram points.  Without it every route
stalls at `N₀(T) ≫ T`.  The tree owns the mollifier's own second moment
(`RHTower/Sieve/InghamMollifierSecondMoment.lean`, upper bound `O(X + V log X)`) and the
critical-line fourth moment of `ζ` with polylog budgets, but not the product moment.  **Next brick:
`∫_T^{2T}|ζ M|² dt ≪ T` for `X = T^θ`, `θ < 1/2`, built from the tree's smooth AFE
(`SmoothAFEZetaExact.lean`) and Dirichlet mean-value machinery (`Sieve/DirichletMVT.lean`,
`Sieve/DirichletMeanValue.lean`, `DpolyBallFloor.lean`).**

Available and already Lean-certified for the cancellation half of (S2): the continuous
first-derivative test (van der Corput, `k = 1`) in both global and interval-local form,
`GaloisForLFunctions.HTGeometry.abs_integral_mul_cos_phase_le` and
`abs_integral_mul_cos_phase_le_on` in `HTGeometry/NonstationaryPhaseLowerBound.lean`.  The Hardy
phase has `θ''(t) = 1/(2t) > 0`, so the hypotheses apply directly to each twisted cell integral.

## Asset inventory for the crux (verified 2026-08-18)

- `RHTower/Sieve/DirichletMVT.lean` — `dirichlet_meanValue_complex`:
  `|∫_0^T |F|² − T ∑_{n<N}|a_n|²| ≤ 4N(1+log N)∑|a_n|²` for `F(t) = ∑_{n<N}a_n n^{it}`.  Error
  `O(N log N)`; the sharp Montgomery–Vaughan `O(N)` is **not** owned (needs a Hilbert inequality at
  the frequencies `log n`).  For `ζM` through the AFE the effective length is `X·√T`, so the
  usable range is `X ≪ √T/log T` — comfortably inside `θ < 1/2`.
- `RHTower/Sieve/InghamMollifierSecondMoment.lean` — the mollifier alone:
  `∫_{-T}^{T}|M_X(1/2+it)|²dt ≤ 5πe·X + (5π/2)(1+log X)T`.
- `RHTower/SmoothAFEZetaExact.lean` — exact Gaussian smooth AFE:
  `riemannZeta_line_eq_smoothAFEZetaMellin_sub_dual_sub_residue`, with the left edge still an exact
  reflected Mellin integral (`smoothAFEZetaDualMellinAt`); `SmoothAFEZetaDirichletExpansion` expands
  the right edge.  This is the AFE the product moment must be built on.
- `RHTower/HardyZ.lean`, `RHTower/HardyZPhaseAsymptotic.lean` — exact polar decomposition
  `ζ(1/2+it) = e^{-iθ(t)}Z(t)` (`riemannZeta_line_eq_exp_neg_theta_mul_hardyZ`,
  `exp_theta_mul_riemannZeta_line_eq_hardyZ`).
- `HTGeometry/NonstationaryPhaseLowerBound.lean` — the first-derivative test, global and
  interval-local.
- `RHTower/MeanValueBridge.lean` — `jensen_avg_log`, `jensen_avg_log_sq` (`⨍ log g ≤ ½ log ⨍ g²`),
  and `RHTower/JensenMeanLog.lean` — `integral_log_le_length_mul_log_mean`; these are the Levinson
  concavity steps, kept in case the Levinson route is revisited.
- `RHTower/EntireWeightedLittlewoodRectangle.lean`, `EntireWeightedLittlewoodLeftClosure.lean` —
  Littlewood's lemma for entire functions on rectangles, with left-edge zeros allowed; the Levinson
  route's contour input, already owned.

What is missing is exactly the **product main term**: the asymptotic (not merely bounded)
evaluation of `∫_T^{2T}|ζ(1/2+it)M(1/2+it)|²dt` with Möbius-times-polynomial coefficients.  That is
Conrey's computation and is the next brick.

## Major correction to the plan: the AFE and the Riemann–Siegel phase are already owned (2026-08-18)

A deeper audit changes the shape of the programme substantially.  The classical sharp-cutoff AFE
does **not** have to be built.

- **The AFE.**  `RHTower/SmoothAFEZetaDualReflection.lean`,
  `riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight`:
  ```
  ζ(½+iτ) = ∑_{n≥1} n^{-(½+iτ)} · smoothAFECutoff (n/x)
          + ∑_{n≥1} zetaChi(½+iτ) · n^{(½+iτ)-1} · smoothAFEZetaDualWeight τ (n·x)
          − smoothAFEZetaShiftedPoleResidue (½+iτ) x
  ```
  exact, unconditional, for every `x > 0`.  73 `SmoothAFEZeta*` modules support it, including the
  dual-weight tail bound `exists_norm_smoothAFEZetaDualWeight_le_inv`, the weight-freezing cost
  `exists_norm_smoothAFEZetaDualSeriesWeightError_le`, and `zetaChi` modulus/derivative bounds
  (`SmoothAFEZetaChi*`).  This is exactly the input the cancellation estimate needs: two absolutely
  convergent Dirichlet series with smooth weights.
- **The Riemann–Siegel phase.**  `RHTower/HardyZPhaseAsymptotic.lean` owns the branch-free global
  phase `gammaHardyTheta τ = ∫_0^τ gammaHardyPhaseRate`, with
  `hasDerivAt_gammaHardyTheta` (`θ' = gammaHardyPhaseRate`), the explicit first-order law
  `gammaHardyPhaseRate_sub_log_conductor_bound`:
  `|θ'(t) − ½log(t/2π)| ≤ 33/(16t²) + π/(2t)`, the exact second jet
  `deriv_deriv_gammaHardyTheta` with `abs_deriv_gammaHardyPhaseRate_le`:
  `|θ''(t)| ≤ 1/t² + π/(4t)`, strict convexity on `[0,∞)`, and
  `exp_theta_mul_riemannZeta_line_eq_hardyZ` (`e^{iθ(τ)}ζ(½+iτ) = hardyZ τ`, real).

So Phase A of the programme (Hardy phase + AFE) is **owned**, not open.  The revised open list is:

1. **Z-side AFE.**  Convert the two-series AFE into a real expansion of `hardyZ` using
   `zetaChi(½+iτ) = e^{-2iθ(τ)}`, giving
   `hardyZ τ = ∑_n n^{-1/2}( w₁(n/x)·cos(θ(τ) − τ log n) + Re[w₂(τ, n x) e^{-i(θ(τ) − τ log n)}] ) + R(τ)`.
   Mechanical, needs only the corpus's phase-gauge identities.
2. **Cell cancellation.**  Apply the first-derivative test term by term.  The atomic estimate is now
   Lean-certified: see the next section.
3. **The mollified second moment** `∫_T^{2T}|ζM|² ≪ T` — still the crux, and now the only genuinely
   open analytic input.

## Landed bricks 2 and 3 (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyPhaseCellCancellation.lean`

- `continuousAt_deriv_digamma_of_re_pos`, `continuous_deriv_gammaHardyPhaseRate` — the exact Hardy
  phase curvature `θ''` is continuous (digamma is analytic on `Re > 0`, so its derivative is too).
  This is the hypothesis the tree's first-derivative test needs and it was not previously available.
- `hardyTwistPhase L τ = gammaHardyTheta τ − τ·L`, `hasDerivAt_hardyTwistPhase`,
  `hasDerivAt_hardyTwistRate`.
- `abs_integral_mul_cos_hardyTwistPhase_le` — **the atomic cell estimate**: for a weight with an
  integrable derivative and a phase velocity bounded below by `m` on the cell,
  `|∫_u^v g cos(θ(τ) − τL + φ)| ≤ |g u|/m + |g v|/m + ∫ (|g'|/m + |g|·|θ''|/m²)`.
- `le_abs_gammaHardyPhaseRate_sub_of_le_conductor` — **nonstationarity below the conductor**: if
  `L ≤ ½log(T/2π) − 2δ` and `33/(16T²) + π/(2T) ≤ δ`, then `|θ'(τ) − L| ≥ δ` for all `τ ≥ T`.
- `abs_integral_cos_hardyTwistPhase_le` — the bare cell integral with unit weight:
  `|∫_u^v cos(θ(τ) − τL + φ)| ≤ 2/δ + (v−u)(1/T² + π/(4T))/δ²`, with no arithmetic input at all.

`formal/GaloisForLFunctions/RHTower/ZetaChiHardyPhase.lean`

- `one_sub_linePt` — `1 − (½+iτ) = conj(½+iτ)`.
- `zetaChi_line_eq_gammaHardyPhase_sq` — **the functional-equation factor on the critical line is
  the square of the normalized Gamma phase**, `χ(½+iτ) = gammaHardyPhase τ ²`.
- `zetaChi_line_eq_exp_neg_two_theta` — hence `χ(½+iτ) = exp(−2iθ(τ))`.
- `exp_theta_mul_zetaChi_line` — `exp(iθ(τ))·χ(½+iτ) = exp(−iθ(τ))`: multiplying the two-series
  AFE by `exp(iθ)` sends the direct edge to `exp(i(θ − τ log n))` and the reflected edge to
  `exp(−i(θ − τ log n))`.  This is exactly the phase-gauge step that turns
  `riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight` into a real cosine/sine expansion of
  `hardyZ`, and its terms are precisely what `abs_integral_mul_cos_hardyTwistPhase_le` consumes.

All axiom-clean.  Next: the termwise real expansion of `hardyZ` (item 1 of the revised open list),
then the mollified second moment.

## Landed bricks 4 and 5: the Hardy-`Z` smooth AFE, complex and real (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyZSmoothAFE.lean`

- `exp_neg_half_log`, `cpow_neg_linePt`, `cpow_linePt_sub_one` — the exact splitting
  `n^{-(½+iτ)} = (√n)⁻¹ exp(−iτ log n)` and its reflected partner.
- `exp_theta_mul_cpow_neg_linePt`, `exp_neg_theta_mul_cpow_linePt_sub_one` — multiplying by
  `exp(±iθ(τ))` produces exactly `hardyTwistPhase (log n) τ = θ(τ) − τ log n`.
- `hardyZ_eq_two_tsum_smoothAFE` — **the Gaussian smooth AFE for Hardy's `Z`**, exact and
  unconditional for every cutoff scale `x > 0`:
  ```
  Z(τ) = ∑_{n≥1} (√n)⁻¹ exp( i(θ(τ) − τ log n) ) · smoothAFECutoff(n/x)
       + ∑_{n≥1} (√n)⁻¹ exp(−i(θ(τ) − τ log n) ) · smoothAFEZetaDualWeight τ (n·x)
       − exp(iθ(τ)) · smoothAFEZetaShiftedPoleResidue(½+iτ) x
  ```

`formal/GaloisForLFunctions/RHTower/HardyZSmoothAFEReal.lean`

- `norm_natSucc_cpow_neg_linePt`, `smoothAFEDirectWeightedSeries_summable` — absolute summability
  of the direct edge, from the tree's `exists_norm_smoothAFECutoff_le_neg_rpow` at exponent `1`
  against the `3/2`-power majorant.  (The dual edge already had
  `smoothAFEZetaDualWeightedSeries_summable`.)
- `re_ofReal_mul_exp_I_mul`, `re_ofReal_mul_exp_neg_I_mul` — the real part of a twisted phase term.
- `hardyZ_eq_two_tsum_smoothAFE_real` — **the real form**: both edges are twisted Hardy
  cosine/sine series with real weights,
  ```
  Z(τ) = ∑_n (√n)⁻¹ ( cos(θ−τ log n)·Re w₁ − sin(θ−τ log n)·Im w₁ )
       + ∑_n (√n)⁻¹ ( cos(θ−τ log n)·Re w₂ + sin(θ−τ log n)·Im w₂ ) − Re(residue).
  ```
  Every term is now exactly of the shape `g(τ)·cos(θ(τ) − τL + φ)` that
  `abs_integral_mul_cos_hardyTwistPhase_le` consumes (`sin t = cos(t − π/2)`).

All axiom-clean.  Item 1 of the revised open list is therefore **done**.  What remains is item 2
(summing the cell estimates over `n`, which needs the `τ`-derivative bounds of the two weights —
the tree has `SmoothAFEZetaDualWeightHeightDerivative` and `SmoothAFEZetaChiShift*DerivativeBound`
for exactly this) and item 3, the mollified second moment.

## Landed bricks 6 and 7 (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyTwistCellCombination.lean`

- `continuous_hardyTwistPhase`, `intervalIntegrable_cos_hardyTwistPhase`,
  `intervalIntegrable_sin_hardyTwistPhase`.
- `abs_integral_hardyTwistCombination_le` — the cell bound for a real combination
  `a·cos(θ(τ) − τL) + b·sin(θ(τ) − τL)` with `τ`-independent coefficients:
  `≤ (|a| + |b|)·(2/δ + (v−u)(1/T² + π/(4T))/δ²)`.  The sine is handled by the quarter-period shift
  `sin t = cos(t − π/2)`, so no second oscillatory estimate is needed.
- `abs_integral_afeTerm_le` — the same bound for one AFE term with amplitude `c ≥ 0` and a
  `τ`-independent complex weight `w`: `≤ c(|Re w| + |Im w|)·(cell bound)`.  This is exactly the
  direct edge of `hardyZ_eq_two_tsum_smoothAFE_real`, whose weight `smoothAFECutoff (n/x)` does not
  depend on `τ`.

`formal/GaloisForLFunctions/HTGeometry/IntervalIntegralTsumBound.lean`

- `abs_intervalIntegral_tsum_le` — **termwise cell bound**: if each term is integrable on the cell,
  the termwise absolute masses are summable, and each term's cell integral is bounded by a summable
  `B n`, then `|∫_u^v ∑' n, F n| ≤ ∑' n, B n`.  Built on mathlib's
  `hasSum_integral_of_summable_integral_norm`.  This is the interchange step that converts the
  per-term cancellation estimates of the AFE into a bound on the cell integral of `Z` itself.

Both axiom-clean, wired, built individually.

### Immediate next step

Instantiate `abs_intervalIntegral_tsum_le` on the direct edge of
`hardyZ_eq_two_tsum_smoothAFE_real` with `B n = (√n)⁻¹(|Re w₁| + |Im w₁|)·(cell bound)` from
`abs_integral_afeTerm_le`; the summability of `B` is the same `3/2`-power majorant already used in
`smoothAFEDirectWeightedSeries_summable`, and the per-term integrability is continuity.  The dual
edge additionally needs the `τ`-derivative of `smoothAFEZetaDualWeight`, for which the tree owns
`SmoothAFEZetaDualWeightHeightDerivative` and `SmoothAFEZetaChiShift*DerivativeBound`; that turns
`abs_integral_mul_cos_hardyTwistPhase_le` (weighted form) into the dual-edge cell bound.  After
that, only the mollified second moment remains.

## Landed brick 8: the direct edge, cell by cell (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyZDirectEdgeCellBound.lean`

- `directEdgeTerm x n τ` — the `n`-th term of the direct edge of
  `hardyZ_eq_two_tsum_smoothAFE_real`, and `continuous_directEdgeTerm`.
- `abs_directEdgeTerm_le` — `|term| ≤ (√n)⁻¹(|Re w₁| + |Im w₁|)` pointwise.
- `summable_directEdge_absMass` — the termwise absolute masses over a cell are summable, via
  `exists_norm_smoothAFECutoff_le_neg_rpow` at exponent `1` and the `3/2`-power majorant.  This
  discharges the hard hypothesis of the interchange.
- `abs_integral_directEdge_le` — **any summable family of per-term cell bounds bounds the cell
  integral of the whole direct edge.**
- `abs_integral_directEdgeTerm_le` — the per-term bound below the conductor, in exactly that form.

So the direct edge is complete: below the conductor every term gains `2/δ + (v−u)·O(1/T)/δ²`, and
the sum converges absolutely.

### What the dual edge still needs

`smoothAFEZetaDualWeight τ Y` depends on `τ`, so its cell integral needs the **weighted** estimate
`abs_integral_mul_cos_hardyTwistPhase_le` with `g(τ) = (Re or Im) smoothAFEZetaDualWeight τ (n x)`
and `g'` its height derivative.  The tree already owns that derivative:
`RHTower/SmoothAFEZetaDualWeightHeightDerivative.lean` and the `SmoothAFEZetaChiShift*Bound`
family.  That is the next brick, after which only the mollified second moment remains.

## Landed brick 9: the frozen dual edge (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyZFrozenDualEdgeCellBound.lean`

The dual weight depends on the height, so the constant-weight estimate does not apply to it
directly.  Rather than build the missing continuity of the weight's height derivative, the route
taken is the one the tree already priced: **freeze the weight**.

- `dualEdgeTermAt x u n τ` — the `n`-th dual-edge term with the weight frozen at height `u`; taking
  `u = τ` recovers the genuine term.
- `continuous_dualEdgeTermAt`, `abs_dualEdgeTermAt_le`.
- `summable_dualEdgeAt_absMass` — summability of the termwise absolute masses over a cell, from
  `exists_norm_smoothAFEZetaDualWeight_le_inv` (`‖dualWeight u Y‖ ≤ K(1+|u|)/Y`) and the
  `3/2`-power majorant.
- `abs_integral_frozenDualEdge_le` — the frozen dual edge obeys the termwise interchange bound.
- `abs_integral_dualEdgeTermAt_le` — the per-term cell bound below the conductor, via
  `abs_integral_hardyTwistCombination_le` with `a = Re w`, `b = Im w`.

The freezing cost is already owned:
`exists_norm_smoothAFEZetaDualSeriesWeightError_le` gives, for `4 ≤ τ`, `4 ≤ u`, `0 < x`,
```
‖∑ₙ (n+1)^{s−1}( dualWeight τ ((n+1)x) − dualWeight u ((n+1)x) )‖ ≤ (A/x)·|τ−u|·majorant(3/2),
```
and `‖exp(−iθ(τ))‖ = 1`, so the real dual edge differs from its frozen version by at most
`(A/x)·|τ−u|·M` pointwise.  On a cell of length `H` frozen at its left endpoint that is `≤ (A/x)HM`,
contributing `≤ (A/x)H²M` to the cell integral.

### Next brick

The freezing transfer itself: `|dualEdge(τ) − ∑ₙ dualEdgeTermAt x a n τ| ≤ (A/x)|τ−a|·M`, obtained
by taking real parts of the owned complex freezing bound through `re_ofReal_mul_exp_neg_I_mul` and
`exp_neg_theta_mul_cpow_linePt_sub_one`.  Then the two edges combine into a cell bound for `Z`
itself, and the remaining input is the mollified second moment.

## Landed brick 10: the freezing transfer (2026-08-18)

`formal/GaloisForLFunctions/RHTower/HardyZDualEdgeFreezing.lean`

- `summable_dualEdgeTermAt` — the frozen dual edge is summable at every height.
- `dualEdgeTermAt_sub_eq_re` — the difference between the genuine and the frozen dual-edge term is
  exactly the real part of `exp(−iθ(τ))·(n+1)^{s−1}·(w_τ − w_u)`, via
  `exp_neg_theta_mul_cpow_linePt_sub_one` and `re_ofReal_mul_exp_neg_I_mul`.
- `abs_tsum_dualEdge_sub_frozen_le` — **the freezing transfer**: there is `A ≥ 0` with, for
  `0 < x`, `4 ≤ τ`, `4 ≤ u`,
  ```
  |∑ₙ dualEdgeTermAt x τ n τ − ∑ₙ dualEdgeTermAt x u n τ| ≤ (A/x)·|τ − u|·majorant(3/2).
  ```
  Proof: the tree's complex frozen-series bound, multiplied by the unit-modulus phase
  `exp(−iθ(τ))` (`‖exp(−iθ)‖ = 1` since the exponent is purely imaginary) and pushed through
  `Complex.reCLM.map_tsum`.

All axiom-clean.  Both edges of the real Hardy-`Z` smooth AFE now have complete cell machinery:
the direct edge directly, the dual edge after freezing at the cell's left endpoint with an
explicitly priced error.

### State of the open list

1. Z-side AFE — **done** (bricks 4, 5).
2. Cell estimates and their summation — **done** (bricks 3, 6, 7, 8, 9, 10).
3. The mollified second moment `∫_T^{2T}|ζM|² ≪ T` — **open**, and now the only remaining input.

## Landed brick 11: the mean-square counting form removes input (S3) (2026-08-18)

`GridCancellationZeroCount.lean` was refactored so that both counting theorems come from one
extraction, and a strictly stronger counting form was added.

- `exists_grid_zero_cells` — **the extraction**: there is a set `S ⊆ range N` of cells and an
  injectively indexed `Zs` of interior zeros with `#Zs = #S`, such that
  `∫|f| ≤ ∑_{j∈S} ∫_{I_j}|f| + ∑_{j<N}|∫_{I_j} f|`.  Both counting theorems are now corollaries.
- `exists_finset_zeros_card_mul_ge` — the original uniform-cell form, unchanged in statement.
- `sub_le_sqrt_card_mul_of_grid` — **the mean-square form**: `L − Bsum ≤ √(#Zs · Q)` where
  `Q` bounds `∑_{j<N}(∫_{I_j}|f|)²`.  Proof: Cauchy–Schwarz over the cells
  (`sq_sum_le_card_mul_sum_sq`).  Stated through `√` so that it is unconditionally true also when
  `L − Bsum < 0`, hence needs no side hypothesis.

`XiSuperlinearFromCancellation.lean` gains the matching reduction:

- `GridCancellationMeanSquareSurplus f` and
  `superlinearSamples_xiRealDivisor_of_meanSquare_grid_cancellation`.

**Why this matters.**  The old form needed a bound on `max_j ∫_{I_j}|f|` — analytic input (S3),
a short-interval mollified second moment.  The new form needs only `∑_j (∫_{I_j}|f|)²`, and
`(∫_{I_j}|f|)² ≤ H ∫_{I_j}|f|²` gives `Q ≤ H·∫_T^{2T}|f|²` — a **global** mean square, exactly what
a Dirichlet-polynomial mean-value theorem supplies.  So (S3) is eliminated as a separate input:
with `f = Z·|M|²` it becomes `∫_T^{2T}|ζ|²|M|⁴`, and with the unmollified `f = Z` it is the plain
second moment, which the tree already owns (`SecondMoment.lean`, `DpolyBallFloor.lean`).

### Revised open list

1. Z-side AFE — done.
2. Cell estimates, their summation and the freezing transfer — done.
3. (S3) per-cell maximum — **eliminated** by the mean-square form.
4. (S1) mollified absolute-mass lower bound — reduced to pairing `Z` against `cos(θ(t))|M(½+it)|²`:
   the `n = 1` diagonal gives `∫(1 + cos 2θ)|M|² ≍ T log X` from the Dirichlet mean value theorem
   (owned), and every `n ≥ 2` term is non-stationary, hence covered by the cell machinery above.
5. (S2) grid cancellation — covered by the cell machinery.
6. The mollified second moment `∫|ζM|² ≪ T` — still the one genuinely open analytic input.

## Landed brick 12: the two-edge split of critical-line zeta (2026-08-18)

`formal/GaloisForLFunctions/RHTower/ZetaLineAFESplit.lean`

- `smoothAFEDirectSeries x τ`, `smoothAFEDualSeries x τ` — the two Dirichlet edges of the Gaussian
  smooth AFE, the reflected one with the unimodular factor stripped.
- `riemannZeta_line_eq_direct_add_chi_mul_dual` — the AFE in the factored form
  `ζ(½+iτ) = D₁ + χ(½+iτ)·D₂ − ρ` (the factor is pulled out of the series by `tsum_mul_left`).
- `norm_riemannZeta_line_le` — `|ζ(½+iτ)| ≤ |D₁| + |D₂| + |ρ|`, using the tree's
  `norm_zetaChi_line` (unimodularity of `χ` on the critical line; already owned — not rebuilt).
- `norm_sq_riemannZeta_line_mul_le` — **the pointwise mollified square majorant**
  `|ζ(½+iτ)·m|² ≤ 3(|D₁m|² + |D₂m|² + |ρm|²)` for every `m`.

Consequence: the mollified second moment `∫_T^{2T}|ζM|²` is bounded by three
**Dirichlet-polynomial** mean squares, each of which is exactly what
`Sieve/DirichletMVT.dirichlet_meanValue_complex` evaluates:
`|∫_0^T|F|² − T∑_{n<N}|a_n|²| ≤ 4N(1+log N)∑|a_n|²`.

So the last open input has been reduced to a coefficient estimate: with
`c_k = k^{-1/2}∑_{mn=k} μ(m)P(log(X/m)/log X)·w(n/x)`, one needs
```
∑_k |c_k|² ≪ 1        and        (length) · log(length) ≪ T,
```
the second holding for `x·X ≪ T/log T`.  The first is the Möbius-mollifier divisor computation —
the remaining mathematical content, and the next target.

## Landed brick 13: the mean value theorem on a window (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMVTWindow.lean`

- `intervalIntegrable_normSq_dirPoly`.
- `dirichlet_meanValue_window` — for every `U, V`,
  `|∫_U^V ‖dirPoly N a‖² − (V − U)∑|a_m|²| ≤ 8 N (1 + log N) ∑|a_m|²`, by subtracting two copies of
  the tree's `[0,T]` statement.  The dyadic window `[T, 2T]` needs exactly this form; the tree only
  had the `[0,T]` version.

### Remaining chain for `∫_T^{2T}|ζM|² ≪ T`

With brick 12 the mollified second moment is bounded by three Dirichlet mean squares, and with
brick 13 each of those is `((V−U) + 8N(1+log N))·∑_k|c_k|²`.  What is left is entirely arithmetic:

- **truncation** — replace the Gaussian-cutoff series by a finite Dirichlet polynomial; the cost is
  controlled by `exists_norm_smoothAFECutoff_le_neg_rpow` at any exponent, already owned;
- **the coefficient estimate** `∑_k |c_k|² ≪ 1` for
  `c_k = k^{-1/2} ∑_{mn=k} μ(m) P(log(X/m)/log X) w(n/x)`.  Note the naive divisor bound is *not*
  enough: with `P ≡ 1` and `w ≡ 1` the sum vanishes for `k ≤ X` but only gives `≪ d(k)` beyond, and
  `∑_{X<k≤xX} d(k)²/k ≍ log⁴(xX)`.  The cancellation supplied by Levinson's polynomial `P` is what
  makes the estimate `O(1)`; that is the Conrey computation and is the remaining mathematics.

## Landed brick 14: truncating the direct edge to a Dirichlet polynomial (2026-08-18)

`formal/GaloisForLFunctions/RHTower/SmoothAFEDirectTruncation.lean`

- `afeDirectCoeff x N : Fin N → ℂ` — the coefficients `(√n)⁻¹ · smoothAFECutoff (n/x)`.
- `afeDirectTerm_eq` — each AFE term is `coefficient × exp(−iτ log n)`, i.e. exactly a term of the
  tree's `dirPoly` evaluated at `−τ`.
- `sum_afeDirectCoeff_eq` — `dirPoly N (afeDirectCoeff x N) (−τ)` is the partial sum of the direct
  edge.
- `exists_norm_smoothAFEDirectSeries_sub_dirPoly_le` — **the truncation bound**: there is `K ≥ 0`
  with, for every `x > 0`, height `τ` and cutoff `N`,
  ```
  ‖smoothAFEDirectSeries x τ − dirPoly N (afeDirectCoeff x N) (−τ)‖ ≤ K x · ∑_{i} (i+N+1)^{-3/2},
  ```
  uniformly in the height.  Proof: `exists_norm_smoothAFECutoff_le_neg_rpow` at exponent `1`
  against the `3/2`-power majorant, and `Summable.sum_add_tsum_nat_add` to split off the tail.

So the direct edge is now literally a `dirPoly` up to a tail that vanishes as `N → ∞`, and
`dirichlet_meanValue_window` applies to it directly.

### Remaining

The single open item is unchanged and now completely isolated: the coefficient estimate
`∑_k |c_k|² ≪ 1` for the Möbius-mollified product coefficients (the Conrey computation).  Every
other link in the chain from `∫_T^{2T}|ζM|² ≪ T` to `SuperlinearSamples xiRealDivisor` is
Lean-certified and axiom-clean.

## Landed brick 15: the mollifier annihilates the short range (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/MollifierShortRange.lean`

- `filter_le_divisors_eq` — for `0 < k ≤ X` the length condition `m ≤ X` is vacuous on the divisors
  of `k`.
- `sum_moebius_filter_mul_const_eq_zero` — for `1 < k ≤ X` and a weight constant along the divisors
  of `k`, the truncated Möbius coefficient `∑_{m ∣ k, m ≤ X} μ(m)·v` **vanishes**.
- `sum_moebius_filter_eq_zero`, `sum_moebius_filter_one` — the unweighted form and the surviving
  `k = 1` term.

This is the first step of the coefficient estimate: the mollified product coefficients `c_k` vanish
identically for `1 < k ≤ X` once the second factor is constant along the divisor chain, so
`∑_k |c_k|²` is carried entirely by `k = 1` plus the range `k > X`.  It reuses the tree's
`sum_divisors_moebius_real` rather than re-proving the Möbius divisor identity.

### What is left in the coefficient estimate

Only the range `k > X`, where the truncation bites and the weight `w(n/x)` is no longer constant
along the divisor chain.  There the cancellation has to come from Levinson's smoothing polynomial
`P(log(X/m)/log X)`; that is the remaining Conrey computation.

## Landed brick 16: the short-range coefficient with a varying weight (2026-08-18)

`MollifierShortRange.lean` extended:

- `abs_moebius_le_one`, `norm_moebius_complex_le_one` — `|μ(m)| ≤ 1` in `ℝ` and `ℂ` (by the
  squarefree dichotomy; not previously in the tree or reachable by name from mathlib here).
- `sum_moebius_divisors_complex` — the complex form of the Möbius divisor identity, cast from the
  tree's real one.
- `norm_sum_moebius_filter_sub_indicator_le` — **the short-range coefficient law**: for `0 < k ≤ X`
  and any weight `v`,
  ```
  ‖ ∑_{m ∣ k, m ≤ X} μ(m) v(k/m) − [k = 1] ‖ ≤ ∑_{m ∣ k} ‖v(k/m) − 1‖ .
  ```
  So the mollified coefficient is the unit indicator up to the total deviation of the AFE cutoff
  from `1` along the divisor chain — and the tree already bounds that deviation
  (`exists_norm_smoothAFECutoff_sub_one_le_rpow`).

This is the general form of brick 15 with the constancy hypothesis removed, and it is the shape the
coefficient estimate needs for `k ≤ X`.  What is left is the complementary range `k > X`, where the
truncation genuinely bites.

## Landed brick 17: the long range of the mollified coefficient (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/MollifierLongRange.lean`

- `exists_norm_sum_moebius_filter_cutoff_le` — for **every** decay exponent `A > 0` there is
  `K ≥ 0` with, for all `x > 0`, `0 < X`, `0 < k`,
  ```
  ‖ ∑_{m ∣ k, m ≤ X} μ(m) · smoothAFECutoff((k/m)/x) ‖ ≤ d(k) · K · (k/(X x))^{-A}.
  ```
  Every surviving divisor `m ≤ X` forces the cutoff argument `(k/m)/x` to be at least `k/(X x)`,
  and the Gaussian cutoff decays faster than any power there; `|μ| ≤ 1` and the divisor count
  finish it.

So the mollified product has effective length `X · x`: beyond it the coefficients are smaller than
any power, uniformly in the height.  Combined with brick 16 (`k ≤ X`, coefficient = unit indicator
plus cutoff defect), the coefficient estimate is now reduced to the **middle range**
`X < k ≲ X x`, where the naive divisor bound loses `log⁴` and the cancellation must come from
Levinson's smoothing polynomial `P(log(X/m)/log X)`.

## Landed brick 18: the linear mollifier produces the von Mangoldt weight (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/LinearMollifierVonMangoldt.lean`

- `sum_moebius_mul_log_eq_neg_vonMangoldt` — `∑_{d ∣ k} μ(d) log d = −Λ(k)` for `k > 1`, derived
  from the tree's `vonMangoldt_eq_sum_moebius_mul_log` (`μ * log = Λ`) and the Möbius divisor
  identity.
- `sum_moebius_filter_log_div_eq_vonMangoldt` — **for `1 < k ≤ X`**,
  ```
  ∑_{m ∣ k, m ≤ X} μ(m) log(X/m) = Λ(k).
  ```

This identifies the arithmetic mechanism that makes the mollified second moment bounded.  With
Levinson's linear smoothing `P(y) = y`, the mollifier coefficient is `μ(m) log(X/m)/log X`, so on
the short range the mollified coefficient is exactly `Λ(k)/log X`.  Since
`∑_{k ≤ X} Λ(k)²/k ≍ (log X)²/2`, the weighted square sum is `≍ 1/2` — bounded — whereas the
unsmoothed divisor bound loses `log⁴`.  That is precisely the gap identified in brick 13's note.

### Remaining

The coefficient estimate now has all three ranges identified with their mechanisms:
`k ≤ X` (von Mangoldt collapse, brick 18 + brick 16 for the cutoff defect), `k ≳ X x`
(negligible to any order, brick 17), and the middle range, where the same `μ * log = Λ` collapse
degrades to a partial divisor sum.  What is still missing in Lean is the Chebyshev-type estimate
`∑_{k ≤ X} Λ(k)²/k ≪ (log X)²` together with the middle-range partial-sum bound.

## Landed brick 19: the Chebyshev square-weight bound (2026-08-18)

`formal/GaloisForLFunctions/RHTower/ChebyshevSquareWeight.lean`

- `sum_vonMangoldt_sq_div_le_log_mul_sum` — termwise, `∑_{k ≤ N} Λ(k)²/k ≤ log N · ∑_{k ≤ N} Λ(k)/k`
  (from mathlib's `vonMangoldt_le_log` and monotonicity of `log`).
- `exists_sum_vonMangoldt_sq_div_le` — **`∃ C, ∀ N ≥ 1, ∑_{k ≤ N} Λ(k)²/k ≤ log N (log N + C)`**,
  by feeding the tree's Mertens second theorem (`∑_{n ≤ N} Λ(n)/n − log N → −γ`) through
  `Tendsto.bddAbove_range`.

So the short-range contribution to `∑_k |c_k|²` is bounded: with the linear mollifier the
coefficient there is `Λ(k)/log X` (brick 18), and this brick gives
`∑_{k ≤ X} Λ(k)²/(k (log X)²) ≤ (log X + C)/log X = 1 + o(1)`.  The `log⁴` loss of the naive
divisor bound is gone.

### Remaining

Only the middle range `X < k ≲ X x` is open: there the divisor sum `∑_{m ∣ k, m ≤ X} μ(m) log(X/m)`
is a *partial* sum, so the `μ * log = Λ` collapse of brick 18 does not apply verbatim and the
partial-sum bound has to be supplied.  That is the last piece of the Conrey computation.

## Landed brick 20, and the identification of the last open input (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/BarbanVehovWeight.lean`

- `barbanVehovWeight X m = if m ≤ X then μ(m) log(X/m) else 0` and
  `barbanVehovCoeff X k = ∑_{m ∣ k} barbanVehovWeight X m`.
- `barbanVehovCoeff_eq_sum_filter`, `barbanVehovCoeff_one`.
- `barbanVehovCoeff_eq_vonMangoldt` — on the short range `1 < k ≤ X` the coefficient **is** `Λ(k)`.
- `abs_barbanVehovCoeff_le` — the crude majorant `|b_X(k)| ≤ d(k) log X`.

### The last open input, named

The middle range is **exactly the Barban–Vehov / Graham mean square**:
```text
∑_{k ≤ N} ( ∑_{m ∣ k, m ≤ X} μ(m) log(X/m) )² = N log X + O(N)          (Graham 1978)
```
This is a named, self-contained theorem of sieve theory — not an open problem — and it is the only
remaining analytic input of the whole programme.  Its short-range half is already Lean-proved here
(the coefficient is `Λ(k)`, and `∑_{k ≤ X} Λ(k)²/k ≪ (log X)²` is brick 19); what Graham supplies is
the partial-divisor-sum range `k > X`, where the crude bound `d(k) log X` loses `log⁴`.

**Next target: Graham's theorem.**  Standard route — expand the square into
`∑_{m₁,m₂ ≤ X} μ(m₁)μ(m₂) log(X/m₁) log(X/m₂) · #{k ≤ N : [m₁,m₂] ∣ k}`, i.e.
`N ∑_{m₁,m₂ ≤ X} μ(m₁)μ(m₂) log(X/m₁)log(X/m₂)/[m₁,m₂] + O(X²log²X)`, then evaluate the diagonal
quadratic form by the standard `gcd`-factorisation of `1/[m₁,m₂] = gcd/(m₁m₂)` and multiplicativity.
The tree already owns the Selberg-sieve quadratic-form machinery
(`RHTower/Sieve/GhsStepFour.lean`, `sieveMeanSquare`) and the divisor/`gcd` toolkit, so this is a
sieve computation, not new mathematics.

## Landed brick 21: the first structural step of Graham's theorem (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/DivisorSumMeanSquare.lean`

- `card_filter_dvd_Icc` — `#{k ∈ [1,N] : d ∣ k} = ⌊N/d⌋` for `d > 0`, from the tree's
  `multiples_Icc`.
- `sum_sq_divisorSum_eq_lcm_quadratic` — **the exact expansion**
  ```
  ∑_{k ≤ N} ( ∑_{m ∣ k} a(m) )²  =  ∑_{m₁, m₂ ≤ N} a(m₁) a(m₂) ⌊N / [m₁,m₂]⌋ ,
  ```
  purely combinatorial: expand the square over the divisor product, swap with `Finset.sum_comm'`
  through the membership equivalence `m₁ ∣ k ∧ m₂ ∣ k ↔ [m₁,m₂] ∣ k`, and count multiples.
  No property of the coefficients is used, so it applies verbatim to the Barban–Vehov weights.

This is step 1 of Graham's theorem.  What remains of Graham is the evaluation of the resulting
quadratic form: replace `⌊N/[m₁,m₂]⌋` by `N/[m₁,m₂] + O(1)` (error `O(X² log²X)` after the crude
coefficient majorant of brick 20), then evaluate
`∑_{m₁,m₂ ≤ X} μ(m₁)μ(m₂) log(X/m₁) log(X/m₂) / [m₁,m₂]` by `1/[m₁,m₂] = gcd(m₁,m₂)/(m₁m₂)` and
multiplicativity.

## Landed brick 22: Graham step two — removing the floor (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/DivisorSumMeanSquareSmooth.lean`

- `abs_natDiv_sub_div_le` — `|⌊N/d⌋ − N/d| ≤ 1` for `d > 0`, from `Nat.div_add_mod` and
  `Nat.mod_lt`.
- `abs_sum_sq_divisorSum_sub_lcm_main_le` — **step two of Graham's theorem**:
  ```
  | ∑_{k ≤ N} (∑_{m ∣ k} a m)²  −  ∑_{m₁,m₂ ≤ N} a(m₁)a(m₂) · N/[m₁,m₂] |
      ≤ ∑_{m₁,m₂ ≤ N} |a(m₁)| |a(m₂)| .
  ```

With the Barban–Vehov coefficients supported on `m ≤ X` and majorised by `log X` (brick 20), the
right-hand side is `O(X² log²X)`, which is the error term Graham's theorem carries.

### What is left of Graham

Only the evaluation of the smooth form
```
∑_{m₁,m₂ ≤ X} μ(m₁) μ(m₂) log(X/m₁) log(X/m₂) / [m₁,m₂]  =  log X + O(1),
```
by `1/[m₁,m₂] = gcd(m₁,m₂)/(m₁m₂)`, the `gcd`-expansion `gcd = ∑_{e ∣ m₁, e ∣ m₂} φ(e)`, and
multiplicativity.  Steps one and two are now Lean-certified.

## Landed brick 23: the Selberg diagonalisation (Graham step three, structural half) (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/LcmQuadraticDiagonalization.lean`

- `div_lcm_eq_sum_totient` — the pointwise identity
  `a(m)a(n)/[m,n] = ∑_{e ∣ (m,n)} φ(e) · (a(m)/m)(a(n)/n)`, from `Nat.gcd_mul_lcm` and
  `Nat.sum_totient`.
- `sum_div_lcm_eq_totient_diagonal` — **the Selberg diagonalisation**: for any finite `S` of
  positive integers and any coefficients,
  ```
  ∑_{m₁,m₂ ∈ S} a(m₁) a(m₂) / [m₁,m₂]  =  ∑_e φ(e) · ( ∑_{m ∈ S, e ∣ m} a(m)/m )² .
  ```
  Proof: the pointwise identity, then `Finset.sum_comm'` through
  `e ∣ gcd(m₁,m₂) ↔ e ∣ m₁ ∧ e ∣ m₂`, then `filter_product` to factor the pair filter into a
  square.

Two consequences.  First, the lcm quadratic form is manifestly **positive semidefinite** — the
structural fact underlying the whole Selberg sieve.  Second, Graham's evaluation is reduced from a
double sum to the one-dimensional sums
```
c_e(X) := ∑_{m ≤ X, e ∣ m} μ(m) log(X/m)/m ,
```
so that `∑_{m₁,m₂ ≤ X} μ(m₁)μ(m₂)log(X/m₁)log(X/m₂)/[m₁,m₂] = ∑_e φ(e) c_e(X)²`.

### What is left

Evaluating `c_e(X)`.  Writing `m = e m'` and using multiplicativity of `μ` on `gcd(e,m') = 1`, the
inner sum is a Möbius sum over integers coprime to `e`, whose evaluation is the last elementary
step.  Steps 1–3 of Graham are now Lean-certified; only this final one-dimensional evaluation
remains.

## Landed brick 24: reindexing the diagonalised Möbius sums (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusScaledReindex.lean`

- `sum_filter_dvd_eq_sum_scaled` — `∑_{m ≤ N, e ∣ m} f(m) = ∑_{j ≤ N/e} f(e j)` for `e > 0`,
  from the tree's `multiples_Icc` plus injectivity of `j ↦ e j`.
- `moebius_mul_eq_zero_of_not_coprime` — `μ(a b) = 0` whenever `gcd(a,b) > 1` (a common prime `p`
  gives `p² ∣ a b`, so `a b` is not squarefree).
- `moebius_mul_of_coprime` — the multiplicative factorisation, from mathlib's
  `isMultiplicative_moebius`.
- `sum_filter_dvd_moebius_scaled` — **the reindexed diagonal sum**:
  ```
  ∑_{m ≤ N, e ∣ m} μ(m) g(m)  =  ∑_{j ≤ N/e, (e,j)=1} μ(e) μ(j) g(e j) .
  ```

So the inner sums of the Selberg diagonalisation are now genuinely one-dimensional Möbius sums
restricted to the residues coprime to `e`, carrying the constant factor `μ(e)` — in particular they
vanish identically unless `e` is squarefree.

### What is left of Graham

Only the evaluation of `∑_{j ≤ X/e, (e,j)=1} μ(j) log(X/(e j))/j`, an elementary Möbius sum with a
logarithmic weight over a coprimality class.  Every structural step of Graham's theorem — expansion,
floor removal, totient diagonalisation, reindexing — is now Lean-certified.

## Landed brick 25: support of the diagonalised Möbius sums (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusDiagonalSupport.lean`

- `filter_dvd_eq_empty_of_lt`, `sum_filter_dvd_eq_zero_of_lt` — beyond the window there are no
  multiples, so the inner sum is empty.
- `sum_filter_dvd_moebius_eq_zero_of_not_squarefree` — a non-squarefree modulus kills the whole
  inner Möbius sum (every reindexed term carries the factor `μ(e) = 0`).
- `sum_filter_dvd_moebius_eq_zero` — the two together: the diagonal is **supported on squarefree
  moduli inside the window**.

So `∑_e φ(e) c_e(X)²` is a finite sum over squarefree `e ≤ X`, which is what makes the totient
weight summable.

### Ledger of Graham's theorem

| step | content | status |
|---|---|---|
| 1 | expand the square into the lcm quadratic form | brick 21 ✔ |
| 2 | remove the floor, error `O(X² log²X)` | brick 22 ✔ |
| 3 | totient/gcd diagonalisation into a sum of squares | brick 23 ✔ |
| 4 | reindex the inner sums, `μ(e)` factors out | brick 24 ✔ |
| 5 | support: squarefree `e ≤ X` only | brick 25 ✔ |
| 6 | evaluate `∑_{j ≤ X/e, (e,j)=1} μ(j) log(X/(ej))/j` | open |

Step 6 is the only remaining item of the entire programme.

## Landed brick 26: the logarithmic Möbius sum against the harmonic floor (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/LogMoebiusHarmonicFloor.lean`

- `harmonicFloorMoebiusSum_eq_one_real` — the tree's exact Möbius inversion of the polar unit,
  `∑_{d ≤ N} μ(d) H_{⌊N/d⌋}/d = 1` (`RHTower.harmonicFloorMoebiusSum_eq_one`, already owned), cast
  from `ℚ` to `ℝ`.
- `sum_moebius_log_div_eq_one_sub_error` — **the exact identity**
  ```
  ∑_{d ≤ N} (μ(d)/d) log(N/d)  =  1 − ∑_{d ≤ N} (μ(d)/d)( H_{⌊N/d⌋} − log(N/d) ).
  ```

The whole content of step 6 is now isolated in one error sum, with no estimate yet made.  Note the
crude route through it is *not* enough: bounding `|μ(d)| ≤ 1` and `|H_{⌊N/d⌋} − log(N/d)| ≤ 1+log 2`
termwise gives only `O(log N)`, whereas Graham needs `O(1)`.  The `O(1)` requires the cancellation
of `μ` against the harmonic-floor defect — which is exactly the Barban–Vehov content, and is what
remains.

### Ledger

Everything from this error sum upwards — Graham steps 1–5, the coefficient estimate's three ranges,
the mollified second moment reduction, the Hardy-`Z` AFE and its cell bounds, the grid count, and
`SuperlinearSamples xiRealDivisor → (23)` — is Lean-certified and axiom-clean.  The single open item
is the `O(1)` bound for
```
∑_{d ≤ N} (μ(d)/d)( H_{⌊N/d⌋} − log(N/d) ).
```

## Landed brick 27: the pointwise harmonic-floor defect (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/HarmonicFloorDefect.lean`

- `two_mul_natDiv_mul_ge` — `N ≤ 2 ⌊N/d⌋ d` for `1 ≤ d ≤ N`.
- `abs_harmonic_floor_defect_le` — **the pointwise defect bound**
  ```
  | H_{⌊N/d⌋} − log(N/d) − γ | ≤ 2/⌊N/d⌋      for 1 ≤ d ≤ N,
  ```
  combining the tree's `HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le`
  (`|H_n − log n − γ| ≤ 1/n`, already owned) with the floor defect of the logarithm,
  `log(N/d) − log⌊N/d⌋ ≤ 1/⌊N/d⌋` (from `log x ≤ x − 1` and `N/d − ⌊N/d⌋ < 1`).

### Step 6 is now a two-line assembly

Writing the error sum of brick 26 as `γ ∑_{d≤N} μ(d)/d + ∑_{d≤N}(μ(d)/d) R_d` with
`R_d = H_{⌊N/d⌋} − log(N/d) − γ`:

* the first term is bounded by `γ` — the tree owns `|∑_{d≤N} μ(d)/d| ≤ 1`
  (`RHTower.abs_sum_moebius_div_le_one`);
* the second is bounded termwise by brick 27 plus `two_mul_natDiv_mul_ge`:
  `|R_d| ≤ 2/⌊N/d⌋ ≤ 4d/N`, so `|(μ(d)/d) R_d| ≤ 4/N`, and there are `N` terms — total `≤ 4`.

Hence `|∑_{d≤N}(μ(d)/d) log(N/d)| ≤ 1 + γ + 4`, an explicit `O(1)`.  Note this **is** the `O(1)`
the earlier note said the crude route could not reach: the crude route bounded the log-floor defect
by `log 2` and summed `1/d`; the sharp bound `1/⌊N/d⌋ ≤ 2d/N` cancels the `1/d` instead.  Only the
`γ`-term needs Möbius cancellation, and that is exactly `abs_sum_moebius_div_le_one`.

## Landed brick 28: Graham step six is closed (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/LogMoebiusBounded.lean`

- `abs_sum_moebius_log_div_le` — **the logarithmic Möbius sum is bounded by an absolute
  constant**:
  ```
  | ∑_{d ≤ N} μ(d) log(N/d) / d |  ≤  5 + |γ|      for every N ≥ 1.
  ```
  Assembly: the exact identity of brick 26 splits the error sum as
  `γ·∑_{d≤N} μ(d)/d + ∑_{d≤N}(μ(d)/d) R_d` with `R_d = H_{⌊N/d⌋} − log(N/d) − γ`; the first term is
  `≤ |γ|` by the tree's `abs_sum_moebius_div_le_one`; the second is `≤ 4` because
  `|R_d| ≤ 2/⌊N/d⌋ ≤ 4d/N` (brick 27 + `two_mul_natDiv_mul_ge`) kills the `1/d`, leaving `4/N` on
  each of the `N` terms.

Axiom-clean, like the rest of the stack.

### Graham ledger, updated

| step | content | status |
|---|---|---|
| 1 | expand the square into the lcm quadratic form | brick 21 ✔ |
| 2 | remove the floor, error `O(X² log²X)` | brick 22 ✔ |
| 3 | totient/gcd diagonalisation into a sum of squares | brick 23 ✔ |
| 4 | reindex the inner sums, `μ(e)` factors out | brick 24 ✔ |
| 5 | support: squarefree `e ≤ X` only | brick 25 ✔ |
| 6 | bound the one-dimensional logarithmic Möbius sum | bricks 26–28 ✔ |

What remains is the **coprime-class refinement of step 6**: the diagonal sums are
`∑_{j ≤ X/e, (e,j)=1} μ(j) log((X/e)/j)/j`, i.e. the same sum restricted to residues coprime to `e`.
Brick 28 is the case `e = 1`.  The general case follows the same route once the identity
`∑_{d ≤ y, (e,d)=1} μ(d) H_{⌊y/d⌋}/d = ∏_{p ∣ e}(…)`-style substitute is set up — the coprimality
being carried by an extra Möbius factor over the divisors of `e`.

## Landed brick 29: the totient weight of the diagonal (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/TotientDiagonalWeight.lean`

- `sum_totient_div_sq_le` — `∑_{e ≤ N} φ(e)/e² ≤ ∑_{e ≤ N} 1/e`, from `Nat.totient_le`.
- `sum_totient_diagonal_le` — **the diagonal bound against a uniform inner bound**: if
  `|T e| ≤ C` for all `e ≤ N`, then
  ```
  ∑_{e ≤ N} (φ(e)/e²) (T e)²  ≤  C² ∑_{e ≤ N} 1/e .
  ```

This is the second of the two inputs of Graham's evaluation, and it makes the shape of the
remaining work explicit: with `T e := ∑_{j ≤ X/e, (e,j)=1} μ(j) log((X/e)/j)/j`, the diagonal is
`≤ C² (1 + log X)` as soon as `|T e| ≤ C` uniformly.  For the mollified second moment an **upper**
bound of this shape is all that is needed — no asymptotic constant.

### The one remaining item

A uniform `O(1)` bound for the coprime-class sum `T e`.  Brick 28 is the case `e = 1`.  The general
case follows the same three-line route once the coprime analogue of the Möbius–harmonic inversion
is in place:
```
∑_{d ≤ y, (d,e)=1} (μ(d)/d) · H_e(⌊y/d⌋)  =  1 ,      H_e(z) := ∑_{k ≤ z, (k,e)=1} 1/k ,
```
which is the same double-counting as `harmonicFloorMoebiusSum_eq_one` with the multiplicative
splitting `(dk, e) = 1 ↔ (d,e) = 1 ∧ (k,e) = 1`.  That identity plus the same defect estimate closes
`T e`, hence Graham, hence the coefficient estimate, hence the mollified second moment, hence
`(22)`.

## Landed brick 30: the coprime Möbius–harmonic inversion (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeMoebiusHarmonic.lean`

- `coprimeHarmonic e z := ∑_{k ≤ z, (e,k)=1} 1/k`.
- `sum_moebius_coprime_harmonic_eq_one` — **the coprime inversion of the polar unit**: for every
  modulus `e` and every `N ≥ 1`,
  ```
  ∑_{d ≤ N, (e,d)=1} (μ(d)/d) · H_e(⌊N/d⌋)  =  1 .
  ```
  Proof: the tree's `Sieve.sum_divisors_swap` applied to
  `G d k = [ (e,d)=1 ∧ (e,k)=1 ] · μ(d)/(dk)`, using multiplicativity of coprimality
  `(e, d k) = 1 ↔ (e,d) = 1 ∧ (e,k) = 1` (`Nat.Coprime.mul_right` and
  `Nat.Coprime.coprime_dvd_right`) to collapse the inner divisor sum to `[m = 1]` by
  `sum_divisors_moebius_real`.

This is the coprime-class analogue of `harmonicFloorMoebiusSum_eq_one`, i.e. exactly the identity
brick 26 used for `e = 1`.  With it, the brick 26 → 27 → 28 chain runs verbatim for every modulus:
the exact identity, the pointwise harmonic-floor defect, and the `|∑ μ(d)/d| ≤ 1` cancellation.

### Remaining

The coprime analogues of the two quantitative inputs of brick 28:
`|∑_{d ≤ N, (e,d)=1} μ(d)/d| ≤ 1` and the coprime harmonic defect
`|H_e(⌊N/d⌋) − (φ(e)/e) log(N/d) − γ_e| ≤ …`.  Both follow the same elementary route as their
`e = 1` cases, which are already Lean-certified.

## Landed brick 31: basic bounds for the coprime harmonic sum (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeHarmonicBounds.lean`

- `coprimeHarmonic_nonneg`, `coprimeHarmonic_le` (dominated by the full harmonic sum),
  `one_le_coprimeHarmonic` (`≥ 1` once the window is nonempty, since `k = 1` is coprime to every
  modulus).

### Course correction on the last input

The plan recorded at brick 30 — prove `|∑_{d ≤ N, (e,d)=1} μ(d)/d| ≤ 1` uniformly, by copying the
`e = 1` argument — does **not** work, and the reason is worth recording so it is not re-attempted.
The `e = 1` proof (`abs_sum_moebius_div_le_one`) runs through
`∑_{d ≤ N} μ(d)⌊N/d⌋ = 1` and bounds the fractional-part sum by `N`.  Its coprime analogue is
`∑_{d ≤ N,(e,d)=1} μ(d) C_e(⌊N/d⌋) = 1` with `C_e(z) = #{k ≤ z : (e,k)=1}`, and
`C_e(z) = (φ(e)/e) z + O(2^{ω(e)})`: the error carries `2^{ω(e)}`, which is **not** bounded
uniformly in `e`.  So the fractional-part route gives no uniform constant.

The correct target is weaker and does suffice.  In the final assembly the diagonal is
`∑_e (φ(e)/e²) T_e², so by brick 29 a modulus-dependent bound `|T_e| ≤ A · e/φ(e)` is enough:
```
∑_{e ≤ X} (φ(e)/e²)·(A e/φ(e))²  =  A² ∑_{e ≤ X} 1/φ(e)  ≍  A² log X ,
```
which is exactly the `O(log X)` Graham needs.  So the remaining item is
```
|T_e(y)| ≤ A · e/φ(e)        uniformly in e and y,
```
with `T_e(y) = ∑_{j ≤ y, (e,j)=1} μ(j) log(y/j)/j` — the natural normalisation, since `H_e` itself
carries the factor `φ(e)/e`.  Brick 30's coprime inversion plus the brick 27 defect estimate is the
route; what it needs in addition is the coprime harmonic asymptotic
`H_e(z) = (φ(e)/e)(log z + γ_e) + O(2^{ω(e)}/z)`, whose main term is what supplies the `φ(e)/e`.

## Landed brick 32: the coprime harmonic decomposition (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeHarmonicDecomposition.lean`

- `coprimeHarmonic_eq_sum_divisors` — **the exact identity**
  ```
  H_e(z)  =  ∑_{f ∣ e} (μ(f)/f) · H(⌊z/f⌋) .
  ```
  Proof: detect coprimality by `[(e,k)=1] = ∑_{f ∣ (e,k)} μ(f)` (`sum_divisors_moebius_real`),
  swap with `Finset.sum_comm'` through `f ∣ (e,k) ↔ f ∣ e ∧ f ∣ k`, and reindex the multiples of
  `f` with brick 24's `sum_filter_dvd_eq_sum_scaled`.

This is the identity whose main term carries the factor `∑_{f ∣ e} μ(f)/f = φ(e)/e`, i.e. exactly
the normalisation the course correction at brick 31 identified as the right target.  Feeding
`H(m) = log m + γ + O(1/m)` (the tree's `abs_harmonic_sub_log_sub_eulerMascheroni_le`) into it gives
the coprime harmonic asymptotic termwise, with a divisor-indexed error — `d(e)` terms, each
`O(f/z)`, which is where the `2^{ω(e)}` of the course-correction note comes from and why the
`e/φ(e)` normalisation is the right one to carry.

### Remaining

Assemble: `H_e(⌊y/d⌋) = (φ(e)/e)(log(y/d) + γ) − ∑_{f ∣ e}(μ(f)/f)log f + (error)`, then run the
brick 26 → 28 argument at the modulus `e` to get `|T_e(y)| ≤ A·e/φ(e)`, then brick 29 turns that
into the `O(log X)` diagonal bound, closing Graham and with it the coefficient estimate, the
mollified second moment, and `(22)`.

## Landed brick 33: the totient normalisation identity (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/TotientMoebiusNormalisation.lean`

- `totient_eq_sum_moebius_mul` — `φ(n) = ∑_{a ∣ n} μ(a)(n/a)`, by Möbius inversion of
  `∑_{d ∣ n} φ(d) = n` (mathlib's `Nat.sum_totient` through
  `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` and `Nat.sum_divisorsAntidiagonal`).
- `sum_moebius_div_divisors_eq_totient_div` — **the normalisation identity**
  `∑_{a ∣ n} μ(a)/a = φ(n)/n`.

Combined with brick 32 this makes the main term of the coprime harmonic decomposition explicit:
```
H_e(z) = ∑_{f ∣ e} (μ(f)/f) H(⌊z/f⌋)
       = (φ(e)/e)(log z + γ) − ∑_{f ∣ e} (μ(f)/f) log f + (divisor-indexed error),
```
the `φ(e)/e` coming from `∑_{f ∣ e} μ(f)/f` exactly.

### Remaining

Estimate the two leftovers of that expansion — the `log f` term and the divisor-indexed error, each
a sum over `d(e)` divisors — and feed the result through the brick 26 → 28 argument at modulus `e`
to obtain `|T_e(y)| ≤ A·e/φ(e)`.  Brick 29 then converts that into the `O(log X)` diagonal bound,
closing Graham, the coefficient estimate, the mollified second moment, and `(22)`.

## Landed brick 34: centering the coprime harmonic decomposition (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeHarmonicCentering.lean`

- `coprimeHarmonic_sub_totient_mul` — for every constant `C` and every `e > 0`,
  ```
  H_e(z) − (φ(e)/e)·C  =  ∑_{f ∣ e} (μ(f)/f) · ( H(⌊z/f⌋) − C ) .
  ```
  Exact, from bricks 32 (decomposition) and 33 (normalisation).

Taking `C = log z + γ` puts the coprime harmonic asymptotic in the exact form
```
H_e(z) − (φ(e)/e)(log z + γ)  =  ∑_{f ∣ e} (μ(f)/f)·( H(⌊z/f⌋) − log z − γ ) ,
```
with each summand `= (H(m) − log m − γ) + (log m − log z)`, `m = ⌊z/f⌋` — the first piece bounded by
`1/m` (mathlib, already used in brick 27) and the second essentially `−log f`.  So the two leftovers
named at brick 33 are now literally the two halves of one divisor-indexed sum, with a free choice of
centering constant.

### Remaining

Bound that divisor-indexed sum by `A·e/φ(e)`, then run brick 26 → 28 at modulus `e` and brick 29.

## Landed brick 35: the harmonic bridge and the centered divisor defect (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeHarmonicDefect.lean`

- `harmonic_eq_sum_Icc` — `(harmonic n : ℝ) = ∑_{j ≤ n} 1/j`, by induction with `harmonic_succ`
  and `Finset.sum_Icc_succ_top`.  This bridges the two notations used by the two halves of the
  programme: the coprime decomposition is written with interval sums, the tree's harmonic
  comparison with `harmonic`.
- `abs_coprime_centered_term_le` — **each divisor contributes at most `4/z`**:
  ```
  | (μ(f)/f)·( H(⌊z/f⌋) − (log z + γ) + log f ) | ≤ 4/z      for 1 ≤ f ≤ z,
  ```
  by splitting `log(z/f) = log z − log f`, applying brick 27's defect bound and
  `2/⌊z/f⌋ ≤ 4f/z`.
- `abs_coprime_centered_sum_le` — summing, `≤ d(e)·(4/z)` for `0 < e ≤ z`.

Combined with brick 34 this is the coprime harmonic asymptotic in explicit form:
```
| H_e(z) − (φ(e)/e)(log z + γ) + ∑_{f ∣ e} (μ(f)/f) log f |  ≤  4 d(e)/z .
```
The `2^{ω(e)}`-type error of the course-correction note is now concrete: it is `d(e)`, and it is
divided by `z`, so it is harmless once `z` exceeds `e` by a polynomial factor.

### Remaining

The `∑_{f ∣ e}(μ(f)/f) log f` term (the modulus-dependent constant `γ_e`), then the brick 26 → 28
argument at modulus `e`, then brick 29.

## Landed brick 36: the modulus constant of the coprime asymptotic (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeModulusConstant.lean`

- `divisors_subset_Icc`, `sum_inv_divisors_le` — `∑_{f ∣ e} 1/f ≤ ∑_{j ≤ e} 1/j`.
- `abs_sum_moebius_log_div_divisors_le` — **the modulus constant is bounded**:
  ```
  | γ_e |  =  | ∑_{f ∣ e} (μ(f)/f) log f |  ≤  log e · ∑_{f ∣ e} 1/f .
  ```

With bricks 34 and 35 the coprime harmonic asymptotic is now fully explicit and fully bounded:
```
H_e(z) = (φ(e)/e)(log z + γ) − γ_e + θ,     |θ| ≤ 4 d(e)/z,   |γ_e| ≤ log e · ∑_{f ∣ e} 1/f .
```

### Remaining

Run the brick 26 → 28 argument at modulus `e`, using brick 30's coprime inversion in place of
`harmonicFloorMoebiusSum_eq_one` and the display above in place of brick 27, to obtain
`|T_e(y)| ≤ A · e/φ(e)`; then brick 29 turns that into the `O(log X)` diagonal bound, closing
Graham → coefficient estimate → mollified second moment → `(22)`.

## Landed brick 37: the exact identity at a general modulus (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeLogMoebiusIdentity.lean`

- `sum_coprime_moebius_log_eq_one_sub_error` — for every modulus `e`, every `N ≥ 1` and every
  centering weight `c`,
  ```
  ∑_{d ≤ N, (e,d)=1} (μ(d)/d)·c·log(N/d)
      = 1 − ∑_{d ≤ N, (e,d)=1} (μ(d)/d)·( H_e(⌊N/d⌋) − c·log(N/d) ) .
  ```
  This is the modulus-`e` analogue of brick 26, obtained from brick 30's coprime inversion by the
  same one-line split.  Taking `c = φ(e)/e` makes the defect exactly the quantity bounded by
  bricks 34–36.

The brick 26 → 28 chain is therefore reproduced at every modulus except for its final quantitative
step: the identity is brick 37, the pointwise defect is bricks 34–36, and what is left is the
modulus-`e` analogue of `abs_sum_moebius_div_le_one`, weighted appropriately — recall from the
brick 31 course correction that the target is `A·e/φ(e)`, not an absolute constant.

## Landed brick 38: the coprime counting identity (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeCounting.lean`

- `coprimeCount_eq_sum_divisors` — **the exact identity**
  ```
  #{ k ≤ z : (e,k) = 1 }  =  ∑_{f ∣ e} μ(f) ⌊z/f⌋ ,
  ```
  by the same detector-and-swap as brick 32, with the multiple count supplied by brick 21's
  `card_filter_dvd_Icc`.

This is the counting analogue of brick 32 and the source of the density `φ(e)/e`: replacing
`⌊z/f⌋` by `z/f` gives `(φ(e)/e)z` through brick 33's normalisation, with an error of at most `d(e)`
fractional parts.

### A second course correction, recorded

The obvious route to the remaining bound — mimic `abs_sum_moebius_div_le_one` at modulus `e` using
this identity — yields
```
| ∑_{d ≤ N, (e,d)=1} μ(d)/d |  ≤  (e/φ(e)) · ( 1/N + d(e) ) ,
```
because the fractional-part error of `coprimeCount_eq_sum_divisors` is `d(e)`, not `1`.  Feeding
that into brick 29 gives `∑_e d(e)²/φ(e) ≍ (log X)^5`, not `log X` — so this route, like the one
retired at brick 31, is **too lossy**.  Both failures have the same source: any argument that
bounds the `d(e)` divisor terms individually loses a power of `log` per divisor.  The remaining
bound therefore requires cancellation *across* the divisors of `e`, which is exactly the
Barban–Vehov content and the last genuinely analytic step of the programme.

## Landed brick 39: peeling one prime off a coprimality class (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimePrimePeeling.lean`

- `sum_filter_coprime_split` — for every prime `p`, every modulus `e` and every weight `g`,
  ```
  ∑_{j ≤ y, (e,j)=1} g(j)
      = ∑_{j ≤ y, (pe,j)=1} g(j) + ∑_{j ≤ y, (e,j)=1, p ∣ j} g(j) ,
  ```
  from `Finset.sum_filter_add_sum_filter_not` on the predicate `(p,j)=1`, together with
  `Nat.coprime_mul_iff_left` and `Nat.Prime.coprime_iff_not_dvd`.

**Why this is the right mechanism.**  Both retired routes (bricks 31 and 38) treated the `d(e)`
divisors of the modulus one at a time and lost a `log` on each.  Prime peeling instead removes one
prime at a time and, on the Möbius weight, the removed piece re-enters with the *opposite sign*:
for `p ∣ j`, `j = p j'`, one has `μ(j) = −μ(j')` whenever `p ∤ j'` and `μ(j) = 0` otherwise, so
```
S_{pe}(y) = S_e(y) + ∑_{j' ≤ y/p, (pe,j')=1} μ(j') g(p j') ,
```
a genuine recursion in which the corrections telescope across the primes of `e` rather than being
summed absolutely.  That is the cancellation the Barban–Vehov bound needs.

### Remaining

The Möbius specialisation of the split (the sign flip `μ(p j') = −μ(j')` plus the reindexing
`j = p j'`), then the induction over the prime factors of `e` to reach `|T_e| ≤ A·e/φ(e)`, then
brick 29.

## Landed brick 40: reindexing the peeled part (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimePeeledReindex.lean`

- `sum_filter_coprime_dvd_reindex` — for a prime `p` with `p ∤ e`,
  ```
  ∑_{j ≤ y, (e,j)=1, p ∣ j} F(j)  =  ∑_{j ≤ y/p, (e,j)=1} F(p j) ,
  ```
  by `Finset.sum_nbij'` with the mutually inverse maps `j ↦ j/p` and `j ↦ p j`.

Together with brick 39 the prime-peeling recursion is now exact at the level of arbitrary weights:
```
∑_{j ≤ y, (e,j)=1} F(j)  =  ∑_{j ≤ y, (pe,j)=1} F(j)  +  ∑_{j ≤ y/p, (e,j)=1} F(p j) .
```

### Remaining

Specialise `F(j) = μ(j) g(j)`: the second sum then carries `μ(pj) = −μ(j)` on `p ∤ j` and vanishes
on `p ∣ j`, turning the recursion into the sign-alternating form whose corrections telescope.  Then
induct over the prime factors of `e` for `|T_e| ≤ A·e/φ(e)`, and apply brick 29.

## Landed brick 41: the Möbius prime-peeling recursion (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusPrimePeeling.lean`

- `sum_moebius_peel` — for a prime `p` with `p ∤ e`, and every weight `g`,
  ```
  ∑_{j ≤ y, (e,j)=1} μ(j) g(j)
      =  ∑_{j ≤ y, (pe,j)=1} μ(j) g(j)  −  ∑_{j ≤ y/p, (pe,j)=1} μ(j) g(p j) .
  ```
  Proof: peel with bricks 39–40 at height `y`, split the peeled part again at height `y/p`, kill
  the `p ∣ j` piece by `μ(pj) = 0` (brick 24), and flip the sign of the rest by
  `μ(pj) = μ(p)μ(j) = −μ(j)` on `(p,j)=1` (brick 24 plus `moebius_apply_prime`).

This is the sign-alternating recursion: the correction enters with a minus sign and at height
`y/p`, so peeling all primes of `e` produces a telescoping alternating sum rather than `d(e)`
separately-estimated terms.  Axiom-clean, together with the rest of the coprime stack.

### Remaining

Induct on the prime factorisation of `e` with this recursion to obtain `|T_e(y)| ≤ A·e/φ(e)`
(the base case `e = 1` is brick 28), then apply brick 29 for the `O(log X)` diagonal, closing
Graham → the coefficient estimate → the mollified second moment → `(22)`.

## Landed bricks 42–43: the uniform coprime bound `|T_e| ≤ A·e/φ(e)` (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeLogMoebiusRecursion.lean`
`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeLogMoebiusUniformBound.lean`

- `coprimeLogMoebius e Y = ∑_{j ≤ ⌊Y⌋, (e,j)=1} μ(j) log(Y/j)/j` — the target functional, with a
  *real* cutoff so that the recursion can divide it.
- `coprimeLogMoebius_recursion` — feeding brick 41 the weight `g(j) = log(Y/j)/j` and using
  `log(Y/(pj))/(pj) = (1/p)·log((Y/p)/j)/j` together with `⌊Y⌋/p = ⌊Y/p⌋`
  (`Nat.floor_div_natCast`) gives the **contraction**
  ```
  T_e(Y) = T_{pe}(Y) − (1/p)·T_{pe}(Y/p) ,   i.e.   T_{pe}(Y) = T_e(Y) + (1/p)·T_{pe}(Y/p).
  ```
  The correction is not merely signed: it sits at the *reduced cutoff* `Y/p`.
- `abs_coprimeLogMoebius_one_le` — the modulus-one bound at a real cutoff: splitting
  `log(Y/d) = log(N/d) + log(Y/N)` with `N = ⌊Y⌋` and using `|∑_{d≤N}μ(d)/d| ≤ 1` costs one unit
  over brick 28, so `|T_1(Y)| ≤ 6 + |γ| =: A`.
- `abs_coprimeLogMoebius_prime_step` — unfolding the contraction in the cutoff (induction on
  `⌊Y⌋`, using `⌊Y/p⌋ ≤ ⌊Y⌋/2`) turns a uniform bound `C` at modulus `e` into the uniform bound
  `C·(1−1/p)^{-1}` at modulus `pe`.  This is the geometric series `∑_k p^{-k}` in disguise.
- `abs_coprimeLogMoebius_le` — inducting on the prime factorisation of a squarefree modulus,
  ```
  |T_e(Y)| ≤ (6 + |γ|) · e/φ(e)     for every squarefree e and every Y,
  ```
  since `∏_{p ∣ e}(1−1/p)^{-1} = e/φ(e)`.

This is exactly the target set by the course correction at brick 31, and it is reached without ever
estimating the `d(e)` divisor terms of the modulus one at a time — the failure mode that retired the
routes at bricks 31 and 38.

## Landed bricks 44–45: the reciprocal totient sum is logarithmic (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTotientDivisorIdentity.lean`
`formal/GaloisForLFunctions/RHTower/Sieve/ReciprocalTotientLogBound.lean`

The bound `|T_e| ≤ A e/φ(e)` turns the Selberg diagonal `∑_e (φ(e)/e²)·μ(e)²T_e²` into
`A²∑_{e ≤ X} μ²(e)/φ(e)`, so Graham's `O(log X)` needs the classical estimate
`∑_{e ≤ N} 1/φ(e) ≪ log N`.  It is proved here from one multiplicative identity, applied twice:

- `sum_divisors_sqfreeTotientInv` — `∑_{d ∣ n} μ²(d)/φ(d) = n/φ(n)`, by comparing the two
  multiplicative functions `μ²/φ` (convolved with `ζ`) and `n ↦ n/φ(n)` on prime powers, where both
  equal `p/(p−1)` because only `d = 1` and `d = p` survive the squarefree support.
- `sum_sqfreeTotientInv_div_le` — `∑_{d ≤ N} μ²(d)/(dφ(d)) ≤ 4`.  Writing
  `1/(dφ(d)) = (1/d²)(d/φ(d))`, the identity and the divisor swap turn the sum into
  `∑_{k ≤ N}(μ²(k)/(kφ(k)))·k^{-1}·∑_{j ≤ N/k} j^{-2}`, and both reciprocal-square sums are `≤ 2`.
- `sum_inv_totient_le` — `∑_{e ≤ N} 1/φ(e) ≤ 4(1 + log N)`, by the same swap with the harmonic sum
  in the inner slot and the previous bound in the outer one.

No Mertens estimate, no Euler product over primes, and no lower bound for `φ` is needed: two
applications of one divisor identity suffice.

### Remaining

Assemble: the inner sums of the Selberg diagonalisation are `(μ(e)/e)·T_e(X/e)`, hence bounded by
`A/φ(e)` and supported on `e ≤ X`; brick 23 plus the bound above then closes Graham's evaluation,
and with bricks 21–22 the mean square `∑_{k ≤ N} b_X(k)² ≪ N log X + X² log²X`.

## Landed bricks 46–47: **Graham's theorem is closed** (2026-08-18)

`formal/GaloisForLFunctions/RHTower/Sieve/SelbergMoebiusLogDiagonal.lean`
`formal/GaloisForLFunctions/RHTower/Sieve/GrahamMeanSquare.lean`

- `barbanVehov_inner_eq` — the inner sums of the Selberg diagonalisation are exactly the coprime
  logarithmic Möbius sums at the divided cutoff:
  ```
  ∑_{m ≤ N, e ∣ m} μ(m) log(X/m)/m  =  (μ(e)/e) · T_e(X/e)      (X ≤ N).
  ```
  Reindex `m = e j` with brick 24, drop the terms `e j > X` (the truncation kills them), and use
  `X/(ej) = (X/e)/j` with `⌊X/e⌋ = X/e`.
- `abs_barbanVehov_inner_le` — hence `|inner_e| ≤ A/φ(e)`, by `|μ(e)| ≤ 1` and bricks 42–43.
- `barbanVehov_inner_eq_zero` — the inner sums vanish for `e > X`, because the cutoff `X/e` drops
  below `1`.
- `barbanVehov_totient_diagonal_le` — the totient-weighted diagonal:
  ```
  ∑_{e ≤ N} φ(e)·(inner_e)²  ≤  A² ∑_{e ≤ X} 1/φ(e)  ≤  4A²(1 + log X).
  ```
- `sum_sq_barbanVehovCoeff_le` — **Graham's mean square, upper half**:
  ```
  ∑_{k ≤ N} ( ∑_{m ∣ k, m ≤ X} μ(m) log(X/m) )²  ≤  4A²·N·(1 + log X)  +  X² log²X
  ```
  for every `1 ≤ X ≤ N`, with `A = 6 + |γ|`.  Assembly: brick 21 expands the square into the lcm
  quadratic form, brick 22 removes the floor at the cost of the square of the `ℓ¹` mass
  (`≤ X log X`), brick 23 diagonalises, and the display above bounds the diagonal.

Axiom-clean.  **This closes the last named analytic input of the Graham ledger**; the whole ledger
(steps 1–6 plus the coprime-class refinement) is now Lean-certified with no hypothesis beyond
`1 ≤ X ≤ N`.

### Remaining

Graham → the mollified coefficient estimate → the mollified second moment `∫_T^{2T}|ζM|² ≪ T` →
`GridCancellationSurplus` → `(22)` → `(23)`.

## Landed brick 48, and a course correction that removes the Conrey computation (2026-08-19)

`formal/GaloisForLFunctions/RHTower/Sieve/HarmonicWeightedGrahamMeanSquare.lean`

- `sum_weighted_sq_divisorSum_eq_lcm_quadratic` — brick 21 with an arbitrary weight attached:
  `∑_{k ≤ N} w(k)(∑_{m ∣ k}a_m)² = ∑_{m₁,m₂ ≤ N}a_{m₁}a_{m₂}∑_{k ≤ N, [m₁,m₂] ∣ k}w(k)`.
- `sum_dvd_inv_le`, `sum_dvd_inv_ge` — the harmonic mass of the multiples of `d`:
  `(log N − log d)/d ≤ ∑_{k ≤ N, d ∣ k}1/k ≤ (1 + log N)/d`, from `log(⌊N/d⌋+1) ≤ H_{⌊N/d⌋} ≤
  1 + log⌊N/d⌋` and `⌊N/d⌋ + 1 > N/d`.
- `sum_harmonic_sq_divisorSum_le` — **the harmonic-weighted mean square**: for coefficients
  supported on `m ≤ X`,
  ```
  ∑_{k ≤ N} (∑_{m ∣ k}a_m)²/k  ≤  (1 + log N)·∑_{m₁,m₂}a_{m₁}a_{m₂}/[m₁,m₂]
                                   + (1 + 2log X)·(∑_m |a_m|)² ,
  ```
  because the defect `(1+log N)/d − ∑_{k≤N,d∣k}1/k` lies in `[0, (1+log d)/d]` and `d = [m₁,m₂] ≤ X²`
  on the support.  The defect therefore costs a quantity that does **not** grow with the outer
  range `N`.
- `sum_harmonic_sq_barbanVehovCoeff_le` — with brick 46,
  ```
  ∑_{k ≤ N} b_X(k)²/k  ≤  4A²(1 + log N)(1 + log X)  +  (1 + 2log X)(X log X)² .
  ```

### The course correction

The programme recorded at bricks 13–20 assumed the mollifier length must be `X = T^θ` and hence
that the full Conrey computation (`∫_T^{2T}|ζM|² ≪ T`) was needed.  It is not, for this target.

The goal `(22)` is `SuperlinearSamples`, i.e. `∀ c, ∃ T, c·T < N₀(T)` — the mollifier may therefore
be chosen **depending on `c`**, and in particular may have *fixed length* `X = X(c)`.  Running the
mean-square grid device with a fixed-length mollifier:

* `L ≈ T` from the first moment (`c₁ = 1` dominates),
* `Q ≤ H·∫_T^{2T}|ζM|²  ≈ H·T·λ`  with `λ = ∑_k |c_k|²`,
* the surplus condition `c·T·Q < (L − Bsum)²` needs `H < 1/(4cλ)`,
* the cell must contain many oscillations, i.e. `H·log T ≫ 1`, i.e. `log T ≫ 4cλ`.

With the fixed-length linear mollifier `a_m = μ(m)log(X/m)/log X` the display above gives
```
λ  =  ∑_k |c_k|²  ≤  4A²(1 + log K)(1 + log X)/log²X + C(X)  ≈  4A²·log K/log X + C(X),
```
and `log K ≍ log T`, so `4cλ ≍ c·log T/log X`: the oscillation condition becomes
`log X ≫ 4A²c`, i.e. **a fixed `X = X(c)` suffices**.  The `X`-dependent additive constant `C(X)`
is harmless because it does not grow with `T`.

So the last genuinely open input is *not* the Conrey/Balasubramanian–Conrey–Heath-Brown asymptotic;
it is only the (already-owned) Graham diagonal bound plus the harmonic-weighted defect of brick 48.
What remains is the analytic assembly: the mollified mean square through the AFE and the Dirichlet
mean-value theorem, the first-moment lower bound, and the cell cancellation.

## Route audit after Graham: where the two remaining routes actually stand (2026-08-19)

With Graham's theorem closed (bricks 46–48) the coefficient side of the programme is finished.  A
careful audit of what is left shows that the two available routes to `(23)` are separated by a
genuine analytic barrier, and it is worth recording exactly where it sits.

### Route 1 — `(22)` through the grid device

The device needs, for cells `I_j` of length `H`,
```
∑_j |∫_{I_j} Z·W|  <  ∫_T^{2T}|Z|·W  −  (superlinear margin) ,     W = |M|² + ε > 0 .
```
Using the Hardy-`Z` smooth AFE and the tree's per-term cell bounds (bricks 6–10) the left side is
bounded **term by term** by
```
∑_{n ≤ x} n^{-1/2}·min(H, 2/δ_n) ,      δ_n = |θ'(τ) − log n| ,
```
and this is `≍ √x ≍ T^{1/4}` for the balanced AFE, whatever `H` is: the terms with `n` near the
conductor `x = √(t/2π)` have `δ_n → 0` and are only saved by the trivial bound.  Summed over the
`T/H` cells that gives `T^{5/4}/H`, so the device closes only for `H ≫ T^{1/4}`, i.e. only
`N₀(T) ≫ T^{3/4}` — sublinear, hence useless for `(22)`.

**This is a barrier of the estimation method, not of the device.**  The device is sharp; what the
term-by-term bound throws away is the cancellation *among* the AFE terms near the conductor, which
is exactly the content of Selberg's theorem.  Any continuation of Route 1 must supply a bound for
`∑_j|∫_{I_j}ZW|` that is not a triangle inequality over `n` — i.e. Selberg's mollified-moment
machinery.  The fixed-length-mollifier simplification recorded at brick 48 remains valid and
removes the Conrey computation, but it does not remove this barrier.

### Route 2 — `(23)` through progression-freeness

`RHTower/SamplingProgressionCriterion.lean` already reduces `(23)`, unconditionally, to
```
hnoAP : ∀ b k, 0 < k → ∃ n : ℕ, b + n·k ∉ xiRealDivisor,
```
i.e. the real zeros of `Ξ` contain no infinite one-sided arithmetic progression (Putnam 1954).
This is strictly weaker than `(22)` and is the shorter route.

**What the corpus already gives.**  `RHTower/PrimeArchThetaFirstMoment.lean` owns the exact
positive-source cosine representation
```
Xi t = 2 ∫_{x > 0} thetaCuspFullSource x · cos(t x) dx ,      thetaCuspFullSource x > 0 (x > 0),
```
with the source Schwartz (`thetaCuspSchwartzReal`) and super-exponentially decaying.  Writing `Φ`
for the even extension, `Ξ = Φ̂`, and Poisson summation over an arithmetic progression gives, for a
**two-sided** progression `a + hℤ` of zeros,
```
0 = ∑_{n ∈ ℤ} Ξ(a+nh) = (2π/h)·∑_{k ∈ ℤ} Φ(2πk/h)·e^{2πika/h} .
```
Since `Φ > 0` and `Φ` decays like `exp(−π e^{2|u|})`, the `k = 0` term dominates as soon as
`2π/h` is not too small, and the right-hand side is nonzero — a contradiction.  So **two-sided
progressions with step below an explicit threshold are impossible**, unconditionally and by an
elementary argument.

**Why this does not yet close `hnoAP`, stated precisely.**

1. *One-sidedness.*  For a one-sided progression the Poisson identity gives only that the
   periodization `P(v) = ∑_k Φ(v + 2πk/h)e^{ia(v+2πk/h)}` has vanishing Fourier coefficients in
   degrees `≤ 0`, i.e. `P ∈ H¹` with spectrum in `n ≥ 1`.  Its value `P(0)` is then
   `(h/2π)∑_{n ≥ 1}Ξ(a−nh)` — the *backward* values, which the hypothesis does not control.  The
   dominance argument bounds `|P(0)|` from below but the matching upper bound
   `|P(0)| ≤ ∑_{n≥1}|c_n|` is lossy by exactly the factor that positivity was supposed to supply.
2. *Large step.*  For `h` large the periodization sums many comparable values of `Φ` and no single
   term dominates; the twisted periodization `∑_k Φ(v+kP₀)ω^k` (with `ω = e^{2πia/h}`) can cancel.
3. *Jensen does not close the gap either.*  For the one-sided case, Jensen's inequality applied to
   `P/z^m ∈ H¹` gives `|Ξ(a−mh)| ≤ (2π/h)exp((1/P₀)∫_0^{P₀}log Q)` with `Q` the periodization of
   `Φ`; the right side is astronomically small but **fixed**, while `Ξ(t) ≍ t^{7/4}e^{−πt/4}|ζ(½+it)|`
   decays super-exponentially, so a progression starting high enough is not excluded.  The
   normalisation is wrong: the natural object for a height-uniform statement is `ζ(½+it)`, which
   does not decay, and the positivity structure lives with `Ξ`, which does.

So the honest open core of Route 2 is: **a height-uniform version of the positivity argument**, or
the explicit-formula route (van Frankenhuijsen) using the tree's
`XiGuinandWeilExplicitFormula`, whose own open core is the treatment of the off-line zeros without
invoking Weil positivity.

### What this session added

Graham's theorem — the last *named* classical input of Route 1 — is Lean-proved unconditionally,
together with the reciprocal-totient estimate `∑_{e ≤ N}1/φ(e) ≤ 4(1+log N)` and the multiplicative
identity `∑_{d ∣ n}μ²(d)/φ(d) = n/φ(n)` that carries it.  These are reusable well beyond this card.

## Landed brick 49: the Poisson trace of `Xi` along an arithmetic progression (2026-08-19)

`formal/GaloisForLFunctions/RHTower/XiPoissonProgression.lean`

The first Lean asset on Route 2.  `Xi = 𝓕 S` with `S = xiThetaSchwartzSource` Schwartz and
`S(0) = 2π·thetaCuspFullSource(0) > 0`, so Poisson summation converts the values of `Xi` along a
progression into the periodisation of the source.

- `isBigO_schwartz_affine` — Schwartz decay survives an affine reparametrisation:
  `y ↦ F(d + cy)` is `O(|y|^{-2})` on the cocompact filter.  Reusable.
- `xiProgressionKernel a h u = (1/h)·e^{-2πiua/h}·S(u/h)` and
  `fourier_xiProgressionKernel` — `𝓕(xiProgressionKernel a h) y = Xi(a + h y)`, by the linear
  change of variables `u = h x` in the Fourier integral.
- `tsum_xiProgressionKernel_eq` — **the Poisson trace**:
  ```
  ∑_{n ∈ ℤ} (1/h)·e^{-2πina/h}·S(n/h)  =  ∑_{n ∈ ℤ} Xi(a + h n) .
  ```
- `thetaCuspFullSource_pos_zero` — the source is strictly positive at the origin (the `n = 1` term
  already is, since `2π > 3`).  This is the positivity input, and the only one.
- `summable_one_add_sq_inv_int`, `summable_xiProgressionKernel` — the summability the split needs.
- `exists_ne_zero_along_progression` — **the theorem**: there is `h₀ > 0` such that for every step
  `0 < h ≤ h₀` and every phase `a` there is `n ∈ ℤ` with `Xi(a + h n) ≠ 0`.  Proof: if all vanished
  the trace would be `0`, so the `n = 0` term `S(0)/h` would be dominated by the rest, which is
  `≤ 2C·h·∑_{n}(1+n²)^{-1}` by the Schwartz bound `‖x‖²‖S(x)‖ ≤ C`; that forces
  `‖S(0)‖ ≤ 2CA h²`, false for small `h`.

Axiom-clean.  Note what the statement does **not** say: it is uniform in the phase `a` (so it is
height-uniform, unlike the Jensen route recorded in the audit) but it needs the step to be small,
and it rules out two-sided progressions only.  The card's `hnoAP` needs one-sided progressions at
every step; the remaining gap is exactly the one the audit isolated.

## Landed brick 50, and the exact literature position of Route 2 (2026-08-19)

### Brick 50: the criterion in length-bound form

`formal/GaloisForLFunctions/RHTower/SamplingBilateralProgression.lean`

- `exists_bilateral_threshold_of_finite_shiftFailure` — on a **symmetric** sample set a finite
  shift failure at step `h` bounds the *backward* failure too, because the backward failure is the
  reflection of the forward one (`backwardFailure_subset_neg_shiftFailure`, already owned).  Hence
  there is one threshold `T` above which the set is closed under both `+h` and `−h`.
- `exists_bilateral_block_of_finite_shiftFailure` — consequently the set carries a two-sided block
  `{b + n h : |n| ≤ M}` of every prescribed length `M`.
- `infinite_shiftFailure_of_no_long_block`, `xiSamplingIdealizer_collapse_of_no_long_block` —
  `(23)` follows from a **length bound**: for each step `h` some length `M(h)` such that no block of
  that length lies in the real `Xi` divisor.  This is the shape in which the literature states the
  corresponding zero-free results.

### The literature position, established (2026-08-19)

- **Putnam (1954)** proves: the positive zeros of `ζ(½+it)` contain no infinite progression
  `{d, 2d, 3d, …}` — the *homogeneous* case.  His proof (recovered from Srichan, *Bull. Aust. Math.
  Soc.* 98 (2018) 376–382, which axiomatises it) is: write
  `ζ(s) = s/(s−1) − s∫_0^∞ B(x)e^{−sx}dx`, `B(x) = {e^x}`, valid for `0 < Re s < 1`; at a zero
  `z`, `A(z) := 1/(z−1) = ∫_0^∞B(x)e^{−zx}dx`; take real parts, extend `B` to the negative axis by
  `B(−x) = B(x)e^{−x}`, and periodise `B(x)e^{−x/2}` with period `2π/d`.  The Fourier coefficients
  of the periodisation are then `O(n^{−2})`, hence absolutely summable, so the periodisation is
  continuous — contradicting the downward jumps of `{e^x}`, which cannot cancel because they all
  have the same sign.
- **Li–Radziwiłł** prove the *inhomogeneous* case: at least one third of the points of any vertical
  progression `½ + i(a+nd)` are **not** zeros, by studying moments of `ζ`.  This is exactly the
  statement `hnoAP` needs, and it is the literature target for Route 2.
- Srichan records explicitly that Putnam's method "does not seem to extend to more general
  arithmetic progressions asymmetrically distributed about the real axis".

### What the audit adds to Putnam's method (recorded for the build)

Working with the *complex* equation instead of its real part removes Putnam's sign condition and
his restriction to the homogeneous case, **for two-sided progressions**.  Put

```
C(x) = B(x)e^{−x/2−iax}   (x ≥ 0),        C(x) = e^{x/2−iax}   (x < 0),
```

and let `D` be the `2π/d`-periodisation of `C`.  Then for **every** `n ∈ ℤ`,

```
∫_0^∞B(x)e^{−z_n x}dx = A(z_n) − ζ(z_n)/z_n ,     ∫_{−∞}^0 e^{x/2−iax}e^{−idnx}dx = 1/(½ − i(a+dn)) ,
A(z_n) + 1/(½ − i(a+dn)) = 0 ,                    z_n = ½ + i(a+dn),
```

so the Fourier coefficients of `D` are exactly

```
c_n(D) = −(d/2π) · ζ(½ + i(a+dn)) / (½ + i(a+dn)) .
```

Hence: **the progression `½ + i(a+dℤ)` consists entirely of zeros iff `D ≡ 0`.**  And `D` cannot
vanish identically, for every `d > 0` and every `a`: `C` jumps by `−m^{−½−ia}` at `x = log m`, and
in the periodisation the jumps at a point `x₀` come from the class
`{m : log m ≡ x₀ (mod 2π/d)}`, i.e. `{m : m/m₀ = e^{2πk/d}}`.  If `e^{2π/d}` is irrational every
class is a singleton; if `e^{2π/d} = u/v` in lowest terms, then for every prime `p ∉ {u,v}` the
class of `p` is `{p}` alone, because `v^k ∣ p` and `u^k ∣ p` force `k = 0`.  A singleton class
carries the nonzero jump `−p^{−½−ia}`, so `D` is discontinuous, so `D ≢ 0`.

This is a clean, unconditional, phase-uniform theorem — strictly stronger than brick 49 (which
needed a small step) and strictly stronger than Putnam's (which needed `a ∈ dℤ`), but still
**two-sided**.  The one-sided case is genuinely different: the same computation gives only
`c_n(D) = 0` for `n ≥ 1`, i.e. `D̄ ∈ H²` of the circle, and an `H²` function *may* have a boundary
jump (`Im log(1−e^{iφ})` does), so no contradiction follows.  That is precisely the gap
Li–Radziwiłł's moment method fills.

### Next targets on Route 2

1. Formalise the two-sided theorem above (`ζ`'s Laplace representation with `{e^x}`, the
   periodisation, its Fourier coefficients, the singleton-class jump).  Unconditional, complete
   proof, no open core.
2. Then the inhomogeneous one-sided case via the discrete second moment of `ζ` along a vertical
   progression — the corpus already owns the Dirichlet mean-value machinery
   (`Sieve/DirichletMVT.lean`, `Sieve/DirichletMVTWindow.lean`) and the smooth AFE, which is what a
   discrete moment computation needs.

## Landed brick 51: the Laplace representation of zeta through the fractional part (2026-08-19)

`formal/GaloisForLFunctions/RHTower/ZetaFractLaplace.lean`

The foundation of the Putnam route, and the only analytic input it needs:

- `image_Ioi_zero_exp` — `exp '' (0,∞) = (1,∞)`.
- `cpow_ofReal_exp` — `(e^x)^w = exp(w x)` for real `x` and complex `w`.
- `integral_Ioi_zero_fract_exp` — **the Laplace representation**
  ```
  ∫_0^∞ {e^x} e^{-s x} dx  =  1/(s−1) − ζ(s)/s ,      0 < Re s,  s ≠ 1,
  ```
  obtained from the tree's `integral_Ioi_one_fract_cpow_of_re_pos` by the change of variables
  `t = e^x` (`integral_image_eq_integral_abs_deriv_smul`).

With this, the periodisation `D` of

`C(x) = {e^x}e^{−x/2−iax}` on `x ≥ 0`,  `C(x) = e^{x/2−iax}` on `x < 0`

has Fourier coefficients `c_n(D) = −(d/2π)·ζ(½+i(a+dn))/(½+i(a+dn))` exactly, which is the identity
the two-sided theorem of the audit rests on.  What remains for that theorem is the periodisation
itself (uniform convergence, Fourier coefficients, and the singleton-class jump).

## Landed brick 52: Putnam's kernel and its Fourier transform (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamKernel.lean`

- `putnamKernel a x` — `{e^x}e^{−(½+ia)x}` for `x ≥ 0`, `e^{(½−ia)x}` for `x < 0`.
- `putnamTwist a ξ x = putnamKernel a x · e^{−iξx}`, with its two branch formulas.
- `integrableOn_putnamTwist_Iio`, `integrableOn_putnamTwist_Ici`, `integrable_putnamTwist` — the
  kernel is dominated by `e^{−|x|/2}`; the left half-line is an honest exponential
  (`integrableOn_exp_mul_complex_Iic`), the right one is dominated by `e^{−x/2}`
  (`exp_neg_integrableOn_Ioi`).
- `integral_putnamTwist` — **the Fourier transform of the kernel**:
  ```
  ∫_ℝ C_a(x) e^{−iξx} dx  =  − ζ(½+i(a+ξ)) / (½+i(a+ξ)) .
  ```
  The polar term `1/(z−1)` of brick 51 is exactly `−1/(½−i(a+ξ))`, which is what the left half-line
  contributes, so the two cancel and only the zeta value survives.

Axiom-clean.  This is the object on which the whole Putnam route runs: the Fourier transform of one
explicit `L¹` kernel *is* the normalised zeta values along a vertical line.

### Remaining on this route

1. The periodisation `D(x) = ∑_k C_a(x + 2πk/d)` and the Fubini identity
   `c_n(D) = (d/2π)·Ĉ_a(dn) = −(d/2π)ζ(½+i(a+dn))/(½+i(a+dn))`.
2. Fourier uniqueness on the circle: all coefficients zero ⟹ `D = 0` a.e.
3. The one-sided limits of `D` at `x₀ = 0` and the jump
   `−∑_{m ∈ class}m^{−½−ia}`, where `class = {m ≥ 1 : log m ∈ (2π/d)ℤ}`.
4. The class is `{u^j : j ≥ 0}` — the exponent set `K = {k ≥ 0 : e^{2πk/d} ∈ ℕ}` is an additive
   submonoid of `ℕ` with `gcd(K) = k₀ ∈ K` (a rational whose integer power is an integer is an
   integer), hence `K = k₀ℕ` — so the jump is the geometric sum `−1/(1 − u^{−½−ia}) ≠ 0`.

That closes the two-sided theorem for **every** step and **every** phase.  The one-sided case still
needs the discrete second moment (Li–Radziwiłł).

## Landed brick 53: the periodisation and its Fourier coefficients (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamPeriodization.lean`
`formal/GaloisForLFunctions/RHTower/PutnamFourierCoefficients.lean`

- `putnamPeriod d = 2π/d`, `summable_exp_neg_abs_int`, `summable_putnamKernel_translates` — the
  lattice translates of the kernel are summable at every point, because
  `|x + kP| ≥ |k|P − |x|` and the kernel is dominated by `e^{−|·|/2}`.
- `putnamPeriodization a d x = ∑' k, C_a(x + k·2π/d)` and `putnamPeriodization_periodic`.
- `iUnion_Ioc_period`, `pairwise_disjoint_Ioc_period` — the half-open lattice cells tile `ℝ`.
- `putnamTwist_shift` — the lattice phase is trivial: `e^{−i d n k (2π/d)} = 1`.
- `integral_putnamPeriodization_fourier` — **the Fourier coefficients of the periodisation are the
  zeta values**:
  ```
  ∫_0^{2π/d} D_a(x) e^{−idnx} dx  =  − ζ(½+i(a+dn)) / (½+i(a+dn))   for every n ∈ ℤ.
  ```
  Proof: interchange the sum and the integral with
  `hasSum_integral_of_summable_integral_norm` (the cell norms are `≤ P e^{P/2}e^{−|k|P/2}`), shift
  each cell integral with `intervalIntegral.integral_comp_add_right`, and reassemble the line from
  the cells with `integral_iUnion`; the value is then `integral_putnamTwist`.

Axiom-clean.  Item 1 of the two-sided programme is closed: **one periodic function records the whole
vertical progression of zeta values.**

### Remaining for the two-sided theorem

2. Fourier uniqueness: transport `D` to `AddCircle (2π/d)`, show it is `L²`, and use
   `fourierBasis` — all coefficients zero forces `D = 0` a.e.
3. The one-sided limits of `D` at `x₀ = 0` (uniform convergence of the translate series, each
   translate having one-sided limits) and the jump `−∑_{m ∈ class} m^{−½−ia}`.
4. `class = {u^j : j ≥ 0}`, so the jump is the geometric sum `−1/(1 − u^{−½−ia}) ≠ 0`.

## Landed brick 54: the exponent monoid is cyclic (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamExponentMonoid.lean`

This is item 4 of the two-sided programme, and it is pure number theory.

- `exists_nat_of_rat_pow_eq_nat` — a positive rational whose `N`-th power is a natural number is a
  natural number, via `Rat.den_pow`: `(r^N).den = r.den^N = 1` forces `r.den = 1`.
- `expNatSet P = {k : ℕ | e^{kP} ∈ ℕ}`, `zero_mem_expNatSet`, `add_mem_expNatSet`.
- `gcd_mem_expNatSet` — **the gcd of two exponents is an exponent**.  Writing `g = gcd(k,k₀)`,
  `k = gk'`, `k₀ = gk₀'` with `gcd(k',k₀') = 1`, Bézout gives
  `e^{gP} = (e^{kP})^α (e^{k₀P})^β`, a positive *rational*; its `k'`-th power is the integer
  `e^{kP}`, so it is an integer.
- `dvd_of_mem_expNatSet` — hence `expNatSet P = k₀ℕ` for its least positive element `k₀`.

Consequently the jump of the periodised kernel at `x₀ = 0`, namely `∑_{k ∈ expNatSet P} v^k` with
`v = e^{−(½+ia)P}`, is the geometric series `1/(1 − v^{k₀})`, whose modulus is at least
`1/(1 + |v|^{k₀}) > 0`.  **The jump is never zero, for any step and any phase.**

### Remaining for the two-sided theorem

2. Fourier uniqueness — from `∫_0^P D e^{−idnx} = 0` for all `n`, conclude `D = 0` at every point of
   continuity.  Two routes: (i) transport to `AddCircle (2π/d)` and use mathlib's `fourierBasis`
   Hilbert basis; (ii) pair `D` against the Fejér kernel `K_N(· − x₀)`, which is a *finite*
   trigonometric polynomial with frequencies in `dℤ`, so the pairing vanishes identically, and let
   `N → ∞` using that `K_N` is a nonnegative approximate identity.  Route (ii) needs no measure
   theory on the quotient.
3. The one-sided limits of `D`, via `TendstoUniformly.tendsto_of_eventually_tendsto` applied to the
   partial sums of the translate series; the one-sided limits of the kernel are read off from
   `C_a(x) = e^{(½−ia)x} − ⌊e^x⌋e^{−(½+ia)x}` (valid on all of `ℝ`, since `⌊e^x⌋ = 0` for `x < 0`),
   whose only discontinuities are the downward jumps `−m^{−½−ia}` of `⌊e^x⌋` at `x = log m`.

## Landed brick 55: the one-sided limits of the periodised kernel (2026-08-19)

`formal/GaloisForLFunctions/HTGeometry/UniformTsumLimit.lean`
`formal/GaloisForLFunctions/RHTower/PutnamKernelLimits.lean`
`formal/GaloisForLFunctions/RHTower/PutnamPeriodizationLimits.lean`

This is item 3 of the two-sided programme.

- `HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on` — **a normally convergent series may be
  passed to the limit term by term along any filter on which the domination holds**, from
  `tendstoUniformlyOn_tsum` and `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto`.  Reusable.
- `putnamKernel_eq_floor` — `C_a(x) = e^{(½−ia)x} − ⌊e^x⌋e^{−(½+ia)x}` on **all** of `ℝ`, because
  `⌊e^x⌋ = 0` for `x < 0`.
- `tendsto_putnamKernel_right`, `tendsto_putnamKernel_left` — the kernel is right-continuous
  everywhere and has a left limit everywhere, obtained from mathlib's
  `tendsto_floor_right_pure_floor` and `tendsto_floor_left_pure_ceil_sub_one` transported through
  `exp`.
- `putnamKernelLeft a z = C_a(z) + (⌊e^z⌋ − ⌈e^z⌉ + 1)·e^{−(½+ia)z}` — the left limit written as
  value plus jump; the coefficient is the indicator of `e^z ∈ ℤ`.
- `norm_putnamKernelLeft_le` — `‖C_a^-(z)‖ ≤ 2e^{−|z|/2}`; the jump term is harmless on `z < 0`
  because the indicator vanishes there.
- `tendsto_putnamPeriodization_right`, `tendsto_putnamPeriodization_left` — **the periodisation has
  one-sided limits everywhere, and they are the term-by-term sums**.

Axiom-clean.  What is left of the two-sided theorem:

* the jump computation at `y = 0`, i.e.
  `∑'_k C_a^-(kP) − ∑'_k C_a(kP) = ∑_{k ∈ expNatSet P} e^{−(½+ia)kP} = 1/(1 − v^{k₀}) ≠ 0`
  by brick 54;
* item 2, Fourier uniqueness (`D = 0` at every continuity point), for which the Fejér-kernel
  pairing route needs no measure theory on the quotient.

## Landed brick 56: the jump is never zero (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamJump.lean`

- `putnamJumpTerm a d k` — the `k`-th jump contribution
  `(⌊e^{kP}⌋ − ⌈e^{kP}⌉ + 1)·e^{−(½+ia)kP}`, i.e. `[e^{kP} ∈ ℤ]·e^{−(½+ia)kP}`.
- `putnamJumpTerm_eq_zero_of_neg` — negative `k` contribute nothing (`0 < e^{kP} < 1`).
- `putnamJumpTerm_of_mem`, `putnamJumpTerm_eq_zero_of_notMem` — for `k ≥ 0` the term is
  `e^{−(½+ia)kP}` exactly when `k` lies in the exponent monoid, and `0` otherwise
  (`Int.ceil_eq_floor_add_one_iff_notMem`).
- `mul_mem_expNatSet` — the monoid contains every multiple of any of its elements.
- `tsum_putnamJumpTerm_ne_zero` — **the jump is never zero.**  Either the monoid is trivial, and
  the sum is the single term `1`; or it is `k₀ℕ` by brick 54, the support of the family is exactly
  the range of `j ↦ k₀ j`, and reindexing through `Equiv.ofInjective` and
  `tsum_subtype_eq_of_support_subset` turns the sum into the geometric series
  `∑_j w^j = (1 − w)^{-1}` with `‖w‖ = e^{−k₀P/2} < 1`.

Axiom-clean.  Together with brick 55 this says: **the periodised Putnam kernel has, at the origin, a
left limit and a right limit whose difference is `(1 − w)^{-1} ≠ 0`** — for every step `d > 0` and
every phase `a`.

### The single remaining item of the two-sided theorem

Fourier uniqueness: from `∫_0^{2π/d} D e^{−idnx} dx = 0` for all `n` (which is brick 53 plus the
vanishing hypothesis), conclude that `D` vanishes at every point of continuity — then both one-sided
limits at the origin are `0` and the jump is `0`, contradicting brick 56.  The Fejér-kernel pairing
route needs no measure theory on the quotient: `K_N(· − x₀)` is a finite trigonometric polynomial
with frequencies in `dℤ`, so the pairing vanishes identically, and `K_N` is a nonnegative
approximate identity.

## Landed brick 57: the Fejér kernel as a square (2026-08-19)

`formal/GaloisForLFunctions/HTGeometry/FejerKernel.lean`

The last item of the two-sided programme is Fourier uniqueness, and the route chosen avoids all
measure theory on the quotient: pair the periodisation against a **finite** nonnegative
trigonometric polynomial.

- `fejerSum N θ = ∑_{n ≤ N} e^{inθ}` and `fejerKernel N θ = ‖fejerSum N θ‖²/(N+1)`, so
  `fejerKernel_nonneg` is immediate.
- `fejerKernel_eq_double_sum` — `K_N(θ) = (N+1)^{-1}∑_{n,m ≤ N}e^{i(n−m)θ}`, a *finite* double sum
  of characters.  Pairing a periodic function against it therefore produces a finite combination of
  its Fourier coefficients, with no interchange argument at all.
- `normSq_exp_mul_I_sub_one` — `‖e^{iθ} − 1‖² = 2 − 2cos θ`.
- `fejerKernel_le` — **the concentration bound** `K_N(θ) ≤ 2/((N+1)(1 − cos θ))`, from the closed
  form of the finite geometric sum and `‖e^{i(N+1)θ} − 1‖ ≤ 2`.

Reusable.  What remains is to assemble: pair `D` against `K_N(d(· − x₀))`, get `0` for every `N`,
and let `N → ∞` to conclude `D(x₀) = 0` at every continuity point — then both one-sided limits at
the origin vanish and brick 56 is contradicted.

## Landed brick 58: integrability of the periodisation (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamPeriodizationIntegrable.lean`

- `measurable_putnamPeriodization` — via mathlib's `Measurable.tsum`.
- `norm_putnamPeriodization_le` — `‖D_a(x)‖ ≤ e^{|x|/2}·∑_k e^{−(P/2)|k|}`, from the termwise
  kernel bound and `norm_tsum_le_tsum_norm`.
- `integrableOn_putnamPeriodization` — hence `D_a` is bounded on a period, so integrable there.

This is the last prerequisite for the Fejér pairing: the pairing
`∫_0^P D_a(x)·K_N(d(x − x₀))dx` is a finite combination of the Fourier coefficients of `D_a`
(brick 57's double-sum form), hence zero under the vanishing hypothesis; and the concentration
bound then forces `D_a(x₀) = 0` at every continuity point.

## Landed brick 59: the Fejér pairing vanishes (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamPeriodizationIntegrable.lean` (extended)

- `putnamPeriodTwist a d k x = D_a(x)·e^{−idkx}` and `integrableOn_putnamPeriodTwist`.
- `integral_putnamPeriodization_fejer` — **the pairing against the Fejér kernel vanishes**:
  ```
  ∫_0^{2π/d} D_a(x)·K_N(d(x − x₀)) dx = 0     for every x₀ and every N,
  ```
  whenever all the twisted integrals vanish.  The kernel's finite double-sum form (brick 57) turns
  the integrand into a finite combination of the `putnamPeriodTwist` integrals; the interchange is
  `MeasureTheory.integral_finsetSum`, needing only the integrability of brick 58.

Axiom-clean.  What is left is the analytic endgame: `K_N ≥ 0`, `∫K_N = P` (the `n = m` diagonal of
the same double sum), and the concentration bound of brick 57 give
`D_a(x₀) = 0` at every continuity point; the one-sided limits of brick 55 then vanish and the
nonvanishing jump of brick 56 is contradicted.

## Landed brick 60: the Fejér mass over a period (2026-08-19)

`formal/GaloisForLFunctions/RHTower/PutnamFejerMass.lean`

- `integral_lattice_character` — `∫_0^{2π/d} e^{idkx}dx = P·[k = 0]`, from
  `integral_exp_mul_complex` and `e^{2πik} = 1`.
- `integral_fejer_mass` — **`∫_0^{2π/d} K_N(d(x − x₀))dx = 2π/d`** for every `x₀` and every `N`:
  in the finite double-sum form only the `n = m` diagonal survives the character integral, and it
  contributes `(N+1)` terms of size `(N+1)^{-1}P`.

Axiom-clean.  With bricks 57 (nonnegativity and concentration), 58 (integrability), 59 (the pairing
vanishes) and 60 (the mass), the approximate-identity estimate is now a purely `ε`-`N` argument:
```
|D_a(x₀)|·P = |∫ (D_a(x) − D_a(x₀))·K_N(d(x−x₀)) dx|
            ≤ sup_{|x−x₀|<δ}|D_a(x) − D_a(x₀)|·P  +  (sup_{far} K_N)·‖D_a − D_a(x₀)‖_{L¹} ,
```
so `D_a(x₀) = 0` at every continuity point, both one-sided limits of brick 55 vanish, and brick 56's
nonvanishing jump is contradicted.

## CLOSED, 2026-08-19 — by Route 2, not Route 1

The programme's target `(23)` is now unconditional Lean.  Route 1 (superlinear counting) is **not**
what closed it and remains open at the barrier recorded above; Route 2 (progression-freeness) closed
completely, with a mechanism that is neither of the two variants this note had ruled out.

### What was wrong with the earlier reading of Route 2

This note recorded that the reduction "cannot be pushed from one-sided to two-sided: symmetry plus a
finite shift failure gives closure under `±h` only above a positive threshold, so the negative tail
is never reached."  That is correct, and it stays correct.  The error was to conclude from it that a
*one-sided* theorem needs Li--Radziwill's discrete second moment.  It does not.  The Fourier side
never has to be symmetrised at all: one-sided vanishing of the coefficients is exactly the statement
that the periodisation lies in a Hardy class, and a Hardy-class function of bounded modulus cannot
have a jump.  The two-sided Fejér programme (bricks 41--60) proves the weaker statement; the Cauchy
kernel proves the stronger one.

### The closing mechanism

For `0 <= r < 1` pair the periodisation `D_a` against `(1 - r e^{idy})^{-1}` over one period.

* The conjugate kernel `(1 - r e^{-idy})^{-1} = sum_{m >= 0} (r e^{-idy})^m` involves only
  frequencies `-dm` with `m >= 0`, so the conjugate pairing vanishes under the one-sided hypothesis
  alone.  Adding the two pairings and removing the mean converts the Cauchy kernel into the Poisson
  kernel `(1-r^2)/|1-re^{idy}|^2 >= 0` of mass `P`, so the pairing is bounded by `||D_a||_infty P`
  uniformly in `r`.  **This is the only step that uses the hypothesis, and it is one-sided.**
* The imaginary part `Im (1-re^{idy})^{-1}` is nonnegative on `(0,P/2]`, odd under `y |-> P-y`, and
  has mass `d^{-1} log((1+r)/(1-r))`, which is unbounded.  Because it is odd, the pairing folds to
  `integral_0^{P/2}(D_a(y) - D_a(P-y)) Im(...) dy`, whose integrand tends to the jump of `D_a` at
  the origin.  The jump is a geometric series `(1 - e^{-(1/2+ia)k_0 P})^{-1}` and never vanishes.
  Nonnegativity of the kernel on the half period is what removes every `L^1` log-estimate: the near
  part is dominated by the *whole* mass, and the far part is `O_delta(1)`.

Since the mass is unbounded and the pairing is bounded, some coefficient of nonnegative index is
nonzero, i.e. some `zeta(1/2+i(a+dn))`, `n >= 0`, is nonzero.

### Consequences for this note

* Li--Radziwill's discrete second moment is **no longer needed** and should not be re-opened as a
  requirement for `(23)`.
* Selberg's positive-proportion theorem is **no longer needed** for the card either.  Route 1's
  barrier (`term-by-term van der Corput over the AFE is ~T^{1/4} per cell, capping the grid device
  at `N_0(T) >> T^{3/4}`) stands as an independent open problem, and the Graham/Barban--Vehov
  machinery built for it (bricks 41--50) stays in the tree as reusable sieve infrastructure.
* The card `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` has moved to stage 3.

Modules: `HTGeometry/{CosineArc,CauchyCircleIntegral}.lean`,
`RHTower/{PutnamPoissonBound,PutnamJumpBlowUp,XiNoArithmeticProgression}.lean`
(and `RHTower/PutnamApproximateIdentity.lean` for the two-sided companion).

## Route 1 barrier, sharpened (2026-09-24)

The audit of 2026-08-19 recorded that Route 1 needs "a bound for `∑_j|∫_{I_j}ZW|` that is not a
triangle inequality over `n`".  That is right but understates the obstruction: **the natural
replacement, Cauchy–Schwarz over the cells, is exactly critical.**

Per cell, `|∫_{I_j} f|² ≤ H ∫_{I_j} f²`; summing and applying Cauchy–Schwarz over the `T/H` cells,

```text
Bsum²  =  (∑_j |∫_{I_j} f|)²  ≤  (T/H) · H · ∫ f²  =  T · ∫ f² .
```

But the same Cauchy–Schwarz bounds the absolute mass the device needs from below:

```text
L²  ≤  (∫ |f|)²  ≤  T · ∫ f² .
```

So `Bsum` and `L` are bounded by the *same* quantity `√(T ∫ f²)`, and no lower bound for the
surplus `L − Bsum` follows from these two estimates however `H` is chosen.  Closing Route 1
requires strict improvement on one of the two sides: either `|f| = |Z·W|` is flatter than
Cauchy–Schwarz allows, so that `L` saturates `√(T∫f²)` (this is what a good mollifier buys), or
genuine cancellation inside each cell, so that `Bsum` falls strictly below it.  Both are quantitative
statements about the mollified function, i.e. Selberg's machinery; neither follows from moment
bounds alone.

Formalised in `formal/GaloisForLFunctions/HTGeometry/GridDeviceCellEstimate.lean`:

- `sq_sum_abs_le_card_mul_length_mul_total` — the cell estimate
  `(∑_i |c i|)² ≤ #cells · H · ∑_i Q i` from the per-cell bounds `c i ² ≤ H · Q i`.
- `grid_surplus_bounds_coincide` — both `L` and `Bsum` are bounded by `√(W · I₂)`.

**Consequence for the ledger.**  The fixed-length-mollifier simplification of brick 48 removes the
Conrey asymptotic, but it does not remove this collision: brick 48's scheme bounds
`Q ≤ H·∫|ζM|²` and then uses Cauchy–Schwarz over the cells, which is precisely the critical
estimate above.  Route 1 therefore still needs a flatness or cancellation input, not a sharper
moment constant.

## Reclassification of the remaining requirement (2026-09-24)

**Unverified estimate, recorded for checking — not a Lean result.**

Bricks 13–15 recorded the open item as "the coefficient estimate `∑_k|c_k|² ≪ 1` … that is the
Conrey computation and is the remaining mathematics".  Those bricks predate Graham (46–47) and
brick 48.  Running the brick-48 harmonic-weighted bound with a *growing* mollifier appears to give
the coefficient estimate directly, without Conrey:

With the normalised linear mollifier `a_m = μ(m)log(X/m)/log X`, brick 48 gives

```text
λ  =  ∑_{k ≤ N} (b_X(k)/log X)² / k
   ≤  [ 4A²(1+log N)(1+log X) + (1+2log X)(X log X)² ] / log²X
   ≈  4A² · log N / log X      +      2 X² log X / log²X .
```

Take `X = T^θ` and `N ≍ T^{1/2+θ}` (the AFE conductor `√(T/2π)` times the mollifier length).  Then

* the main term is `4A²(1/2+θ)/θ`, **a constant**, not a growing quantity;
* the error term needs `X² ≪ N`, i.e. `2θ < 1/2 + θ`, i.e. `θ < 1/2` — exactly the condition the
  programme already carries.

So `λ = O(1)` for every `θ < 1/2`, from Graham alone.  If this is right, the remaining requirement
is **not** the Conrey asymptotic.

What it becomes, via the collision above: the device needs `Bsum < L ≈ T`, while Cauchy–Schwarz
over cells allows only `Bsum ≤ √(T ∫f²) ≈ T√λ`.  So the missing input is a **constant-factor**
saving `√λ` over Cauchy–Schwarz in the cell cancellation, rather than a `√(log T)` saving (which is
what a fixed-length mollifier would require, since there `λ ≍ log T/log X`).

Caveat, and it is a serious one: `A = 6 + |γ|`, so `λ ≈ 8A² ≈ 346` as `θ → 1/2`, giving
`√λ ≈ 19`.  A nineteen-fold gain over Cauchy–Schwarz is a large constant, and the programme's own
margin bookkeeping (Levinson's `0.009`) suggests constants of this size are usually fatal.  The
reclassification is therefore from "needs a hard asymptotic" to "needs a large but fixed constant
factor", which is a different kind of problem, not obviously an easier one.

**To check before relying on this:** the relation `N ≍ T^{1/2+θ}` against the smooth AFE actually
used (bricks 4–5, 14), and whether the first moment really gives `L ≈ T` with a constant that does
not itself carry a `1/√λ`.

## Verification of the reclassification, and brick 61 (2026-09-24)

Check 1 of the previous section — the relation `N ≍ T^{1/2+θ}` against the smooth AFE — **passes**,
but only with two corrections to the chain as recorded.

**Correction A: use the affine mean value theorem, not brick 13.**  Brick 13's window form carries
the error `8N(1+log N)·∑_m|a_m|²`.  With `N ≍ T^{1/2+θ}` and `∑|a_m|² ≍ λ` that is `≍ T^{1/2+θ}log T`,
and the `log T` is avoidable.  The tree already owns the *affine* form
(`Sieve/DirichletPolyAffineMeanSquare.lean`, `integral_Icc_normSq_dirPoly_le_affine`), whose error is
`5πe·∑_m (m+1)|a_m|²`.  For the mollified coefficients `c_k = k^{-1/2} b_X(k)/log X` this is
`≍ ∑_{k ≤ N} b_X(k)²/log²X`, which Graham bounds by `4A²N(1+log X)/log²X ≍ N/log X`.  So

```text
affine error  ≍  T^(1/2+θ) / log X  ≪  T   ⟺   θ < 1/2 ,
```

i.e. the programme's own threshold `θ < 1/2` is exactly the condition for the affine error to be
admissible.  This is a consistency check the chain passes.

**Correction B: the truncation exponent.**  Brick 14 instantiates
`exists_norm_smoothAFECutoff_le_neg_rpow` at `A = 1`, giving a tail `≍ K x N^{-1/2}`.  With
`x ≍ √T` and `N ≍ T^{1/2+θ}` the tail is negligible only when

```text
A  >  1/(4θ) + 1/2 ,
```

so `A = 1` suffices only as `θ → 1/2` and fails for smaller `θ`.  Since the Gaussian cutoff decays
at every exponent, this is a free parameter that brick 14 simply fixed too early.

### Landed brick 61: the truncation at an arbitrary exponent (2026-09-24)

`formal/GaloisForLFunctions/RHTower/SmoothAFEDirectTruncationRpow.lean`

- `exists_norm_smoothAFEDirectSeries_sub_dirPoly_le_rpow` — for every `A > 1/2`,
  ```
  ‖smoothAFEDirectSeries x τ − dirPoly N (afeDirectCoeff x N) (−τ)‖
      ≤ (K_A · x^A) · ∑'_i 1/((i+N)+1)^(A+1/2) ,
  ```
  uniformly in the height, by instantiating the cutoff decay at exponent `A` instead of `1`.

Axiom-clean.  This closes correction B.  Correction A needs no new mathematics, only the use of the
affine mean square in place of brick 13 where the chain is assembled.

**Check 2 remains open**: whether the first-moment lower bound `L ≈ T` carries a constant that
itself absorbs the `√λ ≈ 19`.  Until that is settled the reclassification should not be relied on.

## Check 2 settled — and a correction to the previous section (2026-09-24)

The reclassification section above concluded that the missing input is a constant-factor gain
`√λ ≈ 19` over Cauchy–Schwarz, and warned that such a constant is probably fatal.  **That
conclusion was wrong**, and the error was to compare a scale against a shape.

On a window of length `T` write `I₁ = ∫|f|`, `I₂ = ∫f²`.  Cauchy–Schwarz bounds **both** sides of
the surplus by `√(T I₂)`, so the device needs the cell cancellation to beat that bound by the
factor `√(T I₂)/I₁`.  That factor is invariant under `f ↦ c f`
(`HTGeometry/GridDeviceGainScaleInvariance.lean`, `grid_required_gain_scale_invariant`).

The mollifier's mean-square constant `λ` is exactly such a common amplitude: it multiplies `I₂` by
`λ` and `I₁` by `√λ`, and cancels.  The earlier section compared `L ≈ T` (the value at `λ = 1`)
against `√(T I₂) ≈ T√λ` and read the discrepancy as a required gain.  It is not: the first moment
scales with `√λ` too.

**So the required gain carries no `λ` at all.**  It is a normalised `L¹/L²` shape ratio of the
mollified function on the window — a pure distributional quantity, bounded by `1`, and equal to `1`
only for a function of constant modulus.  Whether it is bounded away from the cancellation the
cells actually exhibit is a statement about the *distribution* of `|Z M|`, not about any constant
in Graham's bound.

Consequence for the ledger: sharpening constants in the coefficient estimate cannot help, and
neither can enlarging `λ`; both cancel.  The open input is the shape of `|ZM|` against the cell
cancellation, and nothing else in the chain bears on it.

## The collision is not about Cauchy–Schwarz: no modulus-only bound can close the device (2026-09-24)

The two preceding sections treated the obstruction as a property of Cauchy–Schwarz, then of the
shape ratio.  Both understate it.  The obstruction is structural and holds for **every** estimate
that factors through `|f|`.

Write `m j` for the absolute mass of `f` on cell `j`.  The signed cell integrals satisfy
`|∫_{I_j} f| ≤ m j`, and an estimate depending only on `|f|` is one valid for every sign pattern
compatible with those masses.  The pattern with no sign changes is realised by `|f|` itself and
attains `∑_j m j = ∫|f|`.  Hence **any modulus-only bound `Φ` satisfies `Φ ≥ ∫|f|`**, and the
surplus `∫|f| − Φ` it yields is never positive.

Formalised in `formal/GaloisForLFunctions/HTGeometry/GridDeviceModulusOnlyNoGo.lean`:

- `no_modulus_only_cell_bound` — `∑_i m i ≤ Φ` for every `Φ` valid across sign patterns.
- `grid_surplus_nonpos_of_modulus_only` — hence the surplus is `≤ 0`.

This subsumes at one stroke: Cauchy–Schwarz over the cells, Hölder at every exponent, the affine
mean value theorem, and every moment estimate on `ζM`, including any sharpening of Graham's
constants.  All of them factor through `|f|`.

**Consequence for the ledger.**  The open input of Route 1 is not any moment bound.  It is an
estimate that uses *where* `Z·W` changes sign — i.e. information about the zeros themselves — which
is why the route reads as circular at this point.  Any continuation must break that circularity
explicitly, and no amount of work on the coefficient side can do it.
