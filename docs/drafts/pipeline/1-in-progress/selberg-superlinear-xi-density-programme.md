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
