# High-order slice positivity at every height

- **ID:** high-order-slice-positivity
- **Stage:** 3-formalized
- **Type:** CONJECTURE → THEOREM (paper, in progress)
- **Source:** `new-route-conjecture-loop.md` C26; route 3 slice core (`XiHorizontalSliceTaylorPositivity`,
  `…Converse`, `XiHorizontalSliceConeCriterion`)
- **Statement.** There are absolute constants `t₀`, `κ` such that for every real `t` with `|t| ≥ t₀` and
  every `k ≥ κ log|t|`, the coefficient `c_k(t)` of `x^{2k}` in
  `g_t(x) = ξ(½+x+it)·ξ(½−x+it)` is strictly positive.

## Why it matters for route 3
- Lean: RH ⟺ `c_k(t) ≥ 0` for all `t, k` (`riemannHypothesis_iff_xiSliceCoeff_nonneg`).
- With the theorem, RH ⟺ `c_k(t) ≥ 0` for `k < κ log|t|` (together with an explicit statement for
  `|t| < t₀`). The RH content at height `t` sits in `O(log t)` explicit differential expressions of `Ξ`
  at `t`.
- The door-2 integer `V(t) = #sign changes of (c_k(t))_{k<κ log t}` is finite, even, at least twice the
  number of off-line pairs at ordinate `t`, and `≡ 0` iff RH. It carries route 3's full-quantum margin
  and is defined pointwise.
- Consistency: the detection-index law (C10) predicts off-line pairs of displacement `b` are first seen at
  order `≍ b log t ≤ ½ log t`.

## Novelty check (first pass)
The literature covers the `t = 0` Maclaurin axis (Laguerre inequalities of order `r` for `γ(n)` once
`n > c r³`; Csordas–Varga; Griffin–Ono–Rolen–Zagier). No height-local large-order statement was found.
A full audit is pending.

## Paper proof (outline with the estimates to be made explicit)

**Setup.** By the FE, `ξ(½−z+it) = ξ(½+z−it)`, so `g_t(z) = ξ(½+z+it)·ξ(½+z−it)`. `g_t` is even, entire,
positive on `ℝ`, and its zeros satisfy `|Re z| < ½`. For any `R > 0`,
`c_k = (R^{−2k}/2π)∫_{−π}^{π} g_t(Re^{iθ}) e^{−2ikθ} dθ = (R^{−2k}/π)∫_{−π/2}^{π/2} g_t(Re^{iθ}) e^{−2ikθ} dθ`,
because the saddles at `θ = 0` and `θ = π` contribute equally (`g_t` is even).

**Step 1 (saddle radius).** On `R ≥ 3/2`, `h(R) := log g_t(R) = 2 Re log ξ(½+R+it)` is smooth and
`R h'(R) → ∞`. For `k ≥ κ log t`, pick `R_k ≥ 4` with `R_k h'(R_k) = 2k` (intermediate value
theorem). Then `R_k ≍ 2k/log(t+R_k)`.

**Step 2 (local quadratic control).** On `|θ| ≤ η := k^{−2/5}` the circle stays in `Re z ≥ R cos η ≥ 1`,
where `g_t ≠ 0` and `Φ(θ) := log g_t(Re^{iθ}) − log g_t(R)` is analytic, with
- `Φ'(0) = 2ik` (choice of `R`);
- `Φ''(0) = −(2k + R²h''(R))`, where `|h''(R)| ≤ C/R` from
  `(log ξ)'' = −s^{−2} − (s−1)^{−2} + ¼ψ'(s/2) + (ζ'/ζ)'(s)`, `|ψ'(w)| ≤ 1/|w| + 1/|w|²` and
  `|(ζ'/ζ)'(s)| ≤ Σ Λ(n) log n · n^{−σ} ≤ C 2^{−σ}` for `σ ≥ 2`; so `Re Φ''(0) ≤ −k` once `κ` is large;
- `|Φ'''| ≤ C k` on `|θ| ≤ η`.

The local integral is then `√(2π/(2k + R²h''))·(1 + O(k^{−1/5}))`, positive.

**Step 3 (angular decay).** For `η ≤ |θ| ≤ π/2`, with `a = R cos θ`, `c = R sin θ`,
`|g_t(Re^{iθ})| = |ξ(½+|a|+i(t+c))|·|ξ(½+|a|+i(t−c))|` (FE reflection for `a < 0`). Stirling in a
sector (uniform in both variables) gives, for the Gamma parts,
`log|Γ-part(θ)| − log|Γ-part(0)| ≤ −(R − |a|)·½ log((t+R)/2) + C`. The exponential factors
`e^{−π|y|/4}` sum to `−(π/2) max(t, |c|) ≤ −(π/2)t`, never worse than at `θ = 0`.
- ζ-factors: for `|a| ≥ 1`, `|ζ| ≤ ζ(3/2)`, and at `θ = 0` `|ζ(½+R±it)| ≥ 2 − ζ(2)`.
- For `|a| < 1`, `|ζ(σ+iy)| ≤ C(|y|+2)` (a crude polynomial strip bound suffices).
- With `1 − |cos θ| ≥ 2θ²/π²` this gives `|g_t(Re^{iθ})| ≤ g_t(R)·C′(t+R)^{2}·exp(−(2/π²)R θ² log((t+R)/2))`
  in the strip part, and without the `(t+R)²` factor elsewhere. For `R ≥ 4` and `k` large this is
  `≤ g_t(R)·exp(−c k θ²)`, so the tail integral is `O(g_t(R) e^{−c k^{1/5}})`, below the local main term
  `≍ g_t(R) k^{−1/2}`.

**Step 4.** Combining Steps 2–3, `c_k > 0` for `k ≥ κ log t`, `t ≥ t₀`.

## Estimates to make explicit (proof checklist)
1. Uniform complex Stirling with explicit error in `|arg w| ≤ π/2`, both for `log|Γ|` and for `ψ'`.
2. `|(ζ'/ζ)'(σ+iy)| ≤ C 2^{−σ}` for `σ ≥ 2` (Dirichlet series; elementary).
3. Crude strip bound `|ζ(σ+iy)| ≤ C(|y|+2)` for `0 ≤ σ ≤ 2` (the corpus has `ZetaStripPolynomialBound`).
4. The saddle integral with an explicit cubic remainder.
5. Existence of `R_k ≥ 4` solving `R h'(R) = 2k` for `k ≥ κ log t` (continuity plus asymptotics of `h'`).

## Proved bricks
- **[L] Imaginary-direction Gamma bounds, explicit and uniform** (`HTGeometry/GammaImaginaryShiftBounds.lean`,
  axiom-clean). The theorem `log_norm_Gamma_sub_log_Gamma_bounds` states: for `x > 0` and real `y`,
  `−½(log(1+y²/x²) + I) ≤ log|Γ(x+iy)| − log Γ(x) ≤ −½ I`, where
  `I = π|y| − x log(1+y²/x²) − 2|y| arctan(x/|y|)`.
  - It comes from Euler's limit (`GammaSeq_tendsto_Gamma`): exactly,
    `log|Γ(x+iy)| − log Γ(x) = −½Σ_j log(1+y²/(x+j)²)` (`hasSum_gammaShiftWeight`).
  - The sum is then sandwiched between integrals (`AntitoneOn.integral_le_sum`/`sum_le_integral`), using
    the closed-form primitive `v log(1+y²/v²) + 2|y| arctan(v/|y|)`.
  - This replaces checklist item 1 in the imaginary direction. What remains of item 1 is the
    real-direction comparison `log Γ(x) − log Γ(x')`, which follows from the corpus's two-sided digamma
    bound `log u − 1/u ≤ ψ(u) ≤ log u` by integration.

## Lean plan
Reuse `NonnegTaylorAtZero`, `xiSliceCoeff`, `hasSum_xiSliceCoeff`. Cauchy coefficient formula: mathlib
`cauchyPowerSeries` / `iteratedDeriv` via the circle integral. Needed new infrastructure: sector Stirling
with explicit constants (the corpus has only vertical-strip Gamma bounds: `GammaVerticalSharpBound`,
the digamma two-sided bound). This is the bulk of the work.

## Log
- 2026-09-26 — created from C26; outline and checklist written.
- 2026-09-26 — brick 1 [L]: explicit two-sided imaginary-direction Gamma bounds (`GammaImaginaryShiftBounds`).
- 2026-09-26 — brick (a) [L]: complex Stirling difference `abs_log_norm_Gamma_sub_stirlingMain_le` (`HTGeometry/GammaStirlingDifference.lean`): along a segment in `Re > 0` at distance `≥ m ≥ 2` from `0`, `log|Γ(z₁)| − log|Γ(z₀)| = Re(stirlingMain z₁ − stirlingMain z₀) ± 3‖z₁−z₀‖/m`. Next: (b) ζ-ratio bounds, (c) angular decay.

## Step 3 refined: Gamma comparison by integrating the corpus's complex digamma bound
The corpus has `HTGeometry.norm_digamma_sub_log_le_of_re_pos`: `‖ψ(z) − log z‖ ≤ 3/‖z‖` for
`Re z > 0`, `‖z‖ ≥ 2`. Only *ratios* of `|Γ(s/2)|` between the saddle point and a point on the circle are
needed. So integrate `d log|Γ(z)| = Re(ψ(z) dz)` along the segment `z₀ = (½+R+it)/2 → z₁`. Then
`log|Γ(z₁)| − log|Γ(z₀)| = Re[w log w − w]_{z₀}^{z₁} + E`, with `|E| ≤ 3|z₁−z₀|/min|w| ≤ 12R/t` for
`R ≤ t/4`.
- With `w = X + iY` and `Y arg w = πY/2 − Y arctan(X/Y)`, the `πY/2` terms of the two factors
  (`Y = (t ± c)/2`) sum to the same value as at `θ = 0`.
- The remainder is `Σ_± (X₁ log|w₁| − X₀ log|w₀|) + O(R³/t²)`.
- Together with the `π^{−s/2}` factor this gives
  `Γ-part(θ) − Γ-part(0) ≤ −R(1 − |cos θ|) log(t/2π) + C(R³/t² + R/t)` for `R ≤ t/4`.
- For `R > t/4` (orders `k ≳ t log t`), the exponential parts still satisfy
  `|y₁| + |y₂| = 2 max(t, |c|) ≥ 2t`, and the real-direction loss `|w|^{(R−|a|)/2}` dominates. Points
  with small `|w|` (`R ≈ t`, `θ ≈ π/2`) are bounded directly by `|Γ(¼ + iy/2)| ≤ Γ(¼)`.

Lean bricks in order:
- (a) arc/segment integration of the digamma bound, i.e. the complex Stirling *difference* lemma;
- (b) the ζ-ratio bounds;
- (c) the angular-decay inequality;
- (d) the saddle integral;
- (e) assembly with `xiSliceCoeff` through the Cauchy coefficient formula.
- 2026-09-26 — brick W1 [L]: `HTGeometry/GammaSymmetricSplitDecay.lean`. Exact law for the Stirling main term `φ(X,Y)=Re(w log w − w)`: `φ(X,·)` is concave (`∂_Yφ = −arg w`) and `∂_Xφ = log|w|`. So `φ(X₁,Y+d)+φ(X₁,Y−d)−2φ(X₀,Y) ≤ −2(X₀−X₁)log|X₁+iY|`, with no error term and any `d`. Gamma form (`log_norm_Gamma_split_le`): `≤ −2(X₀−X₁)log Y + 12(X₀−X₁+|d|)/Y` for `Y ≥ 4`, `|d| ≤ Y/2`. This replaces the four-point estimate.
- 2026-09-26 — brick W2 [L]: `RHTower/XiSliceCircleDecay.lean`.
  - `norm_xiSliceProduct_circle_le`: for `t ≥ 8`, `R ≤ t/2`, `cos θ ≥ 0`, `|g_t(Re^{iθ})| ≤ g_t(R)(B/m₀)² exp(−R(1−cos θ)log(t/2π) + 12R(1−cos θ+|sin θ|)/t + 4(½+R cos θ)/t)`.
  - `…_explicit`: ζ-ratio factor `16` when `R cos θ ≥ 3/2`, and `(4+12t)²` otherwise.
- 2026-09-26 — brick W5-generic [L]: `HTGeometry/SaddleArcControl.lean`, `saddleArc_bounds`. Hypotheses: `f` zero-free and holomorphic on `U ⊇ D̄(R,r)`, `F = wf'/f` real on ℝ, `|F−F(R)| ≤ M` on the disc. Then for `0 ≤ θ ≤ r/(2R)`, with `F₁ = F'(R)` and `K = 32M/r²`:
  - `|G(θ)| ≤ exp(−F₁R(1−cos θ) + KR²θ³/3)`;
  - `Re G(θ) ≥ exp(−F₁R(1−cos θ) − KR²θ³/3)·cos(|F₁|Rθ³/6 + KR²θ³/3)`.
  The proof is the ODE `G' = G·i(F−λ)` plus two Cauchy estimates.

### Remaining Lean plan (window theorem `κ log t ≤ k ≤ ε t log t`)
- W3: the M-bound for `f = g_t` on `D̄(R, R/2)`. Uses `logDeriv_xi_fourFactor`, the digamma bound `|ψ−log| ≤ 3/|w|`, `norm_logDeriv_zeta_le_of_two_le_re` (≤ `vonMangoldtSquareMass`), and `g_t(z) = ξ(½+z+it)ξ(½+z−it)`, which gives `F(w) = w(ℓ(½+w+it)+ℓ(½+w−it))`.
- W3': a lower bound on `F₁ = F'(R) = L(R)+RL'(R)` of size `≥ log(t/2π) − C`, for the Gaussian decay inside `|θ| ≤ η`.
- W6: IVT for the saddle `F(R) = 2k`.
- W7: Cauchy coefficient formula `c_{2k}R^{2k} = (1/π)∫_{−π/2}^{π/2} g_t(Re^{iθ})e^{−2ikθ}dθ` (from `iteratedDeriv_eq_circleIntegral`, evenness, and conjugation symmetry).
- W8: assembly. Core `|θ| ≤ 1/√M`, from `Re G`. Intermediate zone `1/√M ≤ θ ≤ η`, from `|G|`. Tail `η ≤ θ ≤ π/2`, from W2 with `1−cos θ ≥ 2θ²/π²`.
- W9 (large k, `R > t/2`): Stirling with small-`|w|` handling near `θ ≈ π/2`. Deferred.
- 2026-09-26 — **W3–W8 done [L]. Window theorem proved, unconditional and axiom-clean.**
  - `RHTower.exists_xiSliceCoeff_pos_window` (`RHTower/XiSliceHighOrderCoeffPositivity.lean`): `∃ t₀ κ, ∀ t ≥ t₀, ∀ k, κ log t ≤ k ≤ (t log t)/8 → 0 < c_{2k}(t)` (ComplexOrder, so the coefficient is also real).
  - Modules:
    - `XiSliceSaddleArcBounds`: `|ξ'/ξ(s) − ½log(s/2)| ≤ 3 + ΣΛ(n)/n²`; the disc bounds for `L = ξ'/ξ(½+·+it)+ξ'/ξ(½+·−it)`; `F = wL` real on ℝ; `F'(R)` within `2(log4+π+4C)` of `L(R)`.
    - `XiSliceCoeffQuarterArc`: exact formula `c_{2k}(t) = (2|ξ(½+R+it)|²/(πR^{2k}))∫₀^{π/2} Re S`, using period π and conjugate symmetry of `S`; IVT for the saddle radius.
    - `XiSliceHighOrderCoeffPositivity`: pointwise bounds for the core (`Re S ≥ 7/40` for `θ ≤ Λ^{−1/2}`), the mid-core (`Re S ≥ 0` up to `Λ^{−2/5}`), the middle (`|S| ≤ e^{−Λθ²/8}` up to 1/1000) and the tail (circle decay); assembly; scale choice via `Tendsto`.
  - Novelty (web, 2026-09-26): no height-local large-order positivity result found. Nearest items: complex Laguerre half-plane for the first functional (alphaXiv 2609, k = 1 only); Laguerre/Turán results on the Maclaurin axis t = 0; GORZ Jensen hyperbolicity for large shift.
- NEXT (W9): the range `k > t log t/8` (saddle `R ≥ t/5`), needed so that RH ⟺ positivity of the first `κ log t` coefficients.
  - Scale `T = t+R`, `Λ = R log T`.
  - Disc bounds with annulus `T/4 ≤ |s| ≤ 2T`.
  - Arc `θ ≤ π/3`: Stirling split with segment distance `≥ X₁ ≥ R/4` (no `|c| ≤ t/2` needed), `ζ ≤ 2`, polynomial ratio `≤ e^{4θ}`.
  - Arc `θ ∈ [π/3, π/2]`: crude bounds (compact-box bound for ξ, `|Γ(x+iy)| ≤ Γ(x)`, imaginary-shift lower bound at `s₀`, real Stirling gain `≈ (R/4) log R`).
- 2026-09-26 — **W9 done [L]. C26 fully formalized, axiom-clean.**
  - `RHTower/XiSliceLargeRadiusArcBounds.lean`: large-radius disc bounds (scale `log R`); near-arc decay via the Stirling split in `Re ≥ R/4`; far-arc decay `exp(−(R/8)log R)`, from the compact box bound for ξ, `|Γ(x+iy)| ≤ Γ(x)`, the saddle lower bound and the growth of `Γ` on the real axis.
  - `RHTower/XiSliceFiniteOrderReduction.lean`:
    - `quarter_integral_pos_of_arc_bounds`: abstract assembly;
    - `exists_xiSliceCoeff_pos_large_order`: `∃ K₀, ∀ t ≥ 0, ∀ k ≥ max(K₀, t log t/8) → c_{2k}(t) > 0`;
    - `exists_xiSliceCoeff_pos_high_order`: `∃ K κ, ∀ t ≥ 0, ∀ k ≥ max(K, κ log t) → c_{2k}(t) > 0`;
    - `xiSliceCoeff_odd_eq_zero`;
    - `riemannHypothesis_of_xiSliceCoeff_nonneg_of_nonneg_height`;
    - **`exists_riemannHypothesis_iff_low_order_xiSliceCoeff_nonneg`**: `∃ K κ, RH ⟺ ∀ t ≥ 0, ∀ k < max(K, κ log t), c_{2k}(t) ≥ 0`.
  - Stage: Formalized. The card moves to `3-formalized`.

## What the theorem says and what remains
- Unconditional content: at height `t`, every Laguerre-slice coefficient of order `≥ 2κ log t` is positive. The RH content of route 3 therefore sits in the first `O(log t)` coefficients, which are explicit differential expressions of Ξ at `t` of order `O(log t)`. This matches the detection-index law, under which an off-line pair of displacement `b` is first seen at order `≍ b log t`.
- Open core (route 3, unchanged in difficulty): nonnegativity of `c_{2k}(t)` for `k < κ log t`. Nothing here decides it. The four-wall diagnosis of `new-route-conjecture-loop.md` applies verbatim to this finite window.

## 2026-09-27 — sharp window [L], axiom-clean
- **`exists_riemannHypothesis_iff_xiSliceCoeff_nonneg_below_quarter_log`**: for every `ε > 0`, `∃ K, RH ⟺ ∀ t ≥ 0, ∀ k < max(K, (¼+ε) log t), c_{2k}(t) ≥ 0`. This replaces `κ ≥ 6` by `¼ + ε`, which is the CANNOT-470 edge. Every order below `¼ log t` detects some admissible displacement `b = 2k/log t < ½` (N40/N41). So the window is sharp up to `ε`.
- `exists_xiSliceCoeff_pos_above_quarter_log`: `∃ K, ∀ t ≥ 0, ∀ k ≥ max(K, (¼+ε) log t), c_{2k}(t) > 0`.
- Modules:
  - `ZetaConvexityBound`: `‖ζ(σ+it)‖ ≤ C t^{(1+η−σ)/2}` on `[−η, 1+η]`, by bounded Phragmén–Lindelöf on `ζ_entire·e^{(s−it₀)²}·t₀^{−(3+η−s)/2}`.
  - `XiSliceSaddleArcBoundsEulerRegion`: disc, slope and saddle-arc bounds on a disc of radius `η` for saddle radius `R ≥ ½+2η`. Both slice points stay in `Re ≥ 1+η`, where `‖ζ'/ζ‖ ≤ (σ−1)⁻¹ + C`.
  - `XiSliceArcTailConvexity`: `|S(θ)| ≤ A(t^{−η} + t^{−θ₁²/10})` for `θ ≥ θ₁` and `R ∈ [½+2η, R₁]`. Arc points in the strip lose `t^{½+η−R cos θ}` to convexity and gain `t^{−(R−R cos θ)}` from Γ, leaving `t^{½+η−R} ≤ t^{−η}`.
  - `XiSliceCoeffPositivitySharpWindow`: scaled quarter-arc assembly (disc constant `≤ Kℓ`, `K = R₁/(2η)`; saddle bounds on `θ ≤ 1/(1000K)`; phase condition `(1+128K)Λδ³ ≤ 3/2`), saddle existence on `[½+2η, R₁]`, sharp window, and the reduction.
- The open core is unchanged: `c_{2k}(t) ≥ 0` for `k < (¼+ε) log t`. The near-double-zero part is `k = O(1)`, i.e. the bounded-order Laguerre inequalities `L_k(Ξ)(t) ≥ 0`, since `b ≍ 1/log t` is detected at `k ≍ Lb = O(1)`.
