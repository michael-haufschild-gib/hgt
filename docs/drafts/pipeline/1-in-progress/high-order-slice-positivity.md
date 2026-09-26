# High-order slice positivity at every height

- **ID:** high-order-slice-positivity
- **Stage:** 1-in-progress
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
