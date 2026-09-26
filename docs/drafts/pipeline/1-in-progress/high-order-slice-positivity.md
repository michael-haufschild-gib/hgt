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

## Lean plan
Reuse `NonnegTaylorAtZero`, `xiSliceCoeff`, `hasSum_xiSliceCoeff`. Cauchy coefficient formula: mathlib
`cauchyPowerSeries` / `iteratedDeriv` via the circle integral. Needed new infrastructure: sector Stirling
with explicit constants (the corpus has only vertical-strip Gamma bounds: `GammaVerticalSharpBound`,
the digamma two-sided bound). This is the bulk of the work.

## Log
- 2026-09-26 — created from C26; outline and checklist written; no step fully proved yet.
