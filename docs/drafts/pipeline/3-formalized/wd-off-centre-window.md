# Off-centre positivity window: orders ≥ (½ − x₀ + ε) log t are positive at centre x₀

- **ID:** wd-off-centre-window
- **Stage:** 3-formalized
- **Type:** CONJECTURE → THEOREM (paper)
- **Source:** `wd-goal-loop-2026-10-09.md` row 6a (open item), rows 284–287 (window–abscissa duality, heat–tilt)
- **Statement:** For every ε > 0 there is t₁ such that for t ≥ t₁, x₀ ∈ [ε, ½] and every order n ≥ (½ − x₀ + ε) log t, the Taylor coefficient of the slice at x₀, `iteratedDeriv n (xiSliceProduct t) x₀`, is positive.

## Goal
Shrinking finite-order window for every quasi-RH (Θ ≤ ½ + x₀ ⟺ nonnegativity of orders < (½ − x₀ + ε) log t at centre x₀), the off-centre half of the window–abscissa duality (row 284), and (via the heat–tilt identity) the route to the sharp effective-KKL constant ½.

## Paper proof
Shifted slice f(w) = S(t, x₀ + w). Cauchy on |w| = R; by conjugation symmetry a_n(x₀) = (f(R)/(πRⁿ)) ∫₀^π Re G(θ) dθ with G the normalised arc value at exponent n. Saddle radius R with R·L(x₀+R) = n, x₀ + R ∈ [½ + 2η, R₁] (orders n ∈ [(½ − x₀ + 2η)ℓ, (½+ε)ℓ]; higher orders by the Taylor shift from centre 0, row 6a). Near the saddle: generic `saddleArc_bounds` with the Euler-region disc constant at x₀ + R (`xiSliceLogDeriv_disc_bounds_euler`). Tail θ ∈ [θ₁, π]: arc point a + ic with a = x₀ + R cos θ; by evenness use |a|; `norm_xi_split_le` against the saddle point x₀ + R, with ζ bounds from the Euler region or from convexity; the decay (t/2π)^{−(x₀+R−|a|)} beats the convexity loss t^{½+η−|a|}, leaving t^{½+η−x₀−R} ≤ t^{−η}; on the far half x₀ + R − |a| ≥ min(R(1−cos θ), 2x₀).

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 (Lean: `exists_iteratedDeriv_xiSliceProduct_pos_offCentre`, `exists_strip_iff_offCentre_low_order`)

## Log
- 2026-10-11 — created; module 1 (shifted Cauchy formula, saddle data) started.
- 2026-10-11 — closed in Lean (ledger row 288). Modules: `RHTower/XiSliceOffCentreSaddleArc`, `RHTower/XiSliceOffCentreArcTail`, `RHTower/XiSliceOffCentreCoeffWindow`, `RHTower/XiSliceOffCentreConeCriterion`. The theorem as proved: for 0 < ε ≤ 1/8, t ≥ t₀(ε), ε ≤ x₀ ≤ ½ and (½ − x₀ + ε) log t ≤ n ≤ log t, g_t^{(n)}(x₀) > 0; orders above log t are covered by the corpus Taylor shift. For x₀ < ε the corpus window (½ + 2ε) log t is within 3ε of the statement. Side result: the per-zero cone-or-strip criterion and the unconditional height-local abscissa ½ − 1/(58 log(|t|+4)).
