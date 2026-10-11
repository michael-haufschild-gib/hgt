# HCF heat Hankel positivity window at small heat time

- **ID:** hcf-small-time-window
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** hcf-exact-layer-loop-2026-10-09.md, row 50 (positive survivor of the failed diagonal-continuity conjecture C50)
- **Statement:** For every degree `d` there is `a_d > 0` such that, for every heat time `0 < a < a_d`, the heat Hankel form `H_a(P) = Σ_q e^{−a w_q} P(w_q) \overline{P(\overline{w_q})}` is positive definite on nonzero polynomials of degree `≤ d`. Unconditionally.

## Goal
- This is the Yoshida-type window of route HCF. RH is equivalent to a single `a` working for every `d` (cycle 46, `riemannHypothesis_iff_heatMomentDet_pos`).
- Unconditionally, positivity holds in the window `a < a_d`, with `a_d → 0`.
- Under ¬RH, the degree needed to detect a fixed off-line pair diverges as `a → 0` (row 50). The window therefore never reaches it, so this is not a producer.
- Discipline: this is the positive survivor of C50 and must be formalized before the no-go is closed.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional, attack idea
- [x] 1 → 2  fully-proven: paper proof below, no open dependency (corpus: Riemann–von Mangoldt `exists_xiZeroCount_close`, count bound `card_xiCopiesBelow_le_log`, `xiSpectralPoint_im_sq_lt_quarter`)
- [x] 2 → 3  formalized (`RHTower/XiGaussianHeatHankelSmallTimeWindow.lean`, axioms: propext, Classical.choice, Quot.sound)

## Proof (paper, dependency-closed)
Notation: `z_q = γ − iδ` with `|δ| < ½`, and `w_q = z_q²`. `σ_q := a·Re w_q = a(γ² − δ²)` and `ε_q := a·Im w_q`, so `|ε_q| ≤ a|γ|`. `‖Q‖₁` is the sum of the absolute values of the coefficients.

1. **Scaling.** Put `Q(s) := P(s/a)`, again of degree `≤ d`. Then `H_a(P) = Σ_q e^{−s_q} Q(s_q) \overline{Q(\bar s_q)}` with `s_q = a w_q = σ_q + iε_q`.
2. **Pointwise comparison.** For `s = σ + iε`:
   `Re(e^{−s}Q(s)\overline{Q(\bar s)}) ≥ e^{−σ}|Q(σ)|² − (1 + 2d)|ε| e^{−σ} ‖Q‖₁² (1+|s|)^{2d}`.
   - `|e^{−s} − e^{−σ}| ≤ e^{−σ}|ε|`.
   - Lipschitz bound `|Q(z) − Q(σ)| ≤ |z − σ| · d ‖Q‖₁ (1 + |z|)^{d−1}` for `|σ| ≤ |z|`.
   - `|Q(z)| ≤ ‖Q‖₁(1+|z|)^d`.
3. **Window counts.** Split `[1, 2]` into `2d+2` intervals `J_i` of length `1/(2d+2)`. By Riemann–von Mangoldt, `N(T) = (T/2π)log T (1+o(1))`. The number of copies with `σ_q ∈ J_{2k}` is at least `N(√(x_{2k+1}/a)) − N(√(x_{2k}/a + ¼)) ≥ c_d a^{−1/2} log(1/a)` for `a` small, because the endpoints have a fixed ratio greater than `1`.
4. **Lagrange.** Points `t_k ∈ J_{2k}`, `k = 0..d`, are `1/(2d+2)`-separated in `[1,2]`. Every `Q` of degree `≤ d` satisfies `‖Q‖₁ ≤ L_d Σ_k |Q(t_k)|`, with `L_d = (d+1)(3(2d+2))^d`.
   - Taking `t_k` to minimize `|Q|` over the window copies in `J_{2k}` gives `Σ_{window} |Q(σ_q)|² ≥ K ‖Q‖₁² / (L_d²(d+1))`, where `K = min_k #J_{2k}`.
5. **Error.** `Σ_q e^{−σ_q}|ε_q|(1+|s_q|)^{2d} ≤ C_d √a Σ_q e^{−aγ_q²/4} ≤ C'_d log(1/a)`. This uses `a|γ|e^{−aγ²/2} ≤ C√a e^{−aγ²/4}`, `sup_u e^{−u/2}(2+u)^{2d} < ∞`, and the count bound `#{|γ| ≤ T} ≤ C(T+1)log(T+6)` summed over the shells `j ≤ √a|γ| < j+1`.
6. **Combine.** `Re H_a ≥ (e^{−2}K/(L_d²(d+1)) − (1+2d)C'_d log(1/a)) ‖Q‖₁²`. Since `K ≥ c_d a^{−1/2} log(1/a)`, this is positive for `a < a_d`.

## No-go closure (C50)
- **Exact killing mechanism:** detecting a fixed off-line pair needs degree `≫ a^{−1/2}` (the real frequencies that dominate the weighted mass must be killed). The heat-time flow is isospectral, so HCF has no continuity method.
- **Strongest positive survivor:** this card.
- **New insight:** RH is the uniformity in `d` of the window. Unconditionally, `a_d` decays like `d^{−O(d)}`.
- **Status:** paper proof complete; Lean closed.

## Lean
- **Superseded (2026-10-10).** Corpus Route U already proves an unconditional LINEAR window from the
  arithmetic side, strictly stronger than this card's super-exponential `a_d`:
  `XiShiftedParabolicDegreeHorizon.xiPolynomialGaussianHeatTraceReal_ge_parabolicWedgeMass` on the wedge
  `a(deg+1) ≤ κ = routeUCompletedPrimeGammaAperture`. The earlier zero-side modules
  (`RHTower/XiGaussianHeatHankelSmallTimeWindow`, `HTGeometry/PolynomialCoeffMassLagrange`) were removed.
- `RHTower/XiGaussianHeatHankelLinearWindow.lean` (axioms: propext, Classical.choice, Quot.sound):
  - `heatHankel_eq_add_polynomialTrace`: H_a(P) = trace(Re P) + trace(Im P), where P = A + iB, so P(w)·conj P(w̄) = A(w)² + B(w)².
  - `heatHankel_re_pos_of_window`: P ≠ 0 and a(deg P + 1) ≤ κ ⇒ Re H_a(P) > 0.
  - `exists_heatHankel_pos_of_natDegree_le` (same statement as before; now a₀ = κ/(d+1)).
  - `heatMomentDet_pos_of_mul_le`: Δ_N(a) > 0 whenever aN ≤ κ.
- The paper proof above (Riemann–von Mangoldt windows plus Lagrange) stays as an independent zero-side argument. It is zero-blind and gives only a_d = exp(−exp(O(d log d))).

## Log
- 2026-10-10 — created in 1-in-progress (paper proof complete).
- 2026-10-10 — Lean closed; moved to 3-formalized.
- 2026-10-10 — Lean replaced by the Route-U corollary (linear window, explicit κ); zero-side modules removed.
