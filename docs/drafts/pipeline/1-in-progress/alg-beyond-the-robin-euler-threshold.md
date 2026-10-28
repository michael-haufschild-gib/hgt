# The atomic Hodge index up to and beyond the Robin–Euler threshold

- **ID:** ALG-RE
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme step
- **Source:** ArithmeticLorentzianGeometry README, research direction "Trickle-down for ζ"
- **Statement:** Weil positivity on atomic/window tests at overlap ratio `K` well beyond
  `K★ ≈ 6·10⁻⁴`: first up to a fixed fraction of the Robin–Euler threshold `K_RE`, then past it.

## Goal
`K_RE = e^{β(φ)/‖φ‖²}/(2π)` (≈ 0.43 plateau profiles, ≥ 1/(2π) ≈ 0.16 every window profile). Below
`K_RE` the Markov form is positive on the pole vector, so "lower-bound `M`, pay `|2AB|`" works and the
limit is constants. At and beyond `K_RE`, `M(pole) < 0` (proved), so the sign of the pole term along
the pole vector and a gap of `M` on the pole complement are needed.

## Phase A — sharp stability regime (target `K★ ≈ 0.09` plateau, `≈ 0.06` all windows)
Error budget at `K = wN`: positivity needs
`log(K_RE/K) − ε ≥ K(L_X + P_X)` and `1 − ε ≥ K(L_D + P_D)`.
Current `(L_X, L_D, P_X, P_D) = (1517, 236, 107, 54)`. Targets:
- A1 Lévy cross: one-sided pairs (only `n > m` meet at `t > 0`), window bound `ω(s − w)‖G_m‖₁‖G_n‖₁`
  (Fubini, `‖G‖₁ ≤ √w‖G‖₂`), rows `Σ_{n≠m} 1/|log(n/m)| ≤ m(H_{m−1} + H_{N−m}) + N − m`.
  Gives `L_cross ≤ K/(1−κ) · Σ (m/N)(1 + log N) y_m² + K(1/(2(1−κ)) + 1)|y|²`, `κ = w/δ_N`.
- A2 Top payment with parameter `λ`: `Σ (m/N) log m y_m² ≤ (1 + 1/λ) D + (1 + λ) B_ψ |y|²`,
  `B_ψ = sup ψ(y)/y` bound; `u(1 + log(1/u)) ≤ 1`. ⇒ `L_D ≈ 3.3`, `L_X ≈ 12`.
- A3 Hardy, eventually in `N`: edge part `(1/2 + ε) N²/log N · D` (split at `N^{1−η}`), up-row
  `(B² + ε) N²/log N · |y|²` (partial summation with Chebyshev), `H_N ≤ (1+ε) log N`, AM-GM with
  `θ = √β` ⇒ `P_X ≈ 2√(2)B ≈ 4`, `P_D ≈ 0.5`.
- A4 Assembly: explicit `K★_sharp(ε, κ_min)`.

**Status A:** done (Lean). Constants realized: `L_D ≈ 6.7`, `L_X ≈ 16.4`, pole `7.6` (X), `0.71` (D);
`K★_sharp = min(1/10, 1/(2C_D), a/C_X, e^{T−ε−a−1/25})`, `C_X ≈ 24`, `C_D ≈ 7.4`, `T = log K_RE`:
≈ 0.067 plateau, ≈ 0.048 all profiles (`eventually_weilQuad_windowTest_nonneg_sharp`). Remaining
factor ≈ 6 to `K_RE`: PNT up-row (B_ψ² → 1), Fubini ‖·‖₁ windows (factor 2), λ/κ tuning.

**Status A′:** done (Lean). Fubini `∫|c_mn| ≤ ‖G_m‖₁‖G_n‖₁` halves the cross penalty; PNT up-row
`Σ m R_m² ≤ ((1+η)²/b² + o(1)) N²/log N`; `λ = 1/4, κ = 3/20, b = 19/20, θ = 2, ρ = 3/2`:
`C_X ≈ 10.5`, `C_D ≈ 7.0`, `K★_q ≈ 0.108` plateau (= K_RE/4), `≈ 0.072` all profiles
(`eventually_weilQuad_windowTest_nonneg_quarter`). Ceiling of the absolute-value method:
`log(K_RE/K) ≥ K·C_X` with `C_X` bounded below by the Lévy loss and the pole cost ⇒ `K ≲ K_RE/2`.

## Phase B — exact reduction (all `K`)
`W ≥ 0` on atomic tests ⇔ `M ≥ 0` on the pole complement `Σ x_n/√n = 0` ∧ `M(x) + 2B(x) ≥ 0` on
`Σ x_n/√n = 1` (H-row of an atomic test is exactly `(∫g e^{−v/2}) n^{−1/2}`).

**Status B:** done (Lean, TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar):
`forall_add_two_mul_nonneg_iff`, `forall_weilQuad_atomicTest_nonneg_iff` (every width, `M + 2a₀B`
on `p = 1`), `eventually_markovEnergy_pole_neg_and_gap` (beyond `K_RE`: `M(pole) < 0`, `p(pole) =
H_N > 0`, and `W ≥ 0` ⇒ `M ≥ 0` on `p = 0`, so exactly one negative direction).

## Phase C — beyond `K_RE`
Pole gauge `z_n = √n x_n = c·1 + z⊥`: pole term `2a₀b₀(c² N H_N + c H_N Σ z⊥)`, positive on `c`.
Needs: explicit Poincaré gap of `D` on `z⊥` (RAPT: existential only), asymptotically exact Lévy cross
on the `c`-direction (`≈ c_φ K|x|²` heuristically) and on `z⊥`, Hardy on `z⊥`. Leading-order margin
along the pole direction ≈ `log(K_RE/K) + c_φK` (> 0 up to `K = 1` for plateau profiles); on the
complement it depends on the explicit gap. Outcome not known before computation.

## Log
- 2026-10-28 — created; Phase A done.
- 2026-10-28 — A′ (Fubini, PNT, tuning) and B done; next: Phase C.
