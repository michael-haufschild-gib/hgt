# Arithmetic harmonic analysis at the spacing scale (SSHA)

- **ID:** ssha
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean)
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q1 B3.25/B3.26, Q2, Q3)
- **Statement:** Programme `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/`; first pillar: there is an absolute `c₀ > 0` with `M(f_x) ≥ 0` and `Re W + 2S² ≥ 0` on every atomic test of width `≤ c₀ δ_N`, uniformly in `N`.

## Goal
Answer Q1 at the spacing (B3.25), the overlap question (B3.26: critical exponent), and the gauge question at and beyond the spacing (Q2).

## Gates
- [x] 0 → 1  in-progress: plan below
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach (paper proof of SH4)
Notation: `L = log N`, `t = a/N`, `w ≤ cδ_N ≤ c/N`, `‖g‖ = 1`.
1. `ω(y) ≥ 1/(2y)` on `(0,1]` ⇔ `y e^{y/2} ≥ sinh y` (via `cosh y ≤ e^{y/2}` on `[0,1]`, `tanh y ≤ y`).
2. `L(f) ≥ ∫_w^1 ω(y)(2‖f‖² − 2⟨f, f(·+y)⟩) ≥ log(1/w)‖f‖² − 2 Σ_{a<b} |x_a x_b| |K(a,b)|`,
   `K(a,b) = ∫_w^1 ω(y) G(y − log(b/a))`, `G = g ⋆ g̃`; diagonal `G(y) = 0` for `y > w`.
3. `ω(y) ≤ e^{y/2}/(2y)`; for `w ≤ δ_N/2 ≤ ℓ/2`, `|K| ≤ e^{1/2} w/ℓ`, `ℓ = log(b/a) ≥ (b−a)/b`, nonzero only if `ℓ ≤ 1 + w` ⇒ `b ≤ e² a`.
   Row at `a`: `≤ e^{5/2} w a (1 + L)`.
4. Tilted AM-GM with `α(m,k) = k^{−1/2} r(mk)/r(m)`, `r(n) = 1 + n/N`: coefficient of `x_a²` in the bound of `P_N` is
   `up + down ≤ (log(N/a) + C_M + c_ψ) + (1 − (t/2)/(1+t)) log a`.
5. Bracket `≥ 2θ'(0) + log(1/w) − L − C_M − c_ψ − 1/2` once `2 e^{5/2} c ≤ 1/4`.

## Log
- 2026-10-27 — created; README first draft written.
