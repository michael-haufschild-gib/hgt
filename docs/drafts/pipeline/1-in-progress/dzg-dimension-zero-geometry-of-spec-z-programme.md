# Dimension-Zero Geometry of Spec ℤ (DZG) — programme card

- **ID:** DZG
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7, §2.8
- **Statement:** develop the dimension-zero geometry of `Spec ℤ`: descent of positivity from positive
  Tate dimension to `k = 0`, the archimedean place in dimension `k`, the reflection/similitude problem,
  ground states on windows, the prime-blind cone, the function-field dictionary.

## Goal
Answer the §2.7 questions and §2.8 by Lean theorems. Folder
`formal/GaloisForLFunctions/DimensionZeroGeometryOfSpecZ/`, umbrella `DimensionZeroGeometryOfSpecZ.lean`,
README there. WTZ, CWS, ACT are owned by other agents: import, never edit.

## Plan (paper → Lean)
1. Descent and collapse: domination near `k = 0` ⇒ `Q ≥ 0`; the explicit prime-blind family
   `A_k = kD + 2R_A(k)‖H‖²`, `R_A(k) = Σ_{2≤n≤e^A}(n^k − 1 − k log n)n^{−1/2}`, dominates iff `Q ≥ 0` on
   `W_A`. Key bound: `0 ≤ J_k(n) − [n=1] − kΛ(n) ≤ n^k − 1 − k log n` (k ≥ 0), from
   `Σ_{d∣n}J_k(d) = n^k`, `J_k ≥ [·=1] + kΛ`, `Σ_{d∣n}Λ(d) = log n`.
2. Jet constraint on null tests: `Q(H) = 0` + domination ⇒ 2-jet of `A_k` ≥ `2⟨ρ(Λ₂)H,H⟩`.
3. Tilt: `B(e^{kM}H, e^{−kM}H) = W(c_H cosh(k·))`; even in `k`; value `Q` at `0`.
4. Hecke similitudes of `Q` inside the window algebra are scalars; Rosati-fixed elements are scalars.
5. Archimedean even-dimension pieces: `Γ_ℝ(s)/Γ_ℝ(s−2j) = π^{−j}∏_{i=1}^j(s/2 − i)`.
6. Function-field dictionary.

## Status
- README first draft written.

## Log
- 2026-11-02 — created; README draft.
