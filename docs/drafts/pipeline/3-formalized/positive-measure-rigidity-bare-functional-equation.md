# Positive-measure rigidity from the bare functional equation (W6(v))

- **ID:** positive-measure-rigidity-bare-functional-equation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2510/hard-obstacles.md`, ACS route (a): "W6(v): the bare-FE form of
  rigidity"; summary W6(v) "derive the strip-decay premise from finite order and absolute convergence
  by Phragmén–Lindelöf"; first milestone (6).
- **Statement.** Let `ν ≥ 0` with `ν(−∞,1) = 0` and `∫ u^{−3/2} dν < ∞`. If `Γ_ℝ(s) D_ν(s)` on
  `Re s = 3/2` and `Γ_ℝ(1−s) D_ν(1−s)` on `Re s = −1/2` equal `E(s) + αΓ_ℝ(s) + βΓ_ℝ(s−1)` with `E`
  differentiable on `−1/2 ≤ Re s ≤ 3/2` and `‖E(s)‖ ≤ C₀ e^{‖s‖^ρ}` there, then `β = −α`, `α ∈ ℝ`,
  `−2α ≥ 0` and `ν = (−2α) Σ_{k≥0} δ_{k+1}`.

## Lean
`GaloisForLFunctions.ArithmeticPositiveDuality.measure_eq_of_completed_functional_equation_of_finiteOrder`
(`formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureRigidityFromTheBareFunctionalEquation.lean`),
with `norm_le_of_edges_of_finiteOrder` (Phragmén–Lindelöf decay transfer) and
`isBigO_strip_of_finiteOrder_on`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into
`ArithmeticPositiveDuality.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. Edges. On `Re s = 3/2`, `E = Γ_ℝ(s)D_ν(s) − αΓ_ℝ(s) − βΓ_ℝ(s−1)` with `‖D_ν(s)‖ ≤ ∫u^{−3/2}dν`; on
   `Re s = −1/2`, `E = Γ_ℝ(1−s)D_ν(1−s) − αΓ_ℝ(s) − βΓ_ℝ(s−1)`. `Γ_ℝ` is `O(1/(1+t²))` on the lines
   `Re = 3/2, 1/2, −1/2, −3/2` (`exists_decay_Gammaℝ_vertical_line`), so `‖E‖ ≤ K/(1+t²)` on both edges.
2. Finite order is `O(exp(B e^{c|t|}))` with `c = π/4 < π/2` (`isBigO_strip_of_finiteOrder_on`).
3. Phragmén–Lindelöf on the strip of width 2: `‖E‖ ≤ K` inside.
4. `F(s) = E(s)(s+2)²`: on the strip `1 + t² ≤ ‖s+2‖² ≤ 13(1+t²)`, so `F` is bounded by `13K` on the
   edges and by `13K(1+t²) ≤ 13K exp(2e^{|t|})` inside; Phragmén–Lindelöf gives `‖F‖ ≤ 13K`, hence
   `‖E(s)‖ ≤ 13K/(1+t²)`.
5. Apply `measure_eq_of_completed_functional_equation`.
