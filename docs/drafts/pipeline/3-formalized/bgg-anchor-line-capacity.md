# Anchor-line positivity and the capacity of rational deformations

- **ID:** bgg-c2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a rational deformation `F = F₀ · ∏(s − zᵢ)^{mᵢ}` of a nonnegative lattice base
  with even positive-definite sections, `β ↦ −M(σ + iβ)` is even positive definite on every line
  `Re s = σ` bounding the multiplier points of nonzero net multiplicity. Consequences: critical-zero
  conservation in `HeightCoupledSystem 2 1 1 γ` and the sharp boundary capacity `(κ − d)/2` of
  rational deformations of `ζ^d` in `CompletedPositiveSystem κ d`.

## Paper proof
1. *Line residues.* With `w ≥ 0` and `G = G^*` (evenness), `G(s) = ∫₀^∞ w e^{−st}`. For real
   `aₖ, βₖ`: `∫ w(t)|Σ aₖ e^{iβₖt}|² e^{−xt} dt = Σ aₖaₗ Re G(x + i(βₖ − βₗ)) ≥ 0`; multiply by
   `x − σ`, let `x ↓ σ`: `Σ aₖaₗ c(σ + i(βₖ − βₗ)) ≥ 0`. Evenness: the residue of `G = G^*` at
   `σ + ib` is `c(σ − ib)`.
2. *Order law.* `Λ(s)(s−w)^{M⁻} = Λ'(s) R_w(s) (s−w)^{M⁺}` near `w` (identity off the multiplier,
   continuity at `w`), so `ord Λ + M⁻ = ord Λ' + M⁺`.
3. *HCS.* No off-critical zeros at `γ`: all weighted points lie on `Re s ≤ 1/2` (C1 anchor);
   total-zero-mass for the posdef divisor with `D ≤ 0` off `0`: `2ΣM(1/2 + iβ) ≤ −M(1/2)`; order
   law: `−M(1/2) = ord Λ_γ − ord Λ`.
4. *CPS over `ζ^d`.* `Λ (s(s−1))^{d−κ} = (s(s−1))^{κ−d}(2ξ)^d R`; real zeros of the base only at
   `0, 1` and only if `d < κ`; a boundary zero puts the anchor at `1`; no poles on `Re s = 1` off `1`
   (`ξ(1 + iβ) ≠ 0`); `−M(1) ≤ ord_1 = κ − d`; total-zero-mass gives `2Σ M(1 + iβ) ≤ κ − d`.
   If `κ ≤ d`: no anchor, `R ≡ 1`, and at `s = 1` the identity forces `κ = d`.

## Lean
Module `BiarithmeticGaugeGeometry/AnchorLinePositivityAndCapacityOfRationalDeformations.lean`:
`lineResidue_isEvenPosDef`, `lattice_lineResidue_isEvenPosDef`, `rationalDeformation_lattice_data`,
`rationalDeformation_lineResidue_isEvenPosDef`, `rationalDeformation_anchor`,
`analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier`, `eq_mul_rationalMultiplier_of_agree`,
`rationalDeformation_criticalLine_isEvenPosDef`, `rationalDeformation_critical_conservation`,
`rationalDeformation_zetaPow_rigid`, `rationalDeformation_zetaPow_boundary_capacity`.

## Log
- 2026-10-27 — formalized.
