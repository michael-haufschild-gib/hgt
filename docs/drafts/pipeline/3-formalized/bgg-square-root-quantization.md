# The quantization of the square-root surplus

- **ID:** bgg-c14
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `ξ` have no off-critical zero at ordinate `γ`.
  1. For a (perturbed) positive deformation `−F'/F + ζ_γ'/ζ_γ = 𝓛ν + E` of `ζ_γ` in
     `HeightCoupledSystem 2 1 1 γ` (`ν ≥ 0`, `E` holomorphic on `Re s > σ_E`, `σ_E < 1/2`), the residue
     `(σ − 1/2) 𝓛ν(σ)` converges as `σ ↓ 1/2` to `D = ord_{1/2}Λ_γ − ord_{1/2}Λ`, with `D` even and
     `0 ≤ D ≤ 2 ord_{1/2+iγ} ξ`.
  2. For an arithmetic member `−F'/F = Σ b(n)n^{−s}` whose deficit against `b_γ` converges on `Re s > 1/2`
     with zero Abel residue, the surplus measure `Σ (b(n) − b_γ(n))⁺ δ_{log n}` has Abel residue `D` with the
     same properties.

## Paper proof
The Abel limit theorem across `Re s = 1/2` (at height `0`) gives `(σ − 1/2)𝓛ν(σ) → ord_{1/2}Λ_γ − ord_{1/2}Λ`;
the limit of nonnegative quantities is nonnegative. Central orders are even because `Λ` and `Λ_γ` are
symmetric under `s ↦ 1 − s` (reflection parity). `ord_{1/2}Λ_γ = 2 ord_{1/2}(2ξ) + 2 ord_{1/2+iγ}(2ξ)` and
`ξ(1/2) ≠ 0`. In the arithmetic case the deficit is Abel-negligible on the line (`|D(σ + it)| ≤ D(σ)`), so
the abstract Abel limit applies to the surplus measure.

## Lean
`TheQuantizationOfTheSquareRootSurplus.lean`: `even_centralOrder_of_heightCoupled`,
`centralOrder_heightCoupledΛ`, `quantization_of_tendsto`, `tendsto_abel_excess_eq_centralDrop`,
`tendsto_surplus_residue_eq_centralDrop`. Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
