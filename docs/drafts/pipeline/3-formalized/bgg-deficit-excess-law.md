# The deficit residue bounds the central excess

- **ID:** bgg-c5
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For an arithmetic member `−F'/F = Σ b(n)n^{−s}` (`b ≥ 0`, abscissa `≤ 1`) of
  `HeightCoupledSystem 2 1 1 γ` with deficit `d = (b_γ − b)⁺` whose series `D` converges absolutely on
  `Re s > 1/2`, and no off-critical zero of `ξ` at ordinate `γ`:
  `liminf_{σ↓1/2} (σ − 1/2) D(σ) ≥ ord_{1/2} Λ − ord_{1/2} Λ_γ`.

## Paper proof
Perturbed positive-deformation theorem with `σ_E = 1/2` and `E = b(1) − D`: the abscissa `c` of the
surplus measure satisfies `c ≤ 1/2` (else `ξ(c + iγ) = 0`, `c > 1/2`), so on the real segment right of
`1/2` (punctured cofactor balls) `Λ_γ'/Λ_γ − Λ'/Λ = 𝓛(surplus) + b(1) − D`. Multiply by `σ − 1/2`:
LHS → `ord Λ_γ − ord Λ`, surplus term `≥ 0`, `(σ − 1/2)b(1) → 0`; rearrange.

## Lean
`TheDeficitResidueBoundsTheCentralExcess.lean`: `deficit_residue_ge_centralExcess`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
