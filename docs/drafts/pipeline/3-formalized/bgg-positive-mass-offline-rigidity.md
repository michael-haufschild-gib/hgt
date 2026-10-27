# Positive prime-mass deformations are rigid off the critical line

- **ID:** bgg-c3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `(F, Λ) ∈ HeightCoupledSystem 2 1 1 γ` with
  `−F'/F(σ) + ζ_γ'/ζ_γ(σ) = ∫₀^∞ e^{−σu} dν(u)` on a real ray, `ν ≥ 0` with finite Laplace mass
  somewhere. If `ξ` has no off-critical zero at ordinate `γ`, then `ord_w Λ = ord_w Λ_γ` for all
  `Re w ≠ 1/2` and `ord_{1/2} Λ ≤ ord_{1/2} Λ_γ`. For `γ ≠ 0` the ceiling over positive
  deformations is equivalent to no off-critical zero at `γ`; RH ⟺ the positive ceiling at all heights.

## Paper proof
1. `ν' = ν + Lebesgue` has an abscissa `c ≥ 0`; `L = 𝓛ν' − 1/s` is holomorphic on `Re s > c` and
   equals `Λ_γ'/Λ_γ − Λ'/Λ` on a real ray (completion factors cancel).
2. The Wronskian `Λ_γ'Λ − Λ'Λ_γ − LΛΛ_γ` vanishes on the ray, hence on `Re s > c` (identity theorem).
3. Near `w`, `(z − w)f'/f → ord_w f`; on `Re w > c`, `(z − w)L(z) → 0`, so orders agree.
4. If `c > 0` and orders agree at `c`, cofactors give a holomorphic extension of `𝓛ν'` across `c`,
   contradicting Landau's theorem; `(σ − c)𝓛ν'(σ) ≥ 0` gives `ord_c Λ_γ − ord_c Λ ≥ 0`, hence `> 0`:
   `Λ_γ(c) = 0`, so `ξ(c + iγ) = 0` and `c = 1/2` without off-critical zeros at `γ`.
5. Symmetry `w ↦ 1 − w` handles `Re w < 1/2`.
6. Converse: the coupled quartet multiplier has posdef sections, so (sieve with zero lattice) its
   scale density `w ≥ 0`; `ν = w dt` makes the contraction a positive deformation raising the
   central order by `4`.

## Lean
`BiarithmeticGaugeGeometry/PositivePrimeMassDeformationsAreRigidOffTheCriticalLine.lean`:
`exists_logDeriv_cofactor`, `tendsto_sub_mul_logDeriv`, `exists_isAbscissa_add_volume`,
`complexLaplace_add_volume`, `positiveDeformation_orders_and_anchor`,
`positiveDeformation_offLine_rigid`, `laplace_withDensity`, `exists_positiveDeformation_above_ceiling`,
`positiveCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_positiveCentralVanishingCeiling`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
