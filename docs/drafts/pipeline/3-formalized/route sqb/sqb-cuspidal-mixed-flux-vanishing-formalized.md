# SQB mixed cusp flux: full-height vanishing and a tail bound — Lean certificate

- **Paper card:** `sqb-cuspidal-mixed-flux-vanishing.md`
- **Lean module:** `GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFluxLimit`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** as for `sqb-cuspidal-mixed-flux-energy-formalized.md` (same module and audit).

`J_V = sourceTestBoundaryCurrent`, `G_V = sourceTestGreenDensity`, `E_F(Y) = cuspCylinderEnergy N F Y`
with `E_F(Y)² = ∫_Y^∞ y⁻² (E_X F + E_Y F)(y) dy = ∑_q∫_Y^∞∫_0^L (|∂ₓF_q|² + |∂_yF_q|²)`.

| Card item | Lean theorem |
|-|-|
| `J_V ∈ L¹(Y,∞)`, `J_V(y) → 0`, `J_V(Y) = -∫_Y^∞ G_V` | `sourceTestFlux_tail_law` |
| `G_V` = the displayed three-term density | `sourceTestGreenDensity_eq_of_gt` |
| (1) `|J_V(Y)| ≤ [1 + λ(L/(2πY))²] E_U(Y) E_V(Y)` | `norm_sourceTestBoundaryCurrent_le_cylinder` (weighted density bound `norm_sourceTestGreenDensity_le_weighted`, optimization `le_mul_sqrt_mul_sqrt_of_forall`) |
| energies finite, tails → 0 | `integrableOn_cylinderDensity`, `tendsto_cuspCylinderEnergy` |
| (2) uniform bound over `E_V(Y) ≤ 1`, right side → 0 | `uniform_sourceTestBoundaryCurrent_tail` |
| `E_V(Y)² ≤ L ‖V‖²_form` (periodization + cusp tail) | `cuspCylinderEnergySq_le_form`, `deckSliceEnergy_hypGradX_eq_centered`, `tail_le_toDeckL2` |
| boundary functional extends continuously through form completion, norm → 0 | `exists_upperBoundaryFunctional_extension`, `norm_upperBoundaryFunctional_le`, `tendsto_upperBoundaryFunctional_norm_bound` |
