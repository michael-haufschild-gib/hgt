# SQB mixed cuspidal flux from form energy — Lean certificate

- **Paper card:** `sqb-cuspidal-mixed-flux-energy.md`
- **Lean module:** `GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFluxLimit` (namespace
  `GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet`); inputs `MaassFiniteDeckCuspidalCrossFlux`,
  `MaassFiniteDeckCuspidalTail`, `MaassFiniteDeckCuspidalGreen`, `MaassFiniteDeckCoreWitness`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean (no warnings, `autoImplicit false`);
  `#print axioms` of all 14 listed theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| exact theorem: `B ∈ L¹(c,∞)`, `D ∈ L¹(c,∞)`, `∫_c^∞ D = -B(c)`, `B(y) → 0` (every `c > 1`, every cusp-zero pre-vector) | `sourceTestFlux_tail_law` |
| `B ∈ L¹(c,∞)` from `|B| ≤ ½(y⁻² E_Y(U) + E(F))` and slice Poincaré | `integrableOn_sourceTestBoundaryCurrent`, `norm_sourceTestBoundaryCurrent_le`, `deckSliceEnergy_le_poincare` |
| (2) Maass substitution `D = ∑∫ [UₓF̄ₓ + U_yF̄_y - λy⁻² U F̄]` | `sourceTestGreenDensity_eq_of_gt` (uses `retractedSourceDeckComponent_laplacian`) |
| `D ∈ L¹(c,∞)` | `integrableOn_sourceTestGreenDensity`, `norm_sourceTestGreenDensity_le` |
| (1) `|B(y)| ≤ (L/4π)(E_Y^U + E_X^F)` type control | `norm_sum_integral_mul_star_le_weighted` with `deckSliceEnergy_le_poincare` |
| finite limit + integrability ⇒ limit zero | `eq_zero_of_integrableOn_Ioi_of_tendsto` |
