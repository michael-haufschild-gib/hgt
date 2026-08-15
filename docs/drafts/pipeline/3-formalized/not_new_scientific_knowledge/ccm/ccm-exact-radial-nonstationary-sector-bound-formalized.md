# The exact CCM radial nonstationary prime sector vanishes cofinally — formalized closure

- **ID:** `ccm-exact-radial-nonstationary-sector-bound-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-exact-radial-nonstationary-sector-bound.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.RHTower.RadialSymbolTwoBranchInstance` — the instantiation.

Pre-existing and reused (all umbrella-wired):

- `HTGeometry.NonstationaryPhaseLowerBound` — the first-derivative test.
- `HTGeometry.TwoPhaseOscillatoryProduct` — the four-branch product expansion and budgets.
- `HTGeometry.OscBudgetSymbolBound` — the symbol-class budget bound.
- `HTGeometry.GronwallVariableCoefficient`, `HTGeometry.GronwallScaledBound` — the Volterra machinery.
- `RHTower.RadialDilatedPhaseSeparation` — the two-index phase separation `(6)`.
- `RHTower.RadialTwoIndexOscillatoryBound` — the phase, its curvature, and the four-branch assembly.
- `RHTower.RadialSymbolTwoBranchBound` — `SymbolTwoBranch` and `(8)` with explicit constants.
- `RHTower.RadialPSWFExteriorPhase`, `RHTower.RadialPSWFInteractionPicture`,
  `RHTower.RadialPSWFAmplitudeVariation` — the exact two-branch decomposition and its `O(1/c)`
  amplitude variation.
- `RHTower.XiAmplitudeDecay`, `RHTower.ExteriorDunsterPrimitive` — the Liouville amplitude's
  half-power symbol bounds and their continuity.
- `RHTower.RadialNormalFormPotentialDecay` — `|ψ(x)| ≤ 54/x²`.
- `RHTower.RadialGramOffDiagonalDecay` — the arithmetic summation `(9)`–`(10)`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`, exact form | `radialInteraction_reconstruct`, `hasDerivAt_radialInteractionPlus/Minus`, `realPart_eq_twoBranch` | the oscillatory decomposition as an exact consequence of the ODE, not a factored big-`O` |
| `(3)` | `radialInteractionTotal_le_exp`, `integral_norm_deriv_radialInteraction_le`, `abs_xiAmplitude_le_four`, `abs_xiAmplitudeDeriv_le`, `abs_dilatedXiAmplitude_le`, `abs_dilatedXiAmplitudeDeriv_le` | the symbol bounds, with the `O(1/c)` total variation of the interaction amplitudes and the `x^{-1/2}` geometric prefactor |
| potential decay | `abs_lgNormalFormDefect_radialProlate_le_sq` | `|ψ| ≤ 54/x²`, uniform in the bandwidth |
| phase growth | `sub_one_le_xiEndpointPhase`, `le_dilatedRadialPhase` | `x ≤ ξ_s(rx)`, converting a `ξ^{-2}` bound into an `x^{-2}` one |
| `(5)` | `dilatedPhaseSpeed`, `dilatedPhaseSpeed_eq` | the dilated phase derivative |
| `(6)` | `sub_dilatedPhaseSpeed_ge`, `le_add_dilatedPhaseSpeed` | the two-index separation, proved without differentiating in the index |
| phase curvature | `abs_dilatedRadialPhaseAccel_sub_le`, `abs_dilatedRadialPhaseAccel_add_le` | `|j²ξ''(jx) ∓ k²ξ''(kx)| ≤ (16/9)/x³` |
| `(7)` | `abs_half_mul_add_le'`, `abs_half_mul_deriv_sub_le'`, `oscBudget_le_of_symbolBounds` | the product weights are a `1/x` symbol with a `1/x²` derivative, and the budget is endpoint-uniform |
| `(8)`, abstract | `abs_integral_radial_twoBranch_symbol_le'` | the entry estimate from two symbol records alone |
| `(8)`, **instantiated** | `symbolTwoBranch_radialPSWF`, `symbolTwoBranch_radialPSWF_of_bounds`, `abs_integral_radial_entry_le` | the same for a genuine solution of the exterior normal form, with `M_r = (4/√r)(2K_t)` and `M_r' = M_r + (4/√r)κK_t(4r/3)/c` |
| `(9)`–`(10)` | `RadialGramOffDiagonalDecay` — the exact partial-fraction row sum, the row bound `R K ≤ 3(1+log K)/K`, and summability of `∑ log K (1+log K)/K²` | the logarithmically weighted arithmetic sector |

## Axioms

`#print axioms` on every declaration of the new module and of the reused modules returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- Dunster's Liouville–Green construction itself, i.e. the identification of the abstract `W`, `V`,
  `ψ` of the normal form with the actual constrained prolate source `q_λ` and the identification of
  the interaction-total bound `K_t` with `C√d₁/√r`. The Lean statement is proved for *every*
  solution of the exterior normal form with those bounds, which is where the card's mathematics
  lives; naming the solution is the source-side dictionary the card imports.
- The first-row sector `(11)` and the hybrid Bessel/Liouville–Green transfer, which the card itself
  assigns to `ccm-limiting-radial-first-row-weber-bound.md` and to the route's next step.

## Verification performed

- `lake env lean` on the new module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.RadialSymbolTwoBranchInstance`: success.
- `#print axioms` on all fifteen declarations: clean.
- Umbrella import added.
