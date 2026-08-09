# Formalized: Burnol Poisson-subordinate smooth Cartier entrance wall

- **ID:** `burnol-poisson-subordinate-smooth-cartier-entrance-wall-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-poisson-subordinate-smooth-cartier-entrance-wall.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolPoissonSubordinateWall` | the card |
| `GaloisForLFunctions.RHTower.BurnolGlasserIntegral` | the Glasser evaluation and the square-root subordination identity (new reusable analysis) |
| `GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall` | the completion multiplier and the prime-series thresholds |

## Formal theorem chain

1. `burnolPoissonWeight` — `(PS1)`: the subordination weight `A_{y,p} = p⁻¹ e^{-y√(log p)}`.
2. `burnolSummable_poissonWeight_logPow` — `(PS6)`, `(PS7)`: the weight survives every prime-log
   differential domain, by the domination `u^{2k} e^{-2y√u} ≤ C/u²`
   (`burnolPow_mul_exp_neg_sqrt_le`) against `∑ 1/(p (log p)²)`.
3. `burnolNotSummable_poissonWeight_expGain` — `(PS9)`, `(PS10)`: no positive analytic radius; for
   every `a > 0` the gain `e^{2a log p}` destroys summability, since `√u = o(u)` and `∑ 1/p = ∞`.
4. `burnolGlasser_integral` — the Glasser evaluation
   `∫₀^∞ e^{-t² - b²/t²} dt = (√π/2) e^{-2b}`, proved by the reciprocal involution `t ↦ b/t`
   (which equates the two halves, `burnolGlasser_reciprocal_integral`) and the Glasser map
   `t ↦ t - b/t` (`burnolGlasser_image`, `burnolGlasser_injOn`,
   `hasDerivWithinAt_burnolGlasser`, `burnolGlasser_sq`), which carries the positive ray onto the
   whole line and reduces the sum of the halves to the Gaussian integral.
5. `burnolPoissonSubordination` — **`(PS11)`**:
   `e^{-y√λ} = (y/(2√π)) ∫₀^∞ s^{-3/2} e^{-y²/(4s)} e^{-sλ} ds`, by the change of variables
   `s = y²/(4t²)`.
6. `burnolPoissonWeight_subordination` — **`(PS2)`**: the same identity at `λ = log p`, exhibiting
   the weight as the Poisson extension of the singular prime boundary.
7. `hasDerivAt_burnolPoissonWeight`, `hasDerivAt_burnolPoissonWeight_second` — `(PS12)`:
   `∂_y² X_y = D X_y`, coefficientwise.
8. `hasDerivAt_burnolPoissonWeight_sq`, `burnolPoissonInwardFlux_eq`,
   `burnolPoissonInwardFlux_nonneg`, `burnolPoissonTotalInwardFlux_nonneg` — `(PS13)`: the inward
   flux law and its positivity.
9. `burnolPoissonInverseCompletionCoefficient`, `..._eq`, `norm_...` — `(PS3)`, `(PS14)`.
10. `burnolSummable_poissonInverseCompletion_of_re_le_half` — `(PS15)`.
11. `burnolNotSummable_poissonInverseCompletion_of_half_lt_re` — `(PS16)`.
12. `burnolPoissonSmoothWall` — **`(PS4)`**: full prime-log differential regularity of the
    inverse-completed jet is exactly `Re ρ ≤ 1/2`; past the wall it is not even square summable.

## Verification

- `lake env lean` clean, no warnings, on both modules.
- `lake build GaloisForLFunctions.RHTower` compiles them inside the area umbrella.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.

## Reusable byproduct

`BurnolGlasserIntegral` is independent of the Burnol setting: it supplies the Glasser evaluation and
the `1/2`-stable subordination identity, neither of which is in mathlib.
