# Critical thresholds and onset aperture

**Complete proof assembly passes Lean. Individual module import checks and pipeline promotion remain.**

For `a* = onsetAperture zetaZeroConfig`, the critical thresholds satisfy

```
0 < R_c = R_c^{nn} = R_c^{polar}
        ≤ R_c^⊥ = R_c^{high} = inf_{A≥0} windowThreshold A.
```

For universal `c₀,c₁,c₂>0` and every finite `0≤a≤a*`,

```
R_c ≥ c₁ exp(c₂a),       R_c^⊥ ≥ c₀ exp(6a).
```

When the corresponding threshold is finite, these imply
`log R_c ≥ log c₁+c₂a` and `log R_c^⊥ ≥ log c₀+6a`.
Every displayed threshold is infinite iff `a*=∞` iff the Riemann hypothesis.
No specific value of the whole-space exponent `c₂` is asserted.

## Formalized conclusions

| Result | Lean declaration and source |
|---|---|
| Whole-space positivity equals polar payment | `criticalPositivityThreshold_eq_polarPaymentCriticalThreshold` in [WholeSpaceCriticalThresholdEqualsPolarThreshold](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/WholeSpaceCriticalThresholdEqualsPolarThreshold.lean) |
| Nonnegativity has the same threshold | `criticalNonnegativityThreshold_eq_polarPaymentCriticalThreshold` in the same module |
| Whole-space exponential and logarithmic onset bounds | `exp_mul_le_criticalPositivityThreshold`, `log_criticalPositivityThreshold_ge_mul_onsetAperture` in the same module |
| Primitive threshold equals the window infimum, with sixth-exponential and logarithmic bounds | [PrimitiveCriticalThresholdEqualsWindowThreshold](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PrimitiveCriticalThresholdEqualsWindowThreshold.lean) |
| Infinite-threshold equivalence chain | `criticalThresholds_eq_top_equivalences` in `WholeSpaceCriticalThresholdEqualsPolarThreshold` |

## Mathematical ingredients

- **Collar restriction and localization.** Unrestricted atomic Gårding fails. Collar Gårding
  holds, and whole-space mass localizes to `(-A,1]` with `A≤¼log(R+1)+C`, retaining
  only the scalar polar loss `C c b₁²/log N`.
- **Nonpolar cancellation.** Fixed nonpolar dual-seventh residuals and the growing nonpolar
  packet Schur cost vanish uniformly on positive compact critical bands.
- **Strong polar profile.** With `aφ=(∫φ)²/∫φ²`, `x=n/N`, the normalized matrix row has sampled
  square-mean profile `aφ√x[1/x−½log(1−x²)−ψ(1/x)−log(2π)]` on every fixed terminal fraction.
  Squared-log endpoint tails and finite-jump ramps permit compact Lipschitz approximation.
  Source: [ThePolarMatrixRowHasItsStrongProfile](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/ThePolarMatrixRowHasItsStrongProfile.lean).
- **Signed physical transfer.** Weighted collar approximation and adjoint synthesis transfer
  the exact polar pairing to strong physical limits; one-sided mollification identifies its
  source with the correct normalization.
  Source: [PolarModeTopWindowLipschitzTransfer](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/PolarModeTopWindowLipschitzTransfer.lean).
- **Charged contradiction.** The sharp finite comparison retains actual pole energy and signed
  collar pairing. Joint normalization `‖U‖₂²+β²=1` survives compactness. The Gamma lower
  bound and polar transfer contradict the positive eighth-mass and pole-square reserve
  supplied by payment at a strictly larger ratio.

The complete proof assembly and all transitive axiom audits pass with only
`propext, Classical.choice, Quot.sound`.

Cards: [whole-space threshold and onset](../../drafts/pipeline/1-in-progress/cact-whole-space-threshold-onset.md),
[prefix–collar decoupling and thresholds](../../drafts/pipeline/1-in-progress/critical-ratio-window-confinement-and-threshold-law.md).
