# Formalized: Burnol prime-two Gamma-sewn causal Cartier collar law

- **ID:** `burnol-prime-two-causal-cartier-collar-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-prime-two-causal-cartier-collar-law.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolGammaSteinCollarKernel` | Stein profile calculus, `κ_n`, three-chamber law, translate law, deformed kernel |
| `GaloisForLFunctions.RHTower.BurnolGammaSteinMoments` | master Gamma moment, `∫ κ_n = -2^{-n/2} Γ_ℝ(1/2)/16` |
| `GaloisForLFunctions.RHTower.BurnolCollarKernelSeries` | depth decay, normal convergence, crossing commutator, depth pairing, plateau limit |
| `GaloisForLFunctions.RHTower.BurnolPrimeTwoCollarSymbol` | dyadic symbol ladder, Gamma sewing, raw-source landing, reflection |
| `GaloisForLFunctions.HTGeometry.GaussianMellinMoments` | the Gaussian Mellin transform (input) |

## Formal theorem chain

1. `hasSum_burnolXiCompletionMultiplier` — `(3)`, `(4)`: the causal dyadic ladder
   `C₂(w) = ∑_{n ≥ 1} ½ w²(w-1) 2^{-nw}` on the positive half-plane.
2. `burnolCollarGamma`, `burnolCollarZ`, `burnolCollarH` — `(6)`, `(8)`.
3. `burnolCollarGammaFourier_eq` — `(7)`: `∫_ℝ γ(u) e^{-itu} du = Γ_ℝ(1/2 + it)`, by the
   substitution `r = e^{-u}` and the Gaussian Mellin transform.
4. `burnolSteinA_collarProfile` — `(15)`, the single differentiation rule `P ↦ 2z(P - P')`;
   `burnolSteinA_burnolCollarH` is `(14)` and `burnolSteinA_polarOne`, `burnolSteinA_polarTwo`
   give `(16)`.
5. `burnolCollarKernel`, `burnolCollarKernel_eq_steinIterate` — `(9)`.
6. `burnolCollarKernel_neg_iff`, `burnolCollarWidth` — `(17)`, `(18)`: exactly one negative collar
   per depth, of depth-independent width `½ log 6`.
7. `burnolCollarKernel_eq_translate` — `(18a)`.
8. `integral_burnolCollarKernel_depth`, `integral_burnolCollarKernel_depth_neg` — `(18b)`, `(18c)`:
   exact strictly negative total mass `-2^{-n/2} Γ_ℝ(1/2)/16`.
9. `burnolSummable_collarKernel`, `hasSum_burnolCollarKernelTotal`,
   `burnolCollarKernel_normal_convergence` — `(11)`: `κ₂ = ∑_{n ≥ 1} κ_n` converges normally on
   every compact logarithmic interval, from `e^{-z}(2z³+7z²+3z) ≤ 4608 e^{-z/2}` and `z_n ≥ n z_0`.
10. `hasSum_burnolCollarCrossing_depth` — `(12)`, `(20)`: the coefficient-faithful depth lift.
11. `burnolKernelConvolution_commutator`, `burnolCrossingSupport` — `(19)`: the aperture commutator
    is the cross-boundary operator, supported where `u` and `v` are on opposite sides of `b`.
12. `burnolCrossingCorrelation` — `(18d)`.
13. `burnolDepthPairing_eq_crossingCorrelation` — `(18e)` first half (Fubini and the shear
    `s = u - v`); `burnolDepthPairing_translate` — `(18e)` second half, unconditionally, from the
    translate law and translation invariance of Lebesgue measure.
14. `burnolCollarPlateauLimit` — `(18f)`, `(18g)`: the plateau criterion forces the normalized
    depth pairing to converge to `-c Γ_ℝ(1/2)/16`.
15. `burnolPhysicalCollarMultiplier`, `burnolPhysicalCollarMultiplier_mul_rawMellin`,
    `burnolPhysicalCollarMultiplier_mul_dslope_rawMellin` — `(5)`, `(10)`, `(21)`, `(22)`: the
    Gamma-sewn multiplier carries the raw Burnol source `H` to `ξ`, including on first divided
    vectors.
16. `burnolPhysicalCollarMultiplier_reflection` — `(23)`, `(24)`: on the critical line the reflected
    orientation is the complex conjugate, i.e. the logarithmic kernel is real and reflected.
17. `burnolCartierDividedShiftHeadFlux`,
    `xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift` — `(25)`.

## Verification

- `lake env lean` clean, no warnings, on each module.
- `lake build GaloisForLFunctions.RHTower` compiles them inside the area umbrella.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.
