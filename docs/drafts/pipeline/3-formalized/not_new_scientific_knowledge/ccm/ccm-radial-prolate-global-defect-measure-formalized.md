# Global radial-prolate defect measure of the constrained CCM source — formalized closure

- **ID:** `ccm-radial-prolate-global-defect-measure-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-radial-prolate-global-defect-measure.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

New: `GaloisForLFunctions.RHTower.CCMRadialGlobalDefectMass`.

Pre-existing and reused: `CCMRadialProlateProfileMeasure`, `CCMRadialProfileAsymptotic`,
`CCMRadialSquaredProfile`, `CCMRadialDensityBridge`, `FresnelIntegral`, `BesselJZeroConstant`,
`RadialLeakageArcsineMeasure`, `RadialLeakageWeakConvergence`,
`RadialLeakageWeakConvergenceTransfer`, `RadialLeakageMassNormalization`,
`CCMRadialProlateDefect`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(5)`, `(7)` phase | `abs_sqrt_sq_sub_sub_le`, `abs_xiSpeed_sub_second_order_le`, `abs_xiEndpointPhase_sub_second_order_le` | the second-order expansion of `ξ_σ` with an explicit error |
| `(7)` amplitude | `xiAmplitude_pow_four`, `abs_xiEndpointPhase_sq_sub_le`, `abs_xiAmplitude_sub_inv_sqrt_le` | `|A_σ(x) − x^{−1/2}| ≤ 4σ²`, globally on the ray |
| Fresnel | `tendsto_integral_cexp_sq_atTop`, `fresnelValue_eq`, `tendsto_integral_cos_sq_atTop` | `∫₀^∞ e^{ix²} = √π e^{iπ/4}/2` — absent from mathlib |
| Bessel constant | `abs_sqrt_mul_besselJ0_sub_le` | `√u J₀(u) = (cos u + sin u)/√π + O(u^{−1/4})` |
| `(8)` | `abs_radialProfile_sub_le`, `sqrt_mul_xiAmplitude_div_eq` | the fixed-degree radial profile, with three explicit `o(1)` errors |
| `(9)`, `(10)` | `abs_integral_profileSq_sub_le`, `abs_integral_profileSq_sub_density_le`, `abs_integral_testFunction_profileDiff_le` | the weak squared-profile law on intervals and against `C¹` test functions |
| `(17)` | `integral_Ioi_profileDensity` | the limiting density has total mass exactly `1/2` |
| density bridge | `profileDensity_eq_radialLeakageDensity_div_pi`, `radialAngle_eq_pi_div_two_sub_arcsin` | the limiting measure is the tree's arcsine leakage measure |
| `(14)`, `(15)` | `integral_Ioi_radialProfileSq` | the exact change of variables `y = λx` in the leakage norm |
| `(16)` | `tendsto_aperture_mul_integral_radialProfileSq` | `c ∫₁^∞ \|R_λ\|² → 1/2` |
| `(18)` | `tendsto_sq_mul_integral_radialProfileSq` | `λ² ∫₁^∞ \|R_λ\|² → 1/(4π)` |
| `(19)` | `integral_outerProfileSq_eq` | the outer window is the `(18)`-normalized mass of a shrinking band |
| no edge atom | `integral_Ioc_nuInfinityDensity` | `∫₁^b ν_∞ = (8/(11π))(π/2 − arcsin(1/b)) → 0` |
| `(20)` | `tendsto_integral_outerProfileSq` | all normalized mass escapes the former outer coordinate |

## Axioms

`#print axioms` on all nine declarations of the new module returns exactly
`[propext, Classical.choice, Quot.sound]`; the reused modules were already clean.

## Deliberately outside the Lean statement

- The PSWF normalisation `(1)`, Dunster's `(4)` for the actual mode, and the separation law `(6)` —
  the identification of the abstract radial profile with the Fourier ratio of the true prolate
  mode. Everything downstream of that dictionary is proved.
- The exact constrained leakage and endpoint-response constants `(13)`, which this card imports from
  `ccm-constrained-endpoint-euler-response-constant` (itself now stage 3) and which enter the Lean
  statements as named hypotheses.
- The pointwise finite-density law feeding the Scheffé transfer, i.e. the card's own `(12)` for the
  true mode.
- The route gates `(21)`–`(22)`: the uniform all-dilation asymptotic and the von Mangoldt-weighted
  correlation law, which the card explicitly does not claim.

## Verification performed

- `lake env lean` on the new module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMRadialGlobalDefectMass`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
