# Gamma numerical-range coercivity: the weighted-tail theorem, formalized

- **ID:** `suzuki-gamma-weighted-tail-coercivity`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-gamma-weighted-tail-coercivity.md`
- **Lean (card-specific):**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaWeightedTailCoercivity.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaShiftKappa.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiShiftedGammaForm.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaMollifiedEquation.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaWeakDomainUpgrade.lean`
- **Lean (reusable layer built for this card):**
  - `formal/GaloisForLFunctions/HTGeometry/GammaTransportKernel.lean`,
    `GammaJumpTranslationEnergy.lean`, `ShiftedSecondDifferenceBounds.lean`,
    `GammaPairingMajorant.lean`, `GammaPairingFubini.lean`
  - `formal/GaloisForLFunctions/HTGeometry/IntegralCauchySchwarz.lean`,
    `YoungConvolutionL2.lean`, `MollifierPositionCommutator.lean`,
    `MollifierUniformApproximation.lean`, `BumpMollifierFamily.lean`,
    `ScaledMollifierMoments.lean`, `CompactSupportIntegrationByParts.lean`,
    `MollifierL2Contraction.lean`, `WeakLimitBoundedFamily.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CompactKernelL2Convolution.lean`,
    `GammaJumpL2Bound.lean`, `L1FromWeightedL2.lean`, `MollifierTestPairing.lean`,
    `SmoothCompactL2Dense.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)`–`(2)` conjugated Gamma jump | `gammaTransportKernel`, `shiftedSecondDifference`, `shiftedGammaJump` |
| `(3)` `κ_σ < ∞` | `integrableOn_suzukiGammaShiftLowerKernel`, `suzukiGammaShiftKappa`, `suzukiGammaShiftKappa_nonneg` |
| `(9)`–`(10)` exact lower bound | `neg_suzukiGammaShiftLowerKernel_le_realIntegrand`, `neg_suzukiGammaShiftKappa_le_integral` |
| `(11)` numerical range, physical space | `neg_le_integral_shiftedSecondDifference`, `neg_suzukiGammaShiftKappa_mul_le_shiftedGammaForm`, `integral_shiftedGammaJump_mul_self`, `neg_suzukiGammaShiftKappa_mul_le_gammaJumpPairing` |
| `(13)`–`(15)` coercive energy estimate | `suzukiGammaWeightedTailEnergy_norm_le`, `suzukiGammaWeightedTail_derivative_norm_le` |
| `(5)` the weak equation, tested form | `SuzukiGammaTestedEquation` |
| `(16)`–`(18)` the mollified equation, pointwise | `suzukiMollifier`, `suzukiMollifiedDeriv`, `suzukiMollifiedDefect`, `suzukiGamma_mollified_equation` |
| `(17)` position commutator | `mollify_position_eq` (and its pointwise form inside `suzukiGamma_mollified_equation`) |
| `(19)` derivative onto the kernel | `lineConvolution_weightedDeriv`, `integral_deriv_kernel_test` |
| `(20)` mollifier moment bounds | `integral_abs_firstMomentKernel_scaled`, `integral_abs_firstMomentDeriv_scaled`, `integral_abs_suzukiDefectKernel_le` |
| `(21)` support of `U_ε` | `suzukiMollifiedDeriv_eq_zero` |
| `R_σ U_ε ∈ L²` (Fourier step, replaced) | `gammaJumpL2Majorant`, `integral_sq_shiftedSecondDifference_le`, `lintegral_sq_gammaScaleIntegral_le`, `integrable_sq_gammaScaleIntegral`, `integrable_sq_shiftedGammaJump_suzukiMollifiedDeriv` |
| `L U_ε ∈ L²`, `U_ε ∈ L¹` | `hidU2` step inside `suzukiGamma_uniform_energy_bound`, `integrable_of_sq_integrable_of_mul_sq_integrable` |
| `(22)` + `(13)` uniform bound | `suzukiGamma_uniform_energy_bound` |
| the section-4 limit, `(6)` `U ∈ L²` | `suzukiGamma_weakDomain_upgrade` |
| `(6)` `V ∈ H¹` | `suzukiGamma_profile_H1` |
| jump Fubini `⟨R_σU, U⟩ = scale form` | `integrable_gammaPairing`, `integral_gammaPairing_swap` |
| jump transpose `R_σᵀ = R_{−σ}` | `shiftedGammaJump_neg_comp_sub`, `integral_mul_shiftedGammaJump_comp_sub` |
| weak limit machinery | `exists_weakLimit_of_bounded`, `dense_smoothCompactSubmodule`, `tendsto_integral_mul_kernelTest`, `integral_suzukiMollifiedDeriv_mul_test` |

## What is formal, exactly

The card's theorem `(6)` is the terminal statement: **if** the weak equation
`(2L + R_σ − τ)U + V = G` holds in its tested distributional form
(`SuzukiGammaTestedEquation`), with `V, G ∈ L²`, `V` supported in `[L₀, ∞)`, `0 ≤ σ < 1`, and
the coercive budget `κ_σ + |τ| < 2L₀`, **then** the distributional derivative combination
`U = V′ − σV` is realized by an `L²` function, and `V ∈ H¹`.  That implication is
`suzukiGamma_weakDomain_upgrade` / `suzukiGamma_profile_H1`, proved end to end:

```text
tested equation  --test against ρ_ε(x−·)-->  mollified equation (18), pointwise
                 --coercive pairing      -->  uniform L² bound on U_ε
                 --weak limit            -->  U ∈ L², V ∈ H¹
```

The card's two remaining paper items are closed **without Fourier analysis**: the numerical-range
bound `(11)` is the physical-space translation-energy identity, and the `L²` boundedness of
`R_σ U_ε` — the paper's "Schwartz decay of `ρ̂`" step — is replaced by the `L²` scale majorant of
the second difference (`GammaJumpL2Bound`), a weighted Cauchy–Schwarz plus Tonelli argument in
`ℝ≥0∞` that also supplies the joint integrability for every exchange.  The scalar seam instance
`T = τ` realizes the bounded self-adjoint coupling; the abstract Hilbert-valued energy estimate
`(13)`–`(15)` is separately formal in `SuzukiGammaWeightedTailCoercivity.lean`.

## Hypotheses

Every hypothesis of every theorem is object regularity — measurability, square-integrability,
support, the range of `σ`, the coercive budget — or the card's own equation in tested form.  No
hypothesis is an unproved analytic theorem, no completed-source map is assumed, and nothing
assumes RH, a zero hypothesis, or a numerical certificate.

No `sorry`, `axiom`, `opaque`, `unsafe`, or numerical computation occurs.  Every theorem named
above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The open gates are research, not Lean: the literal completed support-pruned carrier map, the
application to completed trace-zero zero modes, the raw Evans kernel identification, Evans
injectivity, and RH.  Section 5's charge elimination applies once the completed-domain
realization exists; that realization is the card's stated frontier.
