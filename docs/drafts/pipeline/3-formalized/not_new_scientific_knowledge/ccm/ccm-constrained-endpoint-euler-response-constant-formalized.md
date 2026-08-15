# Exact gap-scale Euler response of the constrained CCM endpoint layer — formalized closure

- **ID:** `ccm-constrained-endpoint-euler-response-constant-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-constrained-endpoint-euler-response-constant.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

Thirty-nine modules, all pre-existing and all umbrella-wired. The card's own "Lean status" section
is the full clause-by-clause account; this certificate records the audit.

Spectral layer (`GaloisForLFunctions.RHTower` unless marked):

`SlepianKernelFourier`, `SlepianKernelFubini`, `SlepianBandCommutation`, `ProlateL2Operator`,
`ProlateL2Family`, `ProlateL2Regularity`, `BandQuadraticFormFourier`, `BandFrequencyWindow`,
`BandLeakageSpectralTail`, `BandFormBridge`, `BandVariational`, `BandOperatorContraction`,
`BandStrictGap`, `BandUncertainty`, `CompactFourierEntire`, `BandLimitedExtension`,
`FourierPlancherelIntegral`, `BandTransformEnergy`, `PaleyWienerNorms`, `ProlateJointEigen`,
`ProlateJointEigenExistence`.

Kaiser–Bessel envelope layer: `BandTrialMoments`, `BandTrialSeries`, `BandKaiserTrial`,
`BandKaiserBounds`, `BandKaiserTail`, `BandKaiserContinuity`, `BandLeakageEnvelope`.

Riccati / WKB layer: `ProlateEndpointLowerBound`, `ProlateRiccati`, `ProlateWKBSubsolution`,
`ProlateWKBIntegral`, and `HTGeometry.DifferentialInequalityComparison`.

Perturbation layer (`GaloisForLFunctions.HTGeometry`): `HellmannFeynman`,
`SimpleEigenvalueBordered`, `SimpleEigenvalueBranch`, `SimpleEigenvalueCompactBranch`,
`LogDerivativeFromEnvelope`.

Response-constant layer: `CCMEndpointResponseIdentity`, `CCMEndpointResponseConstants`,
`CCMEndpointSawtoothResponse` (over the pre-existing `CCMSawtoothDilationMean`,
`CCMSawtoothDilationIncidence`, `CCMSawtoothExteriorTail`).

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(6)` | `sincSmooth_eq_integral`, `double_integral_fourierChar_eq_sincKernel`, `double_integral_sincKernel_eq_energy` | `Q_c = (c/2π) F_c* F_c`, at kernel, integrated and quadratic-form level |
| `(7)` | `double_integral_cos_eq_norm_sq`, `expectation_cosKernel_eq` | the cosine factorisation of the Hellmann–Feynman derivative |
| Hellmann–Feynman | `HTGeometry.hellmann_feynman`, `hellmann_feynman_eventually` | new infrastructure; absent from mathlib |
| differentiable simple branch | `exists_normalized_branch_of_isCompactOperator`, `exists_bandOperatorL2_branch` | Kato-type perturbation theory built from scratch: bordered system, implicit function theorem, Fredholm pseudo-inverse |
| `(4)` | `endpointResponse_eq`, `endpointResponse_of_hellmannFeynman` | `ν′(c) = 2 ν(c) \|ψ(1)\|²/c` |
| `(5)` | `hasDerivAt_ccmGap`, `endpointResponse_scaled` | the CCM-variable form |
| `(9)`, envelope reduction | `tendsto_deriv_of_monotoneOn_of_tendsto_div`, `tendsto_logDeriv_of_envelope_of_antitoneOn`, `tendsto_scaled_logDeriv` | the differentiated Fuchs asymptotic reduced to the two-sided envelope plus antitonicity |
| `(10)` | `tendsto_endpointSq_div_leakage`, `tendsto_endpointSq_div_leakage_of_envelope` | `\|e_{m,λ}(λ)\|²/(λ d_m(λ)) → 2π` |
| `(11)` | `tendsto_endpointSq_div_reference` | mode-negligibility transport |
| `(12)` | `tendsto_ellSqRatio_of_deltaRatio`, `tendsto_ellSqRatio_of_hermiteLimits`, `hermiteWeight_one` | the `8/11`, derived from the Hermite weight `3/8` |
| `(13)` | `tendsto_constrainedEndpointSq`, `tendsto_constrainedEndpointSq_of_hermiteLimits` | `16π/11` for the two-mode seed |
| `(15)` | `tendsto_lowerExteriorAmplitudeSq` | `\|a_λ\|²/d_1(λ) → 16/(11π)` |
| `(16)`–`(17)` | `sawTail`, `sawTail_mul_shift`, `integral_sawTail_mul_shift`, `tendsto_sawTailPrimeResponse`, `ofReal_tsum_vonMangoldt_div_sq`, `tendsto_sawTailPrimeResponse_ofReal` | the exterior sawtooth incidence constant `π²/12 · (−ζ′(2)/ζ(2))` |
| `(18)` | `tendsto_primeResponse_div_leakage`, `tendsto_primeResponse_div_leakage_sawTail` | the card's headline constant `(4π/33)(−ζ′(2)/ζ(2))` |
| upper leakage envelope | `one_sub_norm_bandOperatorL2_le_exp`, `tendsto_norm_bandOperatorL2_atTop` | `1 − ‖B_c‖ ≤ 64 c² e^{−2c}` for `c ≥ 1`, for the true band operator |
| strict gap | `norm_bandOperatorL2_lt_one` | `‖B_c‖ < 1`, from Paley–Wiener plus the Fredholm alternative |
| WKB endpoint decay | `le_endpoint_prolateWKB`, `integral_prolateWKB_le_aperture`, `exp_neg_aperture_le_endpoint` | the sharp outer-band bound with the exact exponent `≤ c` |

## Axioms

`#print axioms` on all 305 named theorems of the 39 modules returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

Exactly the card's two remaining Lean gates, both of which the card imports from the parent
literature rather than proving:

- the **rate** of the lower leakage envelope — equivalently, the concentration inequality for entire
  functions of exponential type `c` (unit mass on `[−1,1]` forces at least `c₀ c^{1/2} e^{−2c}`
  outside) together with antitonicity of the leakage logarithmic derivative. This is Fuchs's
  asymptotic; the corresponding upper envelope, at the sharp exponential rate, *is* proved here.
- the prolate-to-Hermite coefficient limits `ℓ_j(λ) → h_{4j}(0)` for the true operator — Slepian's
  fixed-mode expansion. What the `8/11` needs from it is isolated and everything downstream of it is
  proved.

Also outside, and flagged by the card itself: the passage from the model seed `b_λ⁰` to the true
Weil ground state, the renormalized exact-tail remainder, and the archimedean endpoint response
(which is the separate card `ccm-leading-endpoint-archimedean-log-law`).

## Verification performed

- `lake build` on all 39 modules: success (3230 jobs).
- `rg` for `sorry`, `admit`, `axiom`, `opaque` across all 39 files: no hits.
- `#print axioms` on every named theorem: clean.
- Every module confirmed present and imported by its umbrella.
