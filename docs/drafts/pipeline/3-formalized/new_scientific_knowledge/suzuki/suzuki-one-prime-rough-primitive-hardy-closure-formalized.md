# One-prime rough-primitive Hardy closure, formalized

- **ID:** `suzuki-one-prime-rough-primitive-hardy-closure`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-one-prime-rough-primitive-hardy-closure.md`
- **Lean (built for this card):**
  - `formal/GaloisForLFunctions/HTGeometry/PolynomialTransportRemainder.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PolynomialGroupOneBlock.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ThirdAmplitudeRayDecay.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeOneBlockEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeChartClosure.lean`
- **Lean (already in the corpus for this card):**
  - `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeRoughPrimitiveHardyTail.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeFractionalCarrier.lean`
- **Lean (inherited from the stage-3 input cards):**
  - `formal/GaloisForLFunctions/HTGeometry/InverseFamilyDerivative.lean`,
    `InverseFamilyThirdDerivative.lean`, `PhaseGeneratorIntegrationByParts.lean`,
    `PhaseGeneratorThirdIntegrationByParts.lean`
  - `formal/GaloisForLFunctions/HTGeometry/DyadicLatticeCover.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GraphFluxStabilityEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPrimitiveFluxNonnormalGraphReduction.lean`,
    `SuzukiGammaShiftKappa.lean`

## Formal content

| Card | Lean |
|---|---|
| `(5)` the fractional valuation weight `w(n) = (1+\|n\|)^{-2/3}` | `fractionalPolynomialOrbitWeight`, `summable_fractionalPolynomialOrbitWeight_twoThirds_sq` |
| `(6)` the concrete parameters `(κ,σ,p) = (2/3, 3/4, 5/4)` | `onePrimeCarrier_window`, `suzukiOnePrimeThirdIBPTails` |
| the weighted prime group is a two-sided polynomial group | `fractionalPolynomialOrbitShift_add`, `fractionalPolynomialOrbitShiftRatio_cocycle`, `abs_fractionalPolynomialOrbitShiftRatio_le`, `tsum_sq_fractionalPolynomialOrbitWeightedShift_le` |
| `(11)` the backward block primitive stays in the block class | `suzukiBackwardGeometricBlockEnvelope`, `tsum_suzukiBackwardGeometricBlockEnvelope_le`, `tsum_suzukiBackwardGeometricBlockEnvelope_lt_top` |
| the three-fold frequency expansion itself | `phase_ibp_third_step_of_continuousOn`, `phase_ibp_thrice_of_continuousOn` |
| the amplitude surviving three integrations by parts is `O(t^{-3})` | `norm_invFamilyProduct2Deriv_le`, `norm_invFamilyProduct2Deriv_le_rpow_neg_three` |
| `(14)`, `(15)` the transported lower endpoint has majorant `x^{κ-p}` | `norm_transport_lowerEndpoint_le` |
| `(16)`--`(18)` the third remainder splits at `x/2` | `polynomialTransportIntegrand`, `integral_polynomialTransportIntegrand_le`, `integral_rpow_neg_threeHalves_le` |
| `(14)`--`(18)` the transported third remainder, operator-valued | `norm_transport_remainder_le` |
| `(19)` the far-tail test `κ < σ` | `integrableAtTop_suzukiPolynomialIBPFarTailNormSq_iff` |
| `(20)` the depth test `κ + 3/2 < N` | `integrableAtTop_suzukiPolynomialIBPNearTailNormSq_iff`, `integrableAtTop_suzukiPolynomialIBPTails_iff` |
| the two-power majorant is square integrable exactly in that window | `polynomialBlockMajorant`, `integrableOn_sq_polynomialBlockMajorant`, `lintegral_sq_ofReal_polynomialBlockMajorant_ne_top` |
| `(21)` the operator-valued polynomial-group one-block estimate | `lintegral_sq_polynomialTransportProfile_ne_top` |
| `(21)` at the concrete rank-one carrier | `lintegral_sq_onePrimeBlockProfile_ne_top`, `lintegral_sq_onePrimeBlockProfile_ne_top_of_tails` |
| `(22)`, `(23)` the complementary fluxes sum to the uncut flux | `primitiveFlux_eq_cut_flux`, `primitiveFlux_cutoffComplement_sum` |
| `(24)` coercivity applied after the rough primitives cancel | `norm_le_of_coercive`, `neg_suzukiGammaShiftKappa_le_integral`, `norm_le_of_complementaryFlux_coercive` |
| `(1)`, §6 the dyadic charts cover the aperture | `Ioo_subset_endpointWindow_of_invisible_two`, `dyadicCenter_spacing`, `exists_finset_dyadicWindow_cover` |
| `(3)` finite energy on the whole aperture from finitely many charts | `lintegral_ne_top_of_finset_cover`, `lintegral_energy_ne_top_of_chart_cover` |

## Notes

**What the gate asked for.**  The card's own `2 → 3` gate named exactly one missing Lean object,
"formalize operator-valued polynomial-group one-block estimate", and its Lean-certificate section
said the next target was that estimate "rather than a theorem restating the desired conclusion".
`lintegral_sq_polynomialTransportProfile_ne_top` is that estimate, stated for an arbitrary
operator-valued transport family `Φ` on a Banach space over `ℂ`.

**Its hypotheses are exactly the card's inputs.**  `htrans` is `(14)`, the transport bound the card
imports from the Gamma dimension theorem (slow exponent `p = 1/2 + σ`) together with the polynomial
group (degree `κ`).  `hr` is the cubic decay of the amplitude left by three integrations by parts —
supplied by the corpus's own amplitude tower through
`norm_invFamilyProduct2Deriv_le_rpow_neg_three`, which is the general `O(w³)` bound read at the ray
scale `w = 1/t`.  `hB` is the Plancherel boundary term at `t = x`, where the transport cancels
because `H(x)H(x)⁻¹ = I`.  `hf` is the shape the three-fold expansion
`phase_ibp_thrice_of_continuousOn` produces: propagated lower endpoint, boundary term, transported
remainder.

**Why three integrations by parts and no more.**  The proof consumes exactly the two tests the card
isolates.  The far half of `(16)` needs `p < 3/2`, which is `σ < 1`; it produces `x^{κ-p}`, square
integrable iff `κ < σ`.  The near half produces `x^{κ-2}`, square integrable iff `κ < 3/2`, which at
depth `N = 3` is `κ + 3/2 < N`.  For `(κ,σ) = (2/3, 3/4)` both are strict, which is
`onePrimeCarrier_window`.

**`(10)` is an unused ingredient.**  The card derives the continuous weighted Hardy bound `(10)` and
then immediately replaces it by the sharper block statement `(11)`, which is what `(12)` uses.  The
Lean route goes through `(11)` (`tsum_suzukiBackwardGeometricBlockEnvelope_le`), so `(10)` is
recorded here rather than formalized.

**`(3)` at the corpus's level of abstraction.**  As with the other trace-zero cards of this folder,
"`u ∈ H¹`" is rendered as finiteness of the weighted energy of the profile and of its derivative;
`lintegral_energy_ne_top_of_chart_cover` is the local-to-global step, taking the finitely many charts
of `exists_finset_dyadicWindow_cover` to the whole aperture.  Construction of Suzuki's concrete
restricted-Weil operator and the vector-valued Fourier/Bochner composition remain, as the card
states, items of the later gates.

All listed declarations audit to `[propext, Classical.choice, Quot.sound]`.
