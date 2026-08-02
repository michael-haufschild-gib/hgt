# Claim trace audit

Internal verification record. Not part of manuscript; formalization contributes no novelty.

## Current manuscript

| Manuscript claim | Unconditional checked declaration |
|---|---|
| Complete source coordinates have exact head-plus-tail norm and converge to the universal point section | `norm_completeResolutionSourceVector_sub_pointSection`; `tendsto_completeResolutionSourceVector_pointSection` in `RHTower/CompleteResolutionCofinalConditioningLaw.lean` |
| Finite source embeddings are injective; distinct source points have positive finite-stage separation, cofinal separation tends to zero, and reciprocal conditioning diverges | `completeResolutionSourceEmbedding_injective`; `norm_completeResolutionSourceVector_sub_pos`; `tendsto_norm_completeResolutionSourceVector_sub_zero`; `tendsto_inv_norm_completeResolutionSourceVector_sub_atTop` |
| Uniformly Lipschitz cofinal observers lose every fixed spectral separation | `tendsto_uniformLipschitz_completeResolutionObserver_separation_zero`; `no_uniformLipschitz_completeResolutionObserver_fixedSeparation` |
| Complete channels have disjoint positive \(0/1\) supports, sum to one, and carry the zeta divisor | `completeResolutionIndicator_eq_zero_or_one`; `tsum_completeResolutionIndicator`; `completeResolutionIndicator_pairwiseDisjoint` in `CompletePositiveKolchinFreeRiemannResolution.lean`; `summable_completeResolutionMultiplier`; `hasSum_completeResolutionMultiplier_one` in `CompleteResolutionSummableLanding.lean`; `analyticOrderAt_riemannZeta_completeResolutionChannel` in `CompleteResolutionSummableConormalLanding.lean` |
| Exact finite Möbius peeling at every prime \(q\) gives \(q^{ns}R_q(ns)\to-1\) | `norm_prime_cpow_mul_invZetaPrimePeeledResidual_add_one_le`; `tendsto_prime_cpow_nat_mul_invZetaPrimePeeledResidual` |
| Peeled-shell adjacent transfer converges to \(q^{-s}\), and normalized transfer to \(q^{1/2-s}\) | `tendsto_prime_cpow_nat_mul_primePeeledShellResidual`; `tendsto_primePeeledShellAdjacentTransfer`; `tendsto_normalizedPrimePeeledShellAdjacentTransfer` |
| Prime-normal character agrees with the least-atom projective recurrence character | `primePeeledShellTransferCharacter_eq_leastAtom` |
| Arbitrary distinct finite prime packets have nonsingular Vandermonde matrix and span every finite target | `finitePrimeNormalSpectrum_sampleMatrix_det_ne_zero`; `finitePrimeNormalSpectrum_samplePoint_span` |
| Countable prime-normal reader is defined on the actual complete-source image and returns the exact packet | `completeResolutionCountablePrimeNormalReader`; `completeResolutionCountablePrimeNormalReader_imagePoint`; `completeResolutionCountablePrimeReader_samplePoint` |
| Generic cofinal rank transmutation sends every retained output span into the multivalued fibre | `closedLinearRelation_mem_vertical_of_tendsto_zero`; `closedLinearRelation_span_le_verticalFiber_of_cofinalCollapse` |
| Subtracting an arbitrary proposed horizon value does not reduce finite prime-normal rank | `completeResolutionAffinePrimeNode_injective`; `completeResolutionCountablePrimeOutput_affine_span` |
| Every leading finite projection of the affine-centred multivalued fibre is surjective | `completeResolution_closedLinearRelation_countablePrime_affine_projectivelyFull` |
| Product-topology closedness upgrades finite surjectivity to \(\operatorname{mul}\mathcal R=\mathbb C^\mathbb N\) | `completeResolution_closedLinearRelation_countablePrime_affine_fullVertical` |
| Full verticality forces \(\mathcal R=\operatorname{dom}\mathcal R\times\mathbb C^\mathbb N\) | `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod` |

## Verification

Foreground check:

```text
lake env lean GaloisForLFunctions/RHTower/CompleteResolutionCofinalConditioningLaw.lean
```

Result: success, no warnings.

Axiom audit for all new prime-peeling, Vandermonde, affine-centre, projective-surjectivity,
full-verticality, and domain-product theorems reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project axiom, `sorry`, `admit`, `opaque`, or unsafe declaration occurs in the
checked chain.

Final module build remains reserved for manuscript freeze, per project build discipline.

## PDF audit

- Current preview: `output/pdf/rank-transmutation-riemann-source-horizon.pdf`
- 11 A4 pages.
- Tectonic build: success.
- No overfull/underfull boxes, undefined references, duplicate labels, or TeX warnings.
- All pages rendered to PNG and visually inspected; full-size checks included title page,
  maximal-boundary proof, recurrence comparison table, conclusion, and references.
- Manuscript contains no mention of formalization.
