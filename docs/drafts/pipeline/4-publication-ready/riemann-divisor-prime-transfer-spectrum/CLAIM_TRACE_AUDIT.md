# Claim trace audit

Internal verification record for `main.tex`. This file is not part of manuscript and may mention
formal verification. Novelty or significance claims do not rely on formalization.

## Policy

- Manuscript may state only unconditional mathematics represented by checked declarations below.
- RH appears only as standard consequence/equivalence; manuscript does not claim zero exclusion.
- Interpretive sentences are narrowed to this exponent-shell resolution.
- Literature priority is supported by `LITERATURE_AUDIT.md`, not asserted as exhaustive proof.

## Main theorem trace

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Shell coefficients are 0/1 and identify largest-exponent shells | `shellIndicator_eq_one_iff`, `shellIndicator_eq_zero_or_one` | `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean` |
| Pairwise coefficient orthogonality | `shellIndicator_mul_eq_zero_of_ne` | `formal/GaloisForLFunctions/RHTower/HighExponentShellOrthogonalDivisorReplication.lean` |
| Exact positive fusion | `sum_range_completeResolutionIndicator`, `tsum_completeResolutionIndicator` (specialize complete resolution at the shell boundary) | `formal/GaloisForLFunctions/RHTower/CompletePositiveKolchinFreeRiemannResolution.lean` |
| Shell factorization \(S_m=\zeta H_m\) | `LSeries_completeResolutionIndicator`; `shellMultiplier` definition | `formal/GaloisForLFunctions/RHTower/CompletePositiveKolchinFreeRiemannResolution.lean`; `HighExponentShellZeroFree.lean` |
| \(H_m\ne0\) on \(\Re s>1/2\), \(m\ge12\) | `shellMultiplier_ne_zero` | `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean` |
| Exact divisor replication with multiplicity | `analyticOrderAt_completedRiemannZeta_mul_shellMultiplier` | same |
| Joint differential independence over full zeta differential field | `relativeShellMultiplierUpperEndCarrier_differentialIndependent_two` | `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean` |
| Unit label codiagonal not closable on \(\ell^2\) | `norm_sq_shellLabelEmbedding_averagingPacket`, `shellCodiagonal_not_closable` | `formal/GaloisForLFunctions/RHTower/HighExponentShellOrthogonalDivisorReplication.lean` |
| \(2^{ms}H_m(s)\to1-2^{-s}\) | `tendsto_two_cpow_nat_mul_shellMultiplier` | `formal/GaloisForLFunctions/RHTower/HighExponentShellLeastAtomAsymptotic.lean` |
| \(H_{m+1}/H_m\to2^{-s}\) | `tendsto_shellAdjacentTransfer` | same |
| Actual source-mass normalization tends to \(2^{1/2-s}\) | `tendsto_shellSourceMass_div_succ`, `tendsto_sourceNormalizedShellAdjacentTransfer` | same |
| Prime-three residual asymptotic | `tendsto_three_cpow_nat_mul_shellSecondAtomResidual` | `formal/GaloisForLFunctions/RHTower/HighExponentShellPrimeSpectrum.lean` |
| Residual adjacent transfer and half-density normalization | `tendsto_shellSecondAtomAdjacentTransfer`, `tendsto_normalizedShellSecondAtomAdjacentTransfer` | same |
| Concrete \((2,3)\) transfer spectrum is globally injective | `twoPrimeShellTransferSpectrum_injective` | same |
| Exact minimal tomography rank: one scale is noninjective; two scales are injective iff log ratio is irrational | `leastAtomTransferCharacter_not_injective`, `leastAtomTwoScaleSpectrum_injective_iff_irrational` | `formal/GaloisForLFunctions/HTGeometry/LeastAtomModularTransferLaw.lean` |
| Universal modulus/reflection/phase trichotomy | `norm_leastAtomTransferCharacter`, `leastAtomTransferCharacter_reflection_pair`, `leastAtomTransferCharacter_phase_trichotomy` | same |
| Base-independent entropy \(c/2-\Re s\) | `leastAtomTransferEntropy_eq`, `leastAtomTransferEntropy_base_independent` | same |
| Xi current residue \(-d(\rho-1/2)\) | `xiExceptionalAffineDivisorCurrent_residue` | `formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean` |
| Local residue equals cofinal atom entropy for every \(q>1\) | `re_centeredXiAffineResidue_eq_leastAtomTransferEntropy`, `tendsto_re_xiExceptionalAffineDivisorCurrent_eq_atomEntropy` | `formal/GaloisForLFunctions/RHTower/XiHypertranscendentalModularResidueTransgression.lean` |
| Charge vanishes iff critical line at nonzero order | `centeredXiModularCharge_eq_zero_iff` | same |
| Two-clock characteristic energy limit | `tendsto_twoClockResidueEnergy_characteristic` | `formal/GaloisForLFunctions/RHTower/HighExponentShellLeastAtomAsymptotic.lean` |
| Characteristic limit strictly positive for nonzero amplitude | `twoClockCharacteristicLimit_pos` | same |
| Full independent quadrant bounded iff rate is zero | `conjugateTwoClockQuadrantBounded_iff` | same |
| Complete localization certificate | `hypertranscendentalDivisorInformationLocalization_law` | `formal/GaloisForLFunctions/RHTower/HypertranscendentalDivisorInformationLocalizationLaw.lean` |

## Claims deliberately excluded

- RH proof or disproof.
- Any theorem excluding a Xi zero.
- A source-derived bound on off-line defect index.
- Novelty for Möbius inversion, \(k\)-free Euler products, logarithmic residues, individual
  hypertranscendence, same-zero Euler modifications, or “critical line = unitary locus.”
- A no-go theorem for Hilbert–Pólya, Connes–Consani, trace-formula, or weighted operator routes.
- Any implication from reflection reciprocity to pointwise unitarity.
- Any claim that a finite characteristic profile detects the critical line.

## Manuscript language audit

- No occurrence of “Lean,” “formalization,” “machine checked,” or equivalent novelty language.
- “New” applies only to conjunction/package identified in literature audit, successive shell
  atom transfer theorem, local–cofinal transgression, and information-localization theorem.
- Route claims are explicitly restricted to this resolution.
- Paper includes no open-problems section and ends with exact proved distinctions.
