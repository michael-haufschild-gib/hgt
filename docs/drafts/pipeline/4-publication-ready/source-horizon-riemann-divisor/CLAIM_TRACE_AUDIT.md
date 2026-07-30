# Claim trace audit

Internal verification record. This file is not part of manuscript and must not be cited as novelty.

## Universal generator law

| Manuscript claim | Checked theorem |
|---|---|
| Factorially normalized coherent jets form exact Poisson packet | `coherentExponentialJet_poisson_conservation` in `formal/GaloisForLFunctions/HTGeometry/CayleyFockOrderSpaceConservation.lean` |
| Poisson drift normalization uniquely forces \(x=\tau/|b|^2\) | `coherentGenerator_observationTime_unique` |
| Forced clock sends \(b\) to \(\overline{b^{-1}}\) | `coherentGenerator_duality` |
| Canonical packet rate is \(2\operatorname{Re}(b^{-1})+1\) | `coherentGenerator_exponent_observationTime`, `coherentGenerator_poisson_conservation` |
| Fock growth factors as drift times dual rate | `cayleyFockExponent_eq_drift_mul_dualRate` |
| Neutral reciprocal line equals shifted-generator unit circle | `coherentGeneratorDualRate_eq_zero_iff_shift_norm_one` |

## Meromorphic source specialization

| Manuscript claim | Checked theorem |
|---|---|
| Residue transport before extraction gives \(m e^{x/(\rho-c)}\) | `cayleyPoleEvolvedResponse_residue_transport` in `formal/GaloisForLFunctions/HTGeometry/CayleyPoleResidueTransport.lean` |
| Source clock is the universal generator clock | `sourceCayleyObservationTime_eq_coherentGeneratorTime` |
| Source clock converts reciprocal displacement to conjugate displacement | `sourceCayley_inverse_observationTime`, `cayleyPoleResidueMode_observationTime_eq` |
| Source rate is \(2\operatorname{Re}(\rho-c)+1\), with stated horizon and sign | `coherentGeneratorDualRate_sourceCayley`, `sourceCayleyTransverseRate_eq_zero_iff`, `sourceCayleyTransverseRate_pos_iff` |
| Exact source-horizon Poisson channel law | `sourceCayleyResidueMode_horizon_conservation` |
| Height cancels in vertical parabolic family | `parabolicCayleyResidueMode_renormalization` |

## Finite-carrier localization

| Manuscript claim | Checked theorem |
|---|---|
| Finite transported divisor is differentially algebraic | `finiteCayleyResidueCarrier_differentiallyAlgebraic` in `formal/GaloisForLFunctions/HTGeometry/CayleyPoleResidueTransport.lean` |
| Explicit characteristic polynomial annihilates finite carrier | `expSumAnnihilator_ode` in `formal/GaloisForLFunctions/HTGeometry/ExponentialSumDA.lean`; specialized as `finiteCayleyResidueCarrier_ode` |
| Distinct finite source frequencies cannot have all first \(N\) jets vanish | `finiteCayleyResidueCarrier_jetFaithful`, based on `phaseJet_exists_ne_zero` |

## Riemann specialization

| Manuscript claim | Checked theorem |
|---|---|
| Actual completed prime–Gamma logarithmic response has stated arithmetic decomposition | `xiCayleyEvolvedLogDeriv_eq_arithmetic` in `formal/GaloisForLFunctions/RHTower/XiSourceCayleyOrderSpaceConservationLaw.lean` |
| Actual \(\xi\)-zero residue is transported with no simplicity assumption | `xiCayleyEvolvedLogDeriv_residue_transport` |
| Source mode is Poisson completion of inverse Li orbit | `xiCayleySourceResidueMode_eq_poissonCompletedLiOrbit` |
| Drift and exponent reconstruct real part and squared height | `xiSourceCayley_rho_re_reconstruction`, `xiSourceCayley_rho_im_sq_reconstruction` |
| Strict-right zero has positive source exponent | `xiSourceCayleyExponent_pos` |
| Riemann canonical-time packet is height-independent | `xiCayleySourceResidueMode_parabolic_conservation` |
| Packaged Riemann source law | `xiSourceCayleyOrderSpaceConservation_law` |

## Escape collision

| Manuscript claim | Checked theorem |
|---|---|
| Polynomial quartet perturbations are entire, symmetric, off-line, and hypertranscendental | `escapingQuartetGaugedXi_hypertranscendental`, `escapingQuartetGaugedXi_analyticAt`, `escapingQuartetGaugedXi_one_sub`, `escapingQuartetGaugedXi_conj`, `escapingQuartetGaugedXi_added_zero`, `escapingQuartetGaugedXi_added_zero_off_critical` in `formal/GaloisForLFunctions/RHTower/CompactOpenKolchinWardChargeEscape.lean` |
| Every holomorphic jet converges compact-open to \(\xi\) | `escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly` |
| Rational differential matroid is unchanged, including all scalar valuation layers | `escapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw`, `escapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw`, and multiplicity analogues |
| Ward density vanishes uniformly on bounded windows | `escapingQuartetWard_window_tendstoUniformly`, `multiplicityEscapingQuartetWard_window_tendstoUniformly` |
| Total Ward mass is \(8\pi\), or \(8\pi N\) with multiplicity | `escapingQuartetWard_mass`, `multiplicityEscapingQuartetWardMass_eq` |
| Added divisor remains a simple logarithmic pole | `escapingQuartetGaugedXi_logDeriv_addedZero_simplePole`, `multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole` |
| Packaged bounded and unbounded escape laws | `compactOpenKolchinWardChargeEscape_law`, `unboundedCompactOpenKolchinWardChargeEscape_law` |

## Capstone and audit status

- Combined endpoint: `sourceHorizonEscapeConservation_law` in `formal/GaloisForLFunctions/RHTower/SourceHorizonEscapeConservationLaw.lean`.
- Direct checks: all modified modules pass `lake env lean <file>`.
- Final module build: recorded separately after manuscript freeze.
- Axiom audit: capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no project axioms.
- Repository lint: new modules are reachable from theorem-area umbrellas. Full lint remains nonzero only because unrelated pre-existing modules are still unreachable; no forbidden declaration was reported in this work.

