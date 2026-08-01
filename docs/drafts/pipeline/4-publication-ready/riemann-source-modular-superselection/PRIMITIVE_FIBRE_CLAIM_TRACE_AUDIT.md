# Primitive-fibre manuscript claim trace

Manuscript: **The Euler primitive--fibre law: A singular source boundary for Riemann's explicit formula**

Audit date: 2026-08-01.

Internal truth-control document. Proof software and formalization are not part of manuscript,
novelty claim, or significance argument.

## Local activation law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Positive valuation atom factors into occupancy and conditional geometric depth | `diagonalActivationPositiveValuationMass_factorization` | `EulerActivationSquarefreeDisintegration.lean` |
| Positive atoms sum to occupancy and total local mass is one | `tsum_diagonalActivationPositiveValuationMass`; `diagonalActivationValuationMass_total` | same |
| Logarithmic occupancy Fisher information is Bernoulli variance | `diagonalActivationOccupancyFisher_eq_variance` | same |
| Prime activation atoms are Möbius--Schur depth differences | `diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference` | same |
| Prime activation atoms are Fisher-damped Gamma valuation coordinates | `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation`; `xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher` | same |
| Diagonal activation is `zeta(s)/zeta(2s)` | `woldActivationHolonomy_diagonal_eq_squarefreePartition` | same |

## Primitive-fibre modular law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| `M_e = d G_e` | `primitiveFibreActivationAtom_eq_fisher_mul_gamma` | `PrimitiveFibreModularRenormalizationLaw.lean` |
| `J_e = P_e G_e` | `primitiveFibreCriticalCurrent_eq_promotion_mul_gamma` | same |
| Direct activation-to-current factorization | `primitiveFibreCriticalCurrent_eq_activationGauge_mul_atom` | same |
| Gamma promotion and direct activation gauge diverge with depth | `tendsto_primitiveFibrePromotionGauge`; `tendsto_primitiveFibreActivationToCurrentGauge` | same |
| Opposite modular tilts are reciprocal | `primitiveFibreModularTilt_mul_reflection` | same |
| Reflected currents have critical current as exact geometric mean | `primitiveFibreModularCurrent_mul_reflection` | same |
| Reflected profiles agree exactly at centered rate zero | `primitiveFibreModularCurrent_eq_reflection_iff` | same |
| Exact sewing quotient and exponential one-way divergence | `primitiveFibreReflectedSewingRatio_eq`; `primitiveFibreReflectedSewingRatio_unbounded` | same |
| Prime activation, Fisher, Gamma, and critical-current specializations | `primitiveFibreActivationAtom_prime`; `primitiveFibreFisherDamping_prime`; `primitiveFibreGammaAtom_prime`; `primitiveFibreCriticalCurrent_prime` | same |
| Bundled law | `primitiveFibreRenormalization_law` | same |
| Prime-power current is `(log p) p^{-k/2}` | `criticalMellinAtomWeight_prime_pow` | `CCMFirstClockPrimePowerTowerCollapse.lean` |

## Global source realizations

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Wold activation holonomy is identity at zero, has translation cocycle, and first jet `-zeta'/zeta` | `woldActivationHolonomy_zero`; `woldActivationHolonomy_cocycle`; `hasDerivAt_woldActivationHolonomy_zero` | `WoldEulerActivationHolonomy.lean` |
| First incidence-normal derivative is exactly von Mangoldt at every integer coordinate | `hasDerivAt_woldIncidenceNormalFactor` | `WoldSieveNormalConeVonMangoldt.lean` |
| Critical Mellin atom has exact Julia--KMS finite telescope | `criticalMellinAtomWeight_eq_juliaKMSInnovationTelescope` | `CCMFirstClockJuliaKMSPrimePowerResolution.lean` |
| Every layer and finite tail is positive on prime powers | `criticalMellinJuliaKMSInnovationLayer_pos`; `criticalMellinJuliaKMSInnovationTail_pos` | same |
| Negative external first-clock phase stays negative on every layer | `criticalMellinJuliaKMSInnovationLayer_mul_neg` | same |
| Normalized positive Euler current is a probability law | `eulerPrimeCurrentTotal_pos`; `tsum_eulerPrimeCurrentProbability`; `eulerPrimeCurrentPMF` | `EulerPrimeCurrentClockLaw.lean` |
| Clock characteristic function equals normalized prime-current response | `charFun_eulerPrimeCurrentClockProbabilityMeasure_eq_response` | same |
| Rescaled logarithmic clock converges weakly to unit exponential law | `tendsto_eulerPrimeCurrentClockProbabilityMeasure` | same |
| Prime Schatten mass is summable exactly for `r sigma > 1` | `summable_primeSchattenMass_iff` | `PrimeSchattenReflectionDuality.lean` |
| Reflected critical exponents are Holder conjugate and equal only at `sigma = 1/2` | `critical_exponents_holder_conjugate`; `critical_exponents_eq_iff_half` | same |
| Reflected prime product is `1/p` and nonsummable | `reflectedPrimeMass_eq`; `reflectedPrimeMass_not_summable` | same |

## Scope audit

- Manuscript does not claim RH, zero exclusion, a one-sided Weil/Ward sign, or a bounded positive
  continuation.
- No-go corollaries are restricted to uniformly bounded, source-label-preserving,
  depth-diagonal multipliers. Arbitrary Hilbert-space equivalence, reindexing, non-diagonal
  operators, singular relations, and zero-dependent constructions are expressly excluded.
- Paper does not claim formalization as novelty or evidence of significance.
- Priority claim is restricted to cross-factorization; classical ingredients are disclaimed and
  external specialist priority review remains required.
