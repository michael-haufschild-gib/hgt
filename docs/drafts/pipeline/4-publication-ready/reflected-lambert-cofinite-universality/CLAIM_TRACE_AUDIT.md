# Internal claim trace audit

This file is not part of manuscript. It records machine-checked support for every
headline mathematical claim. Manuscript itself neither mentions nor claims novelty from
formal verification.

## Claim map

| Manuscript claim | Supporting declaration | Module |
|---|---|---|
| Sector-Blaschke completeness definition | `SectorBlaschkeComplete` | `FrequencySectorBlaschkeCompleteness.lean` |
| Carrier-independent strong condition | `StrongSectorBlaschkeComplete` | same |
| Exact Cayley defect \(2/((\lambda-R)^n+1)\) | `one_sub_norm_frequencyCayley` | same |
| Blaschke divergence forbids nonzero bounded analytic zero function | `not_bounded_analytic_zero_on_all_frequencyCayley` | same |
| Translated frequency zeros force ray vanishing | `frequency_zero_uniqueness_on_ray` | same |
| Arbitrary finite deletion preserves strong completeness | `strongSectorBlaschkeComplete_compl_finset` | same |
| Prime logs injective | `primeLog_injective` | same |
| Cofinite prime logs strongly complete | `cofinitePrimeLog_strongSectorBlaschkeComplete'` | same |
| Lambert annihilation implies Fourier–Borel vanishing, one sector order | `compactFourierBorel_eq_zero_of_frequencyTangent_annihilation` | `CompactCarrierFrequencyCompleteness.lean` |
| Carrier-independent Fourier–Borel recovery | `compactFourierBorel_eq_zero_of_strongFrequencyTangent_annihilation` | same |
| Coordinate monomials in closed tangent span | `coordinate_pow_mem_closedSpan_frequencyLambertTangents` | same |
| Reflected monomials in closed reflected span | `fe_odd_coordinate_pow_mem_closedSpan_frequencyLambert` | same |
| Reflected polynomials in closed reflected span | `fe_odd_polynomial_mem_closedSpan_frequencyLambert` | same |
| Analytic FE-odd critical-disc density | `criticalDisc_analytic_odd_mem_closedSpan_frequencyLambert` | `CriticalDiscReflectedLambertUniversality.lean` |
| Schwarz-real descent and real-span density | `criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_frequencyLambert` | same |
| Local flux derivative is derivative-Lambert tangent | `hasDerivAt_criticalDiscFrequencyUnitFEIncrement_zero` | same |
| Real increments preserve Schwarz structure | `criticalSchwarzTransform_realFrequencyUnitFEIncrement` | same |
| Safe Neumann parameter neighbourhood exists | `exists_real_parameter_ball_norm_one_add_smul_lt_one` | same |
| Every real tangent multiple lies in safe increment-group closure | `real_smul_frequencyTangent_mem_safeIncrementGroup_closure` | same |
| Real tangent span lies in safe group closure | `realSpan_frequencyTangents_le_safeIncrementGroup_closure` | same |
| Pole-free nonlinear universal orbit law | `criticalDisc_analytic_odd_schwarz_mem_safeFrequencyIncrementGroup_closure` | same |
| One-point continuous Hausdorff quotient | `criticalDisc_continuous_safeFrequencyIncrementInvariant_eq_base` | same |
| Odd-to-even normalized division exact inverse | `normalizedTraceMomentGerm_criticalTraceToCenteredOdd_evenMomentToCriticalTrace` | `CriticalTraceMomentGerm.lean` |
| Every even Schwarz germ has exact trace in safe orbit closure | `evenMomentGerm_frequencyOrbitClosure_and_normalizedTrace` | `ReflectedLambertRHBarrier.lean` |
| Cofinite prime-log specialization | `evenMomentGerm_cofinitePrimeLogOrbitClosure_and_normalizedTrace` | same |
| Remote even perturbation sets selected coefficient to \(-1\) | `analyticTraceMoments_remoteEvenPerturbation` | `TraceHankelAnalyticInstability.lean` |
| Remote perturbation fails finite monomial-square test | `remoteEvenPerturbation_not_traceHankel` | same |
| Remote perturbations converge uniformly on smaller disc | `eventually_remoteEvenPerturbation_uniformly_close` | same |
| Close Hankel failure with trace in safe orbit closure | `exists_close_frequencyOrbit_normalizedTraceHankel_failure` | `ReflectedLambertRHBarrier.lean` |
| No continuous safe-increment invariant Hankel classifier | `no_continuous_frequencyInvariant_traceHankel_classifier` | same |
| Source trace equals Xi logarithmic derivative on continued domain | `continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain` | `GammaSewnMobiusXiWardJuliaTransport.lean` |
| Normalized source germ equals reciprocal-square moment germ locally | `normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm` | `PrimeArchCentralMomentGerm.lean` |
| Every source Taylor moment equals centered reciprocal moment | `analyticTraceMoments_normalizedPrimeArchSource` | same |
| Xi and source Hankel values exactly agree | `xiCentralTraceHankel_eq_primeArchSourceTraceHankel` | same |
| Real-polynomial trace-Hankel positivity iff RH | `xiCentralTraceHankelNonnegative_iff_riemannHypothesis` | `XiTraceHankelCriterion.lean` |
| Integer-polynomial tests suffice | `xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis` | `XiTraceHankelCountableCriterion.lean` |
| Prime–arch source integer Hankel positivity iff RH | `primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis` | `PrimeArchThetaAllOrderCumulant.lean` |
| Capstone source endpoint | `reflectedLambert_sourceHankel_iff_RH` | `ReflectedLambertRHBarrier.lean` |

## Scope alignment

- Manuscript uses safe/pole-free increment group, not larger algebraically totalized
  inverse group.
- Repeated generators are described as powers/products of local modifications, never
  as one raw degree-one factor.
- Density is claimed only in analytic FE-odd Schwarz-real fibre, uniformly on a
  smaller closed disc.
- One-point quotient is claimed only for continuous Hausdorff-valued invariants on
  that fibre.
- Strong sector condition is presented as carrier-independent sufficient condition,
  not necessary condition.
- Hankel criterion is explicitly prior art; novelty lies in orbit collision and
  trilemma.
- Paper does not claim RH or general impossibility of Hilbert–Pólya/CCM.

## Verification record

Final audit commands and outputs are added after lint, axiom, and module-build gates.

