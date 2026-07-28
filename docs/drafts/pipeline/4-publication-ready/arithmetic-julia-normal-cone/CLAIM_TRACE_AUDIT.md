# Claim trace audit

Internal audit for `main.tex`. This file is not part of manuscript.

## Scope rule

Manuscript contains no reference to proof-assistant work. Formal development is used only as
internal claim control. Novelty and significance are assessed entirely from mathematics.

## Main theorem trace

| Manuscript claim | Exact checked declaration(s) | Status |
|---|---|---|
| Dense graph of every finite-trace prime clock, (2.2) | `primeFiniteTraceClock_graphClosure_eq_top` in `ArithmeticLogClockFiniteJetSaturation.lean` | Exact |
| Every nonzero bounded postprocessing remains nonclosable and has no source bound | `primeBoundedPostprocessedTraceClock_pair_mem_graphClosure`, `primeBoundedPostprocessedTraceClock_no_global_source_bound` in `ArithmeticLogClockBoundedCompletionSaturation.lean` | Exact |
| Any packetwise bounded recovery has norms tending to infinity | `tendsto_norm_primeBoundedPostprocessedTraceClock_any_recovery_atTop` in `ArithmeticLogClockBoundedCompletionSaturation.lean` | Exact |
| Gamma-sewn fourth-power law and strict contraction | `gammaSewnMobiusValuationContractionMultiplier_pow_four`, `gammaSewnMobiusValuationContractionMultiplier_lt_one` in `GammaSewnMobiusValuationContraction.lean` | Exact |
| Positive Julia defect, plane isometry, scalar no-go | `gammaSewnMobiusJuliaDefect_pos`, `gammaSewnMobiusJuliaSourceTransportV_normSq`, `gammaSewnMobiusValuationContractionMultiplier_not_scalar_isometry` in `GammaSewnMobiusJuliaSourceTransport.lean` | Exact |
| Unique oriented two-channel lift | `gammaSewnMobiusJuliaSourceTransportV_unique_minimal_positive_lift` in `GammaSewnMobiusJuliaSourceTransport.lean` | Exact |
| Normal coordinate tends to literal `log p` | `tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero` in `GammaSewnMobiusJuliaSourceTransport.lean` | Exact |
| Julia finite-packet clock converges to actual logarithmic clock | `tendsto_gammaSewnMobiusJuliaFiniteTraceClock_nhdsGT_zero` in `ArithmeticJuliaNormalConeUniversalityLaw.lean` | Exact, new bridge |
| Any bounded extension of Julia packet clocks has norms tending to infinity | `tendsto_norm_of_extends_gammaSewnMobiusJuliaFiniteTraceClock` in `ArithmeticJuliaNormalConeUniversalityLaw.lean` | Exact, new bridge |
| Same normal coordinate yields full Mellin orbit `Λ(n)n⁻¹ exp(-u log n)` | `tendsto_gammaSewnMobiusJuliaHardMassCoefficient_nhdsGT_zero`, `gammaSewnMobiusJuliaMellinBoundaryMass_add`, `gammaSewnMobiusJuliaMellinBoundaryMass_neg_one` in `GammaSewnMobiusJuliaSourceTransport.lean` | Exact |
| Euler face is hypertranscendental over coordinate plus every prime-zeta valuation layer | `vonMangoldtUpperEndMero_hypertranscendentalOver_all_valuationLayers` in `ArithmeticJuliaNormalConeUniversalityLaw.lean`, instantiating `analyticPrimeProfileCarrier_hypertranscendentalOver_all_valuationLayers` | Exact, new application |
| Critical Julia coefficient tends to `Λ(n)/sqrt(n)` | `tendsto_gammaSewnMobiusJuliaCriticalHardCoefficient_nhdsGT_zero` in `GammaSewnJuliaRectangularDivisorTransgression.lean` | Exact |
| Finite critical scalarization tends to entire finite rectangular prime source | `tendsto_gammaSewnMobiusJuliaCriticalPrimeAutocorrelation_nhdsGT_zero` | Exact |
| Gamma-polar completion tends to exact Xi-Weil observable | `tendsto_gammaSewnMobiusJuliaCriticalCompletedSource_nhdsGT_zero` | Exact |
| Every tail coefficient tends to prime-Gamma divisor coefficient | `tendsto_gammaSewnMobiusJuliaCriticalCompletedTailCoefficient_nhdsGT_zero` | Exact |
| Continuation is meromorphic on `Re s > 1`; poles are exactly shifted strict-right zeros | `gammaSewnMobiusJuliaCriticalCompletedTail_divisorComplete`, using `meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff` | Exact |
| Normalized residues recover analytic multiplicity | `normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity` | Exact |
| Holomorphy on `Re s > 1` iff RH | `riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne` | Exact |
| Ward pair response is two Lorentzians | `re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq` in `XiWardEdgeMassQuantization.lean` | Exact |
| Phase defect derivative is twice real Ward response | `hasDerivAt_xiWardBoundaryPhaseDefect_zero` in `XiWardInfinitesimalDefectIndexQuantization.lean` | Exact |
| Every strict-right upper pair has `8π` defect mass | `lintegral_infinitesimalDefect_xiAntiCausalWardSchwarzPairResponse_eulerEdge` | Exact |
| Total defect index is sum of `8π` packets | `lintegral_xiWardInfinitesimalDefectDensity` | Exact |
| Index vanishes iff RH | `riemannHypothesis_iff_lintegral_re_continuedXiAntiCausalWardResponse_eq_zero` plus factor-two defect identity | Exact |
| Integrated master conjunction | `arithmeticJuliaNormalConeUniversality` in `ArithmeticJuliaNormalConeUniversalityLaw.lean` | Exact |

## Axiom audit

Checked with `#print axioms`:

- `RHTower.arithmeticJuliaNormalConeUniversality`
- `RHTower.vonMangoldtUpperEndMero_hypertranscendentalOver_all_valuationLayers`
- `RHTower.tendsto_norm_of_extends_gammaSewnMobiusJuliaFiniteTraceClock`

Each depends only on:

- `propext`
- `Classical.choice`
- `Quot.sound`

No project axiom, hypothesis about zeros, computation, numerical certificate, `sorry`, `admit`,
or unsafe declaration enters theorem.

## Scope exclusions enforced in manuscript

- No claim that RH is proved.
- No claim that defect index has finite upper bound.
- No inference from `8π` quantization to zero exclusion.
- No claim that global completion is rank one; minimality is one extra channel per prime cell.
- No claim that critical face is hypertranscendental over unshifted valuation-layer field.
- No target divisor, Xi zero, or Ward response is used in source construction before explicit
  formula.
- No use of formalization as novelty or significance.

## Text checks

- `main.tex` contains no occurrence of `Lean`, `formalization`, `proof assistant`, or `computer`.
- No TODO, placeholder, conjectural lemma, or assumed estimate.
- The title says “complete off-critical Riemann divisor,” matching exact result.
