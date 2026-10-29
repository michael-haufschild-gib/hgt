# Mathematical facts supporting the RH frontier

## Complete atomic forms

- `TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_certified`: for each fixed real δ with `0 ≤ δ < certifiedOverlapIncrement`, the complete matrix of `transMetzlerProfile` at ratio `1 + δ` is eventually positive definite. This is a fixed-ratio theorem; its horizon may depend on δ. Source: `TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean:149`.
- `SpacingScaleHarmonicAnalysis.atomicFamilies_negative_iff`: for `|lam n| ≤ Λ(n)`, a normalized compactly supported C² profile and `OverlapGrowth κ`, infinitely recurring negative atomic tests are equivalent to failure of `WeilPositiveFull lam`. The growth and profile hypotheses belong to the statement. Source: `SpacingScaleHarmonicAnalysis/TheGaugeBecomesVisibleAtTheCriticalExponent.lean:365`.
- `eventually_completeWeil_eigenvalues_ge_uniformly_at_touching`: for a fixed C² unit-interval profile of positive L² mass, every `b < bumpRobin φ 1 / ∫φ² + completeWeilPoleShift φ 1 - log(2π)` is an eventual lower bound for every eigenvalue, simultaneously for every `0<c≤1`. Source: `CriticalArithmeticCorrelationTheory/OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching.lean:66`.
- `exists_finite_ramanujan_approximation_uniformly_at_touching`: one finite conductor family approximates every unit vector of complete energy at most T, uniformly over all `0<c≤1` and sufficiently large N. The family depends on profile, T and approximation error. Source: `CriticalArithmeticCorrelationTheory/OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching.lean:43`.
- `eventually_affineRamanujanPrimeWindow_uniform`: at fixed positive conductor q and fixed natural window endpoints `0<A≤B`, the actual Λ(k)/k-weighted affine Ramanujan window converges uniformly over **all** natural n,h. Thus n and h may depend arbitrarily on N. Source: `CriticalArithmeticCorrelationTheory/ActualAffinePrimeWindowsAreUniformInTheirParameters.lean:32`.
- `eventually_primeWindow_all_complex_Gram_packets`: at fixed q,A,B, one horizon controls every finite complex packet and all its coefficients; error is at most ε times the packet's squared norm over all residue classes. Source: `CriticalArithmeticCorrelationTheory/PrimeResidueWindowsControlEveryGramPacket.lean:143`.
- `primitivePrefixGram_quadratic_nonneg`: the primitive-root prefix kernel is positive semidefinite for every finite family of prefix lengths and real coefficients, at every positive conductor. Source: `CriticalArithmeticCorrelationTheory/TheArithmeticCurvatureHasAnExactGramCompletion.lean:108`.
- `tendsto_plateauSuccessorFiber_div_log`: the normalized successor divisor fiber divided by log(N+1) tends to `bumpCorr transMetzlerProfile (1/c) / ∫transMetzlerProfile²` at every fixed c>0. Source: `TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean:140`.
- `ramanujanPoleProfile_dyadic_twoSided_frame`: at `Q≥2` and `A≥4Q(Q−1)`, squared packet mass on `(A,2A]` lies between 1/4 and 5/4 of squared coefficient mass. The literal prime kernel vanishes on that annulus (`weilPrimeKernel_eq_zero_on_dyadic_annulus`). Source: `CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean:93,121`.

## Height-dependent locality

- `exists_prime_certifies_height`: among any set of more than `choose(heightIndex T,2)` primes, some prime tower has a compact C² generator and finite translate set whose Weil Gram negative index is at least `heightIndex T`. The generator and translate set are existential. Source: `EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean:320`.
- `twoPrime_tower_certifies_height`: for T≥0, a tower of step `|log(3^k/2^j)|` carries at least `heightIndex T` negative squares, for some `0<k≤floor(T log 2/π)+1` and `k≤j≤2k`. Source: `EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean:265`.

## Critical-line census

- `simple_critical_proportion_ge_67250071`: for every ε>0, eventually `(67250071/100000000−ε) Ncount(0,T) ≤ N0simple(0,T)`.
- `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio`: the lower limiting simple-critical proportion is at least `HD(1)+10⁻⁸`. Both statements: `IncommensurableGaborPinching/CriticalLineZeroProportion.lean:1042,1076`.

## Actual theta-clock history

- `liEvenCrossActualClockHistory_first_zero_budget_iff_pos`: the inequality `Cout(t) ≤ V(t)` at every `t > 20` with `D(t)=0` and nonnegative preceding history is equivalent to `D(t)>0` for every `t>0`. Source: `RHTower/LiEvenCrossActualClockScoreBudget.lean:182`.
- `liEvenCrossActualClockHistory_guarded_zero_outside_excess`: at a positive zero with nonnegative preceding history, `Cout(t)-V(t)=Anear(t)-P(t) ≥ zeta(t)>0`. This is a conditional consequence of a hypothetical first zero, not a construction of such a zero.
- `liEvenCrossActualClockScoreHistory_budget_iff_pos`: the score-weighted first-zero inequality `thc*IU(t) ≤ 303*(IK(t)+V(t))` is also equivalent to global positivity of D. Source: `RHTower/LiEvenCrossActualClockScoreBudget.lean:280`.
- `liEvenCrossActualClockPrimitive_eq_ageMean`: for `t>0`, `P(t)=t*K(t)-A(t)*∫P(s)dQ_t(s)`. Source: `RHTower/LiEvenCrossActualClockMovingHistory.lean:506`.
- `liEvenCrossActualClockPrimitiveScoreGap_lower`: `nu(1)*r³/48 ≤ G(r)` for `r≥0`. Positivity of this primitive gap alone does not discharge either first-zero budget. Source: `RHTower/LiEvenCrossActualClockPositivePrimitives.lean:431`.

## Count precision

- `riemannHypothesis_precision_tfae` equates RH, two-sided Count for Λ, each one-sided count, precision exponent 1/2, both integral-lattice halves at square-root scale, and Count after deleting the tower at 2. Source: `ArithmeticOfSquareRootPrecision/ThePrecisionLedgerOfTheCount.lean:26`.
- `count_iff_sub_mem_sqrtClass_of_successor`: whenever `u-successorWeight ∈ sqrtClass`, `Count(a) ↔ a-u ∈ sqrtClass`. Source: `ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean:58`.
- `complexCount_iff`: a complex count is exactly Count for the real part together with square-root-scale partial sums for the imaginary part. Source: `ArithmeticOfSquareRootPrecision/EveryRealGaugeHasAComplexCountLift.lean:35`.
