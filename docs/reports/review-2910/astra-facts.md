# Mathematical facts supporting the RH frontier

## Complete atomic forms

- `TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_certified`: for each fixed real δ with `0 ≤ δ < certifiedOverlapIncrement`, the complete matrix of `transMetzlerProfile` at ratio `1 + δ` is eventually positive definite. This is a fixed-ratio theorem; its horizon may depend on δ. Source: `TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean:149`.
- `SpacingScaleHarmonicAnalysis.atomicFamilies_negative_iff`: for `|lam n| ≤ Λ(n)`, a normalized compactly supported C² profile and `OverlapGrowth κ`, infinitely recurring negative atomic tests are equivalent to failure of `WeilPositiveFull lam`. The growth and profile hypotheses belong to the statement. Source: `SpacingScaleHarmonicAnalysis/TheGaugeBecomesVisibleAtTheCriticalExponent.lean:365`.
- `eventually_completeWeil_eigenvalues_ge_uniformly_at_touching`: for a fixed C² unit-interval profile of positive L² mass, every `b < bumpRobin φ 1 / ∫φ² + completeWeilPoleShift φ 1 - log(2π)` is an eventual lower bound for every eigenvalue, simultaneously for every `0<c≤1`. Source: `CriticalArithmeticCorrelationTheory/OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching.lean:66`.
- `exists_finite_ramanujan_approximation_uniformly_at_touching`: one finite conductor family approximates every unit vector of complete energy at most T, uniformly over all `0<c≤1` and sufficiently large N. The family depends on profile, T and approximation error. Source: `CriticalArithmeticCorrelationTheory/OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching.lean:43`.
- `eventually_affineRamanujanPrimeWindow_uniform`: at fixed positive conductor q and fixed natural window endpoints `0<A≤B`, the actual Λ(k)/k-weighted affine Ramanujan window converges uniformly over **all** natural n,h. Thus n and h may depend arbitrarily on N. Source: `CriticalArithmeticCorrelationTheory/ActualAffinePrimeWindowsAreUniformInTheirParameters.lean:32`.
- `eventually_primeWindow_all_complex_Gram_packets`: at fixed q,A,B, one horizon controls every finite complex packet and all its coefficients; error is at most ε times the packet's squared norm over all residue classes. Source: `CriticalArithmeticCorrelationTheory/PrimeResidueWindowsControlEveryGramPacket.lean:143`.
- `primitivePrefixGram_quadratic_nonneg`: the primitive-root prefix kernel is positive semidefinite for every finite family of prefix lengths and real coefficients, at every positive conductor. Source: `CriticalArithmeticCorrelationTheory/TheArithmeticCurvatureHasAnExactGramCompletion.lean:108`.
- Its full quadratic form is `Σ_(ζ primitive m) |Σ_i a_i Σ_(r<k_i) ζ^r|²` (`primitivePrefixGram_quadratic_eq`). Its radical is exactly divisibility of `Σ_i a_i Σ_(r<k_i) X^r` by Φ_m; a finite conductor family has the intersection of these radicals (`primitivePrefixGram_family_eq_zero_iff`). Source: `CriticalArithmeticCorrelationTheory/CyclotomicDivisibilityClassifiesTheOverlapGramRadical.lean:57,74`.
- For `i,j≤Q`, summing the prefix Gram over nontrivial divisors of Q gives exactly `Q*min(i,j)−i*j`. This retains all mixed entries. Source: `CriticalArithmeticCorrelationTheory/AllDivisorConductorsRecoverTheDiscreteBridge.lean:52`, `sum_nontrivial_divisors_primitivePrefixGram`.
- `tendsto_plateauSuccessorFiber_div_log`: the normalized successor divisor fiber divided by log(N+1) tends to `bumpCorr transMetzlerProfile (1/c) / ∫transMetzlerProfile²` at every fixed c>0. Source: `TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean:140`.
- For every fixed c>1 this fiber tends to +∞ (`plateauSuccessorFiber_atTop`, same module, line 159). A horizon-independent bound on all such absolute row fibers is false.
- The eleven trial is a unit-mass Ramanujan packet on conductors 1,11,121. Its complete **untwisted** energy limit is established; the scalar completed upper margin including a prime-power tail cost <1/40 is negative. `elevenTrialUpperMargin_neg` proves that scalar margin's sign, not an eventual-negative theorem for the twisted atomic form. Sources: `TransMetzlerWeilPositivity/BoundedOverlap/ElevenPacket.lean:57,62,90`; `ElevenTrialMargin.lean:64,75`.
- `ramanujanPoleProfile_dyadic_twoSided_frame`: at `Q≥2` and `A≥4Q(Q−1)`, squared packet mass on `(A,2A]` lies between 1/4 and 5/4 of squared coefficient mass. The literal prime kernel vanishes on that annulus (`weilPrimeKernel_eq_zero_on_dyadic_annulus`). Source: `CriticalArithmeticCorrelationTheory/AnnularRamanujanFamiliesHaveTwoSidedFrames.lean:93,121`.

## Height-dependent locality

- `exists_prime_certifies_height`: among any set of more than `choose(heightIndex T,2)` primes, some prime tower has a compact C² generator and finite translate set whose Weil Gram negative index is at least `heightIndex T`. The generator and translate set are existential. Source: `EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean:320`.
- `twoPrime_tower_certifies_height`: for T≥0, a tower of step `|log(3^k/2^j)|` carries at least `heightIndex T` negative squares, for some `0<k≤floor(T log 2/π)+1` and `k≤j≤2k`. Source: `EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean:265`.

## Critical-line census

- `simple_critical_proportion_ge_67250071`: for every ε>0, eventually `(67250071/100000000−ε) Ncount(0,T) ≤ N0simple(0,T)`.
- `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio`: the lower limiting simple-critical proportion is at least `HD(1)+10⁻⁸`. Both statements: `IncommensurableGaborPinching/CriticalLineZeroProportion.lean:1042,1076`.
- For every admissible `WindowProfile ε₁ u`, η>0 and ε>0, eventually `N0simple(T,2T) ≥ (29/36−32π ε₁−ε) Ncount(T,2T) − coalescentSurplus(u,η,T) + offLineMultipleMass(T,2T)`. Source: `TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean:1288`.
- `calibration_five_models_four_thirds`: at bandwidth 4/3 the affine-model surplus is −1/144 for parameters (1,0), 0 for (1,1), and 1/16 for (2,1). The spectral-sieve model (Υ,0) meets the 1/18 budget iff Υ≤2; the unsigned-additive model (1+Υ,1) meets it iff Υ≤8/9. These are exact model evaluations, not prime-source discrepancy estimates. Source: `TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean:540`.

## Fixed-strip precision and detector budgets

- With E the actual normalized Chebyshev cumulative mean-square energy, `2*zetaZeroAbscissa = inf {r≥1 : ∃C≥0, ∀N≥2, E(N)≤C N^r}`. Source: `RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean:651`.
- The closed strips [1/6,5/6] and [1/4,3/4] are equivalent to `E(N)≪ε N^(5/3+ε)` and `E(N)≪ε N^(3/2+ε)`, respectively, for every ε>0. Same module: lines 698,729.
- A one-sided bound for the normalized Chebyshev sum on every point of any fixed power mesh gives the corresponding strip. For exponent c the general conclusion is `zetaZeroAbscissa≤1/2+max(0,c)`. Same module: lines 605,615.
- `gramProfile_five_sixths_feasible_iff`: for ν≥0, `∃x≥0,s, gramProfileBoundary(x,s,ν,κ)≤5/6` iff `ν≤1/15` and `κ+4ν≤4/3`.
- Exact witness: `(x,s,ν,κ)=(5/48,1/6,1/30,6/5)` gives 5/6. Retaining κ=2 forces the boundary above 5/6 for every ν. With exceptional term removed, minimum is 23/27 at `(x,s)=(5/18,1/6)`; unit-Gram minimum is 29/36 at `(0,1/6)`. These are exponent-budget statements, not zero-free theorems. Source: `RHTower/QuasiRHDetectorGramTradeoff.lean:52,124,161,220,254`.

## Actual theta-clock history

- `liEvenCrossActualClockHistory_first_zero_budget_iff_pos`: the inequality `Cout(t) ≤ V(t)` at every `t > 20` with `D(t)=0` and nonnegative preceding history is equivalent to `D(t)>0` for every `t>0`. Source: `RHTower/LiEvenCrossActualClockScoreBudget.lean:182`.
- `liEvenCrossActualClockHistory_guarded_zero_outside_excess`: at a positive zero with nonnegative preceding history, `Cout(t)-V(t)=Anear(t)-P(t) ≥ zeta(t)>0`. This is a conditional consequence of a hypothetical first zero, not a construction of such a zero.
- `liEvenCrossActualClockScoreHistory_budget_iff_pos`: the score-weighted first-zero inequality `thc*IU(t) ≤ 303*(IK(t)+V(t))` is also equivalent to global positivity of D. Source: `RHTower/LiEvenCrossActualClockScoreBudget.lean:280`.
- `liEvenCrossActualClockPrimitive_eq_ageMean`: for `t>0`, `P(t)=t*K(t)-A(t)*∫P(s)dQ_t(s)`. Source: `RHTower/LiEvenCrossActualClockMovingHistory.lean:506`.
- `liEvenCrossActualClockPrimitiveScoreGap_lower`: `nu(1)*r³/48 ≤ G(r)` for `r≥0`. Positivity of this primitive gap alone does not discharge either first-zero budget. Source: `RHTower/LiEvenCrossActualClockPositivePrimitives.lean:431`.
- `liEvenCrossActualClockGuardedZeroSet_rh_iff`: RH iff the guarded-zero set ZS is empty; not-RH iff ZS is nonempty. Source: `RHTower/LiEvenCrossActualClockTerminalHistory.lean:229`.
- `exists_forall_ge_not_mem_liEvenCrossActualClockGuardedZeroSet`: ZS is unconditionally bounded above. Thus `exists_liEvenCrossActualClockGuardedZero_budget` gives an eventual guarded-zero budget unconditionally; it does not settle whether the bounded set is empty. Same module: lines 257,271.
- Under not-RH, ZS has a final point τ at the infimum of negative-history times. Its analytic vanishing order is odd; preceding guarded zeros have even order at least two. Same module: `liEvenCrossActualClockGuardedZeroSet_ordered_of_not_rh`, line 110.
- Under not-RH, D has an exponentially negative escaping subsequence determined by the finite set of maximal inverse-zero growth frequencies (`exists_liEvenCrossActualClockLogHistory_negative_escape_of_not_rh`, line 65). RH instead implies D(t)>0 for every t>0 (line 57).

## Compensated Euler-deletion covariance

- `DeletionAveragedDivisor.errorEnergy_eq_covariance` gives the exact finite cumulative-error quadratic form, including all cross terms. `fullErrorEnergy_eq_covariance_add_tail` appends the literal infinite error tail. Source: `RHTower/EulerDeletionAveragedDivisorCovariance.lean:400,463`.
- `DeletionCutoffAverage.riemannHypothesis_iff_averagedCurrent_cofinally_subpower`: RH iff, for each nontrivial zero ρ and every e>0, there is B such that above every K one can choose `K≤X<M` with `|Re averagedCurrent(X,M,ρ)|≤B X^e`. The scale is X, although M is adaptive. Source: `RHTower/EulerDeletionCutoffAverage.lean:287`.

## Count precision

- `riemannHypothesis_precision_tfae` equates RH, two-sided Count for Λ, each one-sided count, precision exponent 1/2, both integral-lattice halves at square-root scale, and Count after deleting the tower at 2. Source: `ArithmeticOfSquareRootPrecision/ThePrecisionLedgerOfTheCount.lean:26`.
- `count_iff_sub_mem_sqrtClass_of_successor`: whenever `u-successorWeight ∈ sqrtClass`, `Count(a) ↔ a-u ∈ sqrtClass`. Source: `ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean:58`.
- `complexCount_iff`: a complex count is exactly Count for the real part together with square-root-scale partial sums for the imaginary part. Source: `ArithmeticOfSquareRootPrecision/EveryRealGaugeHasAComplexCountLift.lean:35`.
- `deciding_input_necessary_properties` assumes a predicate S on **all real arithmetic weights**, with `∀a, S(a) → Count(a)`. It proves Liouville rejection, separation under nonzero `ε n^(−η)` for `0≤η<1/2`, failure of finite-prefix determination, and square-root-class differences between two S-weights. It is not a classification of every possible RH proof. Source: `ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean:50`.
