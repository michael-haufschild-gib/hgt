# Reflection branch of Matomäki–Teräväinen Lemma 3.5 (Process B for log phases)

- **ID:** mt-watt-reflection-process-b
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean programme), a peer brick for hgt-52 (KDIW owner)
- **Source:** hgt-52 request 2026-10-09; the KDIW card (owned by hgt-52, do not edit it); MT arXiv:2207.05038 Lemma 3.5.
- **Statement (Lean target):** module `RHTower/Sieve/MatomakiTeravainenWattReflection.lean`, namespace `RHTower.Sieve`:
  - `MTDeshouillersIwaniecBoundShort`, `MTWattBoundShort`: verbatim copies of `MTDeshouillersIwaniecBound` / `MTWattBound` (Sieve/MatomakiTeravainenTwistedFourthMoments) with the extra hypothesis `(N : ℝ) ^ 2 ≤ T` placed after `2 ≤ T`.
  - `mtDeshouillersIwaniecBound_of_short : MTDeshouillersIwaniecBoundShort → MTDeshouillersIwaniecBound`, and likewise `mtWattBound_of_short`.
  - Unconditional, standard axioms only.
- **Don't touch:** hgt-52's files (LinearHypersurface, HankelSlice*, ReciprocalSource*, HankelResolution*, HankelSecantKernel, HankelIncidenceChartRing, HankelRationalSingularities, TriangularPolynomialAutomorphism, TwistedCechSlice, CechKernelChase, ProjZeroSections, AwayLinearGenerators, CuspHardyInequality), any Kuznetsov*/Deck*/Maass* module, the route-E cards and the KDIW/MT cards.

## Split on the unit-block length `N` (blocks `(N, N']`, `N' ≤ 2N`, window `t ∈ [T/2, T]`)
1. `N² ≤ T`: the Short hypothesis.
2. `N ≥ T`: `integral_mtWatt_overHeight_le_energy` (Kuzmin–Landau), already in the corpus. Its bound `c T^{-4}(1/A + T/A²)Σ|a|²` fits the `(T+A)/(T⁴A)` term.
3. `√T < N < T` (the reflection branch, consumed by Type I and Type I/II):
   - **(R) pointwise reflection:** `|U_N(t)| ≤ C t^{-1/2} |Σ_{m ∈ R(t)} m^{it}| + C(log t/N + t^{-1/2})`, where `R(t) = [t/(2π(N'−c)), t/(2π(N+c))]`.
   - **(P) moving dual endpoints:** truncated Perron in the cutoff `1[m ≤ y(t)]`, at height `U = T/4`, `c = 1/log T`. The dual block becomes fixed blocks `(M, M']` (`M ≤ T/N ≤ √T`) with twisted coefficients `m^{−c−iu}`, at heights `t − u ∈ [T/4, 5T/4]`. Error `O(1)` pointwise, which is fine after `T^{-2}` normalization.
   - **(A) Abel reweighting:** `Σ m^{1−c}·m^{-1-iτ}` becomes sharp sub-blocks `(M, x]`, `x ≤ 2M`, to which Short applies, uniformly in `x`. Coefficient twists `a_m m^{iu}` are harmless (same `ℓ²` norm or sup norm).
   - **(W) windows:** `[T/4, 5T/4] ⊆ [T/4,T/2] ∪ [T/2,T] ∪ [5T/8,5T/4]`. Short applies at `T' ∈ {T/2, T, 5T/4}` because `(T/(2πN))² ≤ T/2` for `N ≥ √T`.
   - **Errors:** `(log t/N + t^{-1/2})^4 ∫|𝒜|²` and `T^{-2}·O(1)^4 ∫|𝒜|²` both fit the DI/Watt right sides. Use `integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine`.

## Proof of (R) with bounds only, no stationary-phase asymptotics
- Smooth window `φ`: `φ = 1` on `[N+¾, N'+¼]`, support in `[N+¼, N'+¾]` (built from `Real.smoothTransition`), so `Σ_n φ(n)F(n) = U_N(t)` for `F(x) = x^{-1-it}`.
- Poisson (Mathlib `Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`, as in `LogLatticePoissonAnticoncentration`): `U_N(t) = Σ_ν 𝓕(φF)(ν)`.
- For `m ≥ 1`, `𝓕(φF)(−m) = (t/2π)^{-it} m^{it} J_m(t)` with `J_m(t) = ∫ φ(x_m y) y^{-1-it} e^{it y} dy`, `x_m = t/(2πm)`. The `m^{it}` factor is exact.
- Fix a window `ψ` around `y = 1`, and put `J_∞(t) = ∫ψ(y)y^{-1-it}e^{ity}dy`. Then `|J_∞| ≤ C/√t` by the second-derivative test. The phase is `t(y − log y)`, with second derivative `t/y²`.
- For `m` with `x_m` deep inside the window, `J_m − J_∞` is non-stationary. It is `≲ (1/t)/|y_e − 1|`, and summing over `m` gives `log t/N`.
- At most `O(1)` values of `m` have `x_m` near a transition. Each such `|J_m|` is `≲ 1/√t`.
- Every other frequency (`ν ≥ 0`, `m` outside the range) is non-stationary. Use the first-derivative test in the middle range and two integrations by parts for `|ν| ≥ 2t`. The total is `≲ log t/N`.
- Result: `U_N(t) = (t/2π)^{-it}J_∞(t)Σ_{m∈R(t)} m^{it} + O(log t/N + t^{-1/2})`. Only `|J_∞| ≤ C/√t` is used.

## Status / log
- 2026-10-09: card created. Corpus scan:
  - no sharp AFE and no Process B exist;
  - the smooth Gaussian Jutila reflection (`SmoothDyadicZetaReflection`) leaves a gap `N ∈ (√T, T^{1/2+δ})`, so it is not sufficient.
  - Plan above. Next: A1 (window), then A2 (Poisson for `φF`).
- 2026-10-09 (later): modules compiled with `lake env lean`, no sorry.
  - HTGeometry: `MonotonePhaseFirstDerivativeTest` (first-derivative and stationary tests) and `SmoothPlateau` (plateau with explicit φ', φ'', ∫|φ'| ≤ 2, K₁/ℓ, K₂/ℓ²).
  - RHTower/Sieve:
    - `UnitBlockPoissonKernel`: f_t, ubFreq, Fourier formula, Σ_ℤ f_t(n) = U_N(t).
    - `UnitBlockFrequencyBounds`: non-stationary 4/(Nλ), stationary 218/√t, |ubJ| ≤ 23/√t.
    - `UnitBlockFrequencyComparison`: interior ‖ubFreq k − X^{-it}ubJ‖ ≤ (30/π)(16π/t + 1/(N(k₂−k)) + 1/(N(k−k₁))).
    - `UnitBlockFrequencyDecay`: ‖ubFreq k‖ ≤ K(1+t)²/k².
    - `UnitBlockPoissonSummation`: U_N(t) = Σ' ubFreq, harmonic, count and tail lemmas.
  - Next: `UnitBlockReflection` (classification of k, final pointwise reflection); then Perron, Abel and Short assembly.
- 2026-10-09 (later):
  - Compiled: `UnitBlockReflection` (pointwise B-process; standard axioms), `UnitBlockReflectionMoment` (MV window, twist, dual form, three windows, Perron mass), `HTGeometry/IntervalIntegralHolderSwap` (CS, Hölder-4, Fubini), `UnitBlockReflectionDualBlocks` (three dyadic Perron blocks; uses hgt-8a's `MatomakiTeravainenDualPerron`), `UnitBlockReflectionFourthMoment` (core lemma `exists_integral_unitBlock_fourth_le_dual`).
  - Next: `MatomakiTeravainenWattReflection` (Short defs; cases N²≤T / T≤N / Y<11 / Y≥11; arithmetic).
- 2026-10-09 (done): `MatomakiTeravainenWattReflection` builds with `lake --old build`. `mtDeshouillersIwaniecBound_of_short`, `mtWattBound_of_short`, the pointwise reflection `exists_norm_mtWattUnitBlock_sub_main_le` and the core `exists_integral_unitBlock_fourth_le_dual` all depend only on [propext, Classical.choice, Quot.sound]. Lint is clean for these modules.
  - Case split: N² ≤ T (Short); T ≤ N (over-height); N < T, T/(2πN) ≤ 11 (bounded dual); T/(2πN) > 11 (reflection, Perron with U = T/4, Hölder, Fubini, twist, three windows, Short on the dual blocks B ∈ {M, 2M, 4M} with B² ≤ T/2).
  - Short is applied at η/2; the factors log⁴ and (5/4)^{η/2} are absorbed into T^η.
  - Modules: HTGeometry `MonotonePhaseFirstDerivativeTest`, `SmoothPlateau`, `IntervalIntegralHolderSwap`; Sieve `UnitBlock{PoissonKernel, FrequencyBounds, FrequencyComparison, FrequencyDecay, PoissonSummation, Reflection, ReflectionMoment, ReflectionDualBlocks, ReflectionFourthMoment}`, `MatomakiTeravainenReflection{Arithmetic, Branches}`, `MatomakiTeravainenWattReflection`; peer module `MatomakiTeravainenDualPerron` (hgt-8a).
  - Umbrella incident: RHTower.lean was truncated at 21:36 by a concurrent sed rewrite. Repaired by restoring 9,777 HEAD imports and keeping all current lines; a backup of the truncated file is in the scratchpad. Peers are re-appending post-HEAD imports.
