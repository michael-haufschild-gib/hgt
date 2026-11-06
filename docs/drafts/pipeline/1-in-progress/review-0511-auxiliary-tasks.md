# Review-0511 §2.1 auxiliary tasks

- **ID:** review-0511-aux
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0511/obstacles-summary.md#21-auxiliary-tasks-difficulty-not-certified)
- **Statement:** Each task A* gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A43 | done | `ArithmeticIncidencePositivity/TheWeilFloorTowerIsFrozen.lean`: `a_k < 0.3621`, `a_∞ − a₀ < 10^(−7800000)` |
| A28 | done | `WindowTowerOfSpecZ/TheAtomicLatticeHasTheSharpSchurBound.lean`: `Σ_{d≤N}Λ(d)/d ≤ log N`, atomic form `≤ ½ log N` |
| A52 | statement done, numeric `c` open | `RHTower/Heat/AHeatCoefficientGivesAZeroFreeStrip.lean`: ceiling `Λ_X log X ≤ κ` ⇒ depth `≤ √(κ/c)`; `κ < c/4` ⇒ `Re s ≤ σ < 1` |
| A7 | done as Schur complement; Gram expansion of the dual norm not done | `GrowingWindowsOfSpecZ/TheFirstStageComplementIsASchurComplement.lean`: `twoCollarForm_firstStage_eq` |
| A51 | done | `ZeroConfigurationGeometry/HeatScaleRepulsion/TheSaddleHorizonOnAlmostAllHeights.lean`: exceptional measure `O(T^{1−ε²/32})` |
| A54 | Li, PA, Jensen and HCF parts done; Jensen and HCF heights use `xiMassHeight(1/100)`, `≥ e^{4000}` because the corpus count has remainder `10T` | `VerifiedHeightRungs/LiAndHausdorffEntries.lean`: `λ_n ≥ 0` for `n ≤ 4.7T`; row `(k,r)` for `k+1 ≤ 1.5(T−1)`, `r ≤ RT³`; `VerifiedHeightRungs/JensenEntries.lean`: `R_d(Ξ)` real-rooted for `2·10⁷d⁴ ≤ T log T`; `FiniteFreeProbability/JensenStripContraction.lean`; `VerifiedHeightRungs/HeatGridEntries.lean`: heat and pole-hyperplane source forms nonnegative at every offset for `4800(deg p+1) ≤ Y`, `Y ≥ heatGridHeight h` |
| A48 | VK collar and all-aperture finite ranks done; `D` in `T(N) = D(N+1)³` not explicit (needs explicit strip bounds for `Ξ, Ξ'`, a floor for `\|Ξ\|` at low height, one zero of known height; expected `D ≈ 10⁵–10⁶`) | `ThetaCuspSections/VinogradovKorobovCriticalCollar.lean`; `ThetaCuspSections/AllApertureFiniteRankCriterion.lean`: core and tail of the current are both `∝ a`, so current `≥ 0` on `\|b\| ≤ D(N+1)³` gives rank `N` at that `a`; `VerifiedHeightRungs/ThetaEntries.lean` |
| A11 | done (ladders were already in `ArithmeticLorentzianGeometry`) | `ArithmeticCastelnuovoSeveri/TheWindowReceiversOfACurve.lean`: one window of size `#R` decides purity; `ℋ(n) = {1}` for large `n`; evaluation bounded for `n ≤ #R`, unbounded above |
| A49 | done | `CanonicalSystemOfTheWindowTower/ThePrecontactWeilSpacesHaveSamplingBases.lean`: `‖x‖² = Σ_{S_φ(t)=0} |F_x(t)|²/K(t,t)`, at most one exceptional phase; `TheSamplingAtomsArePositiveMimicsOfZeta.lean`: finite Lorentzian mass, zeta image on every smooth window below onset, sharp count uniform in the phase |
| A44 | height law and `N_d` threshold done; explicit constants in the Cauchy limit and an explicit degree at which a given zero is counted open | `FiniteFreeProbability/JensenRootsAreRealBelowTheSaddleEdge.lean`: every root with `|Re z| ≤ √(d log d)/100` is real, non-real zeros of `Φ_d` have `|Re u| < 100√(d/log d)`; `NonRealJensenCountBound.jensenNonrealCount_le_sqrt_of_log_ge`: `N_d ≤ 300√(d log d)` for `d ≥ exp(6.1·10⁶)` |
| A25 | done: `h¹` part positive; mixed-jet part closed as an equivalence, RETIRED beyond it | `LatticeSectionTheory/ThePrimitiveH1IsCoerciveAtSmallDegree.lean`: for `a ≤ 181/500`, `h¹_prim ≥ ∫f²/10000` on all tests, Riemann inequality on the whole subsurface. `ArithmeticHarmonicAnalysis/SameOrderJetRecoveryIsHomogeneousLogIndependence.lean`: `∂ₛʳF(pˢ)|₀ = r! Σ_{\|a\|=r} c_a Π(log pᵢ)^{aᵢ}`; order-`r` recovery ⇔ `K`-independence of degree-`r` log monomials; Baker for `r = 1`, Gelfond–Schneider for two primes. Three primes at `r ≥ 2` is that independence itself (Schanuel-type), so no jet algebra decides it |
| A23 | depth law effective; star horizons and gcd tables follow the same horizon | `SquareRootThreshold/EffectiveHorizons/ExplicitPrimeNumberTheorem.lean`: for `x ≥ 2`, `\|ψ(x) − x\| ≤ 1000x e^{−√(log x)/20}`, `\|Σ_{n≤x}Λ(n)/n − log x + γ\| ≤ 6400 e^{−√(log x)/20}`. `HodgeTheoryWithoutVarieties/TheDepthLawIsEffective.lean`: `P_N ≤ (log N − γ + ε)\|x\|²` for `N ≥ H(ε)`, and `R_N ≥ (log d − ε)\|x\|²` on the star of `d` for `⌊N/d⌋ ≥ H(ε)`, `H(ε)` explicit |
| A18 | rungs done; numerics need A47 | `VerifiedHeightRungs/PolyaFrequencyEntries.lean`: RH through `T` gives `PF_k` at the centre for `k+1 ≤ 3T`, `PF_k` at `t` for `k+1 ≤ 3Δ`, `\|t\|+Δ ≤ T`, and all slice coefficients `≥ 0` on `\|t\| ≤ T−½`; Jensen and two-grid degrees in `JensenEntries`, `HeatGridEntries` |
| A46 | done, height astronomically above verified range | `VerifiedHeightRungs/WindowEntries.lean` (zero side in `TheZeroSideOfTheWindowRung.lean`): `RHVerifiedThrough (windowHeight a) → WindowPositiveAt ζ a`, `windowHeight` explicit (`T₁ = 4e^{E+2π}`, `n ≍ gapHeight/σ`, `b ≍ 48^{−2n}`, `T ≍ b⁻⁸`). Ingredients: `ZeroGapsFromVerifiedZeros.lean` (no gap of length `σ` at height `≥ gapHeight σ`), `SeparatedNodesControlTheTransform.lean` (Lagrange + Taylor), `TheNormalizedSmoothingKeepsThePoles.lean` (pole terms kept for every test). The [D] heuristic `log T₀ ≍ Σ_{n≤e^{2a+s}}Λ(n)/√n` is not what this proves: a floor for the low band costs `48^{−2n}` |
| A2 | in progress: target `θ < 1/4`, not yet compiled end to end | `1080` entered only through the prime-packet lemmas; Pythagoras (`‖u_{>Q}‖² = ‖u‖² + ‖u_{≤Q}‖²`) removes it. The torsion counterterm sharpens to `2 log N + log 4 + 4` (`renormalizesAt_two_log`, compiled), so the Riesz range becomes `4 log R + 18 ≤ log N`. Build order below |
| A36 | shallow necessity and fixed-depth crystal with uniform RvM open | Interferometer and distinct ordinates already formalized. Fixed-depth crystal plan below |

## A2 build order (`_of_four_log` lemmas; old names stay as wrappers)

`SuccessorShellArithmetic/Conductor/HarmonicGramUniformRemainder`, `CompletedArithmeticForms/ConductorBandTopTailBounds`, `ConductorBandPrimeAndCenterBounds`, `ConductorBandOverlapAndNonRatioBounds`, `ConductorBandQuadraticCenterBounds`, `WeightedConductorCrossBounds`, `HighConductorAdjunctionCoercivity`, `CriticalArithmeticCorrelationTheory/TerminalSupportSharpensTheWeightedNearPairing`, `TheLinearMomentRemovesTheOverlapLogarithm`, `TerminalSupportLeavesOnlyALinearHighConductorLoss`, `EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans`, then the two corollaries. Then A36: `WindowVisibilityLaw/CoherentClusterAndTiltAmplificationLaw` (generic splitting), `WindowVisibilityLaw/TheShallowDepthMassBound` (written, unchecked; wire into the umbrella once checked).

## A36: fixed-depth crystal with uniform RvM (plan)

Crystal `L ≍ log T` minus its on-line points below height `t₀ = T^κ`. A test can hide mass below `t₀`, but only with
`‖F‖²_{|x|<t₀} ≤ e^{C a t₀} ‖F‖²_{|x|>t₀}` (Turán–Nazarov). Flat-top localization at scale `T^{1/2}` around the packet has tail
`e^{−T^{1/4}}`, so the crystal inequality applies to `F·m` once `a t₀ ≪ T^{1/4}`. Needs: Turán–Nazarov for bandlimited
functions, truncated lattice sampling, the crystal bound for the localized test.

## Rule for verified-height statements

`∃ C, RHVerifiedThrough (C …) → X`, with `X` implied by RH, is classically trivial: split on RH and pick
`C` above an off-line zero. So every such theorem must carry an explicit height. This applies to A46, A48,
A54 and the verified-height part of A5.
