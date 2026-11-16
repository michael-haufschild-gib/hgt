# Review 1611 — the ECS route: exclusion of the critical state

Corpus: commit 8319f63d78 with the working tree (16 November 2026). Inputs: the 49 Lean files of [ExclusionOfTheCriticalState](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState.lean) (17 128 lines), its README read through the corpus search tool, the modules ECS imports, and corpus searches for results ECS does not use. Facts: [logs/review-1611-route-ecs-facts.md](../../../logs/review-1611-route-ecs-facts.md).

Every cited declaration is a Lean statement read in source. Results about the critical state are unconditional: either "RH, or a critical state exists and has property P", or a theorem with the state as hypothesis. *Readme* marks content of the ECS README. *Reading* marks an interpretation made in this report; it is not a Lean statement. Identifiers: E-J (just work), E-O (open problems), E-Q (questions), E-T (tools), E-M (missed connections). In the companion reports ECS is task J10, open problem O10 and the programme of [obstacles summary §2.16 and §2.18](obstacles-summary.md); its row in the route tables is in [route-obstacles.md](route-obstacles.md).

## 1. Summary

### 1.1 What the route is

Weil's quadratic form, restricted to real profiles F on the half-line u < 0 and confined by the weight e^(−8u), is

  Q_R(F) = B(F) + a(R)·W₈(F),  W₈(F) = ∫F(u)²e^(−8u)du,

with B Weil's bare form (Gamma part − prime part + pole part) and a(R) a constant divided by R ([`criticalAliasCoefficient`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalFormHasAGammaLiminf.lean#L37)). The window threshold W₀ is the infimum of the thresholds of the windows [−A, 0] ([`windowThreshold`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L52)); RH holds exactly when every window threshold is infinite ([`riemannHypothesis_iff_windowThreshold_eq_top`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L88)). Off RH, W₀ is finite and Q_(W₀) has a unit null vector F, the **critical state** ([`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339); definition [`IsCriticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L328)). The state

- is unique up to sign ([`criticalHalfLineGroundState_unique_up_to_sign`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L67));
- has a transform LF(w) = ∫F(u)e^(wu)du with no zero on Re w ≥ 0 ([`criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L126));
- solves the weak equation Q_(W₀)(F, G) = 0 for every G of the energy domain H ([`criticalHalfLineMixedEnergy_groundState_eq_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateSatisfiesTheWeakEquation.lean#L136); domain [`CriticalHalfLineEnergyDomain`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineFormHasItsActualDomain.lean#L23));
- satisfies |F(u)| ≤ C e^(βu) for every β < 15/2 ([`criticalHalfLineGroundState_exponential_bounds`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L243)), and a(W₀) > 0 ([`criticalState_zeroNorm_limit_neg`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L783)).

RH is the statement that this one function does not exist.

### 1.2 How it is supposed to work

The programme proves every exact property of F as a theorem and looks for one property that contradicts the arithmetic of ζ while failing for models with off-line zeros (*readme*). F is a null vector, so every relation it satisfies is an identity and no constant is lost between steps. The proved picture:

1. **Prime coordinates.** Tested on the probes e_p(u) = e^(pu)·1_(u<0), which lie in H for p > 4, the weak equation is a closed formula in transforms of F: a·LF(p−8) + Gamma pairing − LF(p)·ΣΛ(n)n^(−½−p) − TF(p) + pole terms = 0, where TF collects the backward prime translates ([`criticalState_probeEquation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateEquationOnProbes.lean#L118)).
2. **Residue transport.** Replacing ΣΛ(n)n^(−½−p) by −ζ'/ζ(½+p) continues the equation in p and moves the poles of ζ'/ζ eight units to the left. LF continues to a meromorphic function on ℂ whose poles are exactly the points ρ − 17/2 for the nontrivial zeros ρ, with residue −m_ρ·LF(ρ−½)/a, nonzero when Re ρ ≥ ½ ([`riemannHypothesis_or_criticalState_meromorphic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateIsMeromorphicInThePlane.lean#L441), [`differentiableAt_stateContinuation_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateHasPolesAtTheZeros.lean#L193)).
3. **Three regions.** Right of the strip the equation is in prime coordinates. On the strip the Gamma pairing is the functional equation in Lévy form ([`levyGamma_eq_reflected_euler`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheGammaPairingIsTheFunctionalEquationOnTheStrip.lean#L504)). Left of the strip the Euler parts cancel, and a·LF(w) is minus the archimedean head, the prime heads and the two charges at w + 8 ([`stateMeromorphic_eq_left`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateIsMeromorphicInThePlane.lean#L350)).
4. **The explicit formula and (★).** On the whole domain, BF(p) − BF(1) = Σ_z LF(z)(1/(p−z) − 1/(1−z)) over the centred zeros z = ρ − ½ ([`globalRemainder_sub_eq_zeroSum`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L667)). At the state this is (★): a(LF(w) − LF(v)) = −Σ_z LF(z)(1/(w+8−z) − 1/(v+8−z)) ([`criticalState_starEquation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L712)). The state is the Cauchy transform of its own values at the zeros.
5. **One series.** As distributions on the line, Σ_z LF(z)e^(−zu) is −a·e^(−8u)F(u) for u < 0 and a·F⁺(u) for u > 0, where F⁺ is the prime side of the state ([`criticalState_hasSum_heated_zeroSeries`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond.lean#L363), [`criticalState_hasSum_zeroSeries_test`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L312)).

The route closes when one exact property of F contradicts a property of ζ that the models with off-line zeros lack.

### 1.3 Where it ends

The last step has a Lean criterion. For a profile F of H, the beyond-the-wall prime-pole balance

  Φ_F(p) = ŜF(p) + LF(−½)/(p + ½),  ŜF(p) = Σ_n Λ(n) n^(p−½) ∫_(−log n)^0 F(u)e^(pu)du,

is holomorphic on Re p < −½. The property "Φ_F continues holomorphically to Re p < 0 for every F in H" ([`ZetaBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L268))

- excludes the state ([`no_criticalState_of_beyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L399)) and is equivalent to RH ([`zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L452));
- fails for the state's own balance ([`criticalState_not_hasBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L380)), because every state sees a zero with 0 < Re ρ < ½ ([`criticalState_exists_seen_left_zetaZero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/TheCriticalStateSeesALeftZero.lean#L1878));
- is sharp: for every δ > 0, continuation to Re p < δ fails already for the probe e_5 ([`not_forall_wallPrimeBalance_continues_past_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L563));
- fails on the prime-two deformations and on positive Euler twins that agree with ζ through any prefix ([`primeTwo_not_modelBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean#L550), [`exists_positive_euler_twin_failing_beyondTheWallContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean#L600)).

*Reading.* Φ_F is the Laplace transform of the right-of-wall wave Σ_(n>e^v) Λ(n)n^(−½)F(v − log n) − ∫_(x>v) F(v−x)e^(x/2)dx, and the polar term is the continuum main term of the prime number theorem ([`polarWallTerm_eq_continuumMainTerm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L217)). The wave is the remainder ψ(e^x) − e^x, weighted by e^(−x/2) and averaged against F. Continuation to Re p < 0 for every F is the bound ψ(x) − x = O(x^(½+ε)) in F-averaged form. The state is the profile at which this average is worst: it sees every zero on or right of the line. Stage 5 is RH in the form of the prime number theorem with square-root remainder, averaged by one function.

### 1.4 Stages

| Stage | Statement | Status |
|---|---|---|
| 0 | Dichotomy, uniqueness, zero-free transform, weak equation, continuation, (★), zero-side identities, multiplicities, a seen left zero, decay ruler, sign law, finite index, energy identities, the criterion and its equivalence with RH | proved (§2) |
| 1 | Zero pairing for all pairs of profiles; exact index law | the state against every profile is proved with Gaussian summation ([`criticalState_tendsto_zeroPairing`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L699)); two general profiles and the index law are just work (E-J4, E-J1) |
| 2 | Finitely many zeros right of the line ⇒ no state | open; equivalent to B13 (E-O2) |
| 3 | The collar −log 2 < u < 0 against the poles | open; no mechanism (E-O5) |
| 4 | Euler-log positivity in the prime tail | open; no mechanism (E-O3) |
| 5 | No state for ζ | equivalent to RH (E-O1) |

## 2. What is proved

### 2.1 Stage 0 (inputs from ArithmeticHodgeTheoryOfDegenerations)

| Result | Lean |
|---|---|
| RH, or a critical state at a finite threshold W₀ > 0 | [`riemannHypothesis_or_exists_criticalHalfLineGroundState`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality.lean#L339) |
| The state is unique up to sign | [`criticalHalfLineGroundState_unique_up_to_sign`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L67) |
| LF ≠ 0 on Re w ≥ 0 | [`criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L126) |
| Weak equation against every profile of H | [`criticalHalfLineMixedEnergy_groundState_eq_zero`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateSatisfiesTheWeakEquation.lean#L136) |
| abs F(u) ≤ C e^(βu) for ½ < β < 15/2; ∫F²e^(−bu) < ∞ for b < 15 | [`criticalHalfLineGroundState_exponential_bounds`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L243) |
| Positive square mass on every terminal interval (−d, 0) | [`criticalHalfLineGroundState_endpoint_mass_pos`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoTerminalSupportGap.lean#L194) |
| The ground energy is differentiable in R and strictly concave in 1/R; a minimizer minimizes at one ratio only | [`hasDerivAt_criticalHalfLineGroundEnergy`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningGlobalTransverseGapAndResponse.lean#L399), [`confiningHalfLineGroundEnergy_strict_jensen`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningHalfLineGroundEnergyCurvature.lean#L45), [`halfLineEnergyMinimizer_ratio_unique`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningHalfLineGroundStateSeparation.lean#L41) |

### 2.2 Probes and the state equation

| Result | Lean |
|---|---|
| e_p lies in H for p > 4 | [`criticalHalfLineEnergyDomain_probe`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExponentialProbesLieInTheEnergyDomain.lean#L123) |
| Weil's bare form on two probes is the Carathéodory kernel (D(p) + D(q))/(p + q) of D = (log ξ)'(½ + ·) | [`bareMixedEnergy_probe_eq_criticalLogDerivKernel`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/WeilsFormOnProbesIsTheCaratheodoryKernelOfXi.lean#L271), [`probeSymbol_eq_logDeriv_xiCent`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/WeilsFormOnProbesIsTheCaratheodoryKernelOfXi.lean#L220) |
| The explicit formula on the probe span | [`bareMixedEnergy_probe_eq_zeroSide`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/WeilsFormOnProbesIsTheCaratheodoryKernelOfXi.lean#L283) |
| The state equation on probes, p > 4 | [`criticalState_probeEquation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateEquationOnProbes.lean#L118) |
| Its holomorphic extension in p vanishes at real p > 4 | [`stateEquation_ofReal_eq_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateEquationIsHolomorphicInTheProbeExponent.lean#L427) |

### 2.3 Continuation

| Result | Lean |
|---|---|
| On Re w > −8 the continuation is holomorphic exactly where ζ(w + 17/2) ≠ 0 | [`differentiableAt_stateContinuation_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateHasPolesAtTheZeros.lean#L193) |
| Continuation to Re w > −17/2; a pole at every zero with Re ρ ≥ ½ | [`riemannHypothesis_or_criticalState_poles_across_line`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateContinuesAcrossTheCriticalLine.lean#L358) |
| On abs(Re p) < ½ the Lévy symbol is −(ζ'/ζ(½+p) + ζ'/ζ(½−p)) and ΓF = −LF·(ζ'/ζ(½+p) + ζ'/ζ(½−p)) + JF | [`levySymbol_eq_neg_logDeriv`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheGammaPairingIsTheFunctionalEquationOnTheStrip.lean#L420), [`levyGamma_eq_reflected_euler`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheGammaPairingIsTheFunctionalEquationOnTheStrip.lean#L504) |
| Meromorphic in ℂ; poles only at ρ − 17/2 (Re ρ > 0) with residue −m_ρLF(ρ−½)/a; bounded on Re w ≤ −17/2 − δ | [`riemannHypothesis_or_criticalState_meromorphic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateIsMeromorphicInThePlane.lean#L441) |
| Left of the strip: a·LF(w) = −(JF + ŜF + LF(½)/(w+15/2) + LF(−½)/(w+17/2)) at w + 8 | [`stateMeromorphic_eq_left`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateIsMeromorphicInThePlane.lean#L350) |
| The continuation tends to 0 as Re w → −∞, uniformly in Im w | [`exists_left_halfPlane_norm_stateMeromorphic_lt`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateVanishesUniformlyToTheLeft.lean#L151) |
| Square-integrable vertical traces beyond the Euler boundary | [`isHalfPlaneHardy_leftContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheLeftContinuationHasSquareIntegrableVerticalTraces.lean#L121) |
| At distance δ from the zeros the pairing with a probe is O((1 + abs p)(1 + abs p/δ)) | [`norm_globalRemainder_le_of_dist`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheContinuationIsPolynomiallyBoundedOffTheZeros.lean#L49) |

### 2.4 The explicit formula on the domain and (★)

| Result | Lean |
|---|---|
| BF(p) − BF(1) = Σ_z LF(z)(1/(p−z) − 1/(1−z)) for every F in H; Liouville on a glued defect, no bound on ζ'/ζ inside the strip | [`entireDefect_eq_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L577), [`globalRemainder_sub_eq_zeroSum`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L667) |
| (★) a(LF(w) − LF(v)) = −Σ_z LF(z)(1/(w+8−z) − 1/(v+8−z)), Re w, Re v > −4 | [`criticalState_starEquation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L712) |
| The zero values solve a Cauchy system, normalised at the left end | [`criticalState_zeroValues_cauchy`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes.lean#L744), [`criticalState_zeroValues_cauchy_normalised`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroSideIsNormalisedAtTheLeftEnd.lean#L101) |
| Difference equation a·LF(p−8) + ξ'/ξ(½+p)·LF(p) = −(BF(1) + ΔF(p)), Re p > 4, with a pole-free right side | [`criticalState_differenceEquation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProductOfTheStateWithXiIsEntire.lean#L201) |

### 2.5 Zero-side identities

| Result | Lean |
|---|---|
| Two vertical lines cut out Σ_z LF(z)H(z) for every F in H and every entire H of fourth-order decay | [`hasSum_zeroValues_two_lines`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TwoVerticalLinesCutOutTheZeroSeriesOfTheState.lean#L228), [`criticalState_hasSum_zeroValues_two_lines`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TwoVerticalLinesCutOutTheZeroSeriesOfTheState.lean#L308) |
| Heated zero series: Σ_z LF(z)e^(εz²−zT) = a(k_ε * F⁺ − k_ε * (e^(−8u)F))(T) | [`criticalState_hasSum_heated_zeroSeries`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond.lean#L363) |
| Left of the wall the heated state is the zero series up to a Gaussian | [`criticalState_heatedState_add_zeroSeries_le`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond.lean#L455) |
| Against smooth compactly supported tests; left tests read the state, right tests read the prime side | [`criticalState_hasSum_zeroSeries_test`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L312), [`criticalState_hasSum_zeroSeries_test_left`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L339), [`criticalState_hasSum_zeroSeries_test_right`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L361) |
| W(F, G) = Σ_z LF(z)LG(−z) for smooth G of compact support in u < 0 | [`criticalState_hasSum_bareMixedEnergy`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests.lean#L387) |
| W(F, G) = lim_(ε→0+) Σ_z LF(z)LG(−z)e^(εz²) for every G in H | [`criticalState_tendsto_zeroPairing`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L699) |
| lim_(ε→0+) Σ_z LF(z)LF(−z)e^(εz²) = −a∫F²e^(−8u) < 0: the zero values are a negative vector of the pairing β(c, d) = Σ_z c_z d_(−z) | [`criticalState_tendsto_zeroNorm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L755), [`criticalState_zeroNorm_limit_neg`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L783) |
| W(F, G) = −a∫G e^(−8u)F for every G in H | [`criticalState_bareMixedEnergy_eq_neg_statePairing`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L681) |

### 2.6 The entire product, multiplicities and seen zeros

| Result | Lean |
|---|---|
| ξ(w + 17/2)·LF(w) is entire | [`riemannHypothesis_or_criticalState_xi_mul_entire`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProductOfTheStateWithXiIsEntire.lean#L218) |
| For Re z ≥ 0 it vanishes at z − 8 exactly when ξ'(½ + z) = 0 | [`stateXiProduct_centredZero_sub_eq_zero_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProductOfTheStateWithXiIsEntire.lean#L165) |
| At a seen zero of multiplicity m it has order exactly m − 1 | [`analyticOrderAt_stateXiProduct_add_one`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/StateProductMultiplicity.lean#L144), [`criticalState_stateXiProduct_order`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/StateProductMultiplicity.lean#L172) |
| A seen zero with 0 < Re ρ < ½; a pole in −17/2 < Re w < −8 | [`criticalState_exists_seen_left_zetaZero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/TheCriticalStateSeesALeftZero.lean#L1878), [`criticalState_has_left_strip_pole`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/TheCriticalStateSeesALeftZero.lean#L1892) |

### 2.7 Decay

| Result | Lean |
|---|---|
| LF holomorphic on Re w > κ (κ ≤ −7) ⇒ Re ρ ≤ κ + 17/2 for every zero with Re ρ > ½ | [`zero_re_le_of_laplace_holomorphic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheDecayOfTheStateReadsTheZeros.lean#L290) |
| Decay ruler: ∫F²e^(−bu) < ∞ ⇒ Re ρ ≤ (17 − b)/2 | [`criticalState_not_integrable_of_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheDecayOfTheStateReadsTheZeros.lean#L316) |
| If every centred zero has Re z ≤ κ, the averaged state is O(e^(−(8−κ')t)) for every κ' > κ | [`exists_bound_averagedState`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L627) |
| With the zero-free half-plane Re s > 20999/24000: every averaged rate below 183001/24000 | [`criticalState_averaged_decay_beyond_barrier`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L701), [`re_centredZero_le_seed`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L682) |
| The barrier comparison absorbs exactly up to rate 15/2 | [`exponentialBarrier_forcingDominance_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/SharpExponentialBarrier.lean#L33), [`no_polarForcing_absorption_at_eight`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/SharpExponentialBarrier.lean#L164) |

### 2.8 Signs

| Result | Lean |
|---|---|
| The state has both signs on every ray u < −T; the proof uses that ζ has no real zero in (½, 1) | [`criticalState_changes_sign_on_every_ray`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateChangesSignOnEveryRay.lean#L517) |
| Landau's obstruction for almost-everywhere signed tails | [`integrable_exp_of_signed_tail_of_real_continuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Analysis/LandauTailSignObstruction.lean#L146) |
| The prime-side datum and the prime-minus-pole wave have both signs on every tail | [`criticalState_prime_side_changes_sign_on_every_ray`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/ThePrimeSideChangesSignOnEveryRay.lean#L258), [`criticalState_prime_wave_changes_sign_on_every_ray`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/ThePrimeSideChangesSignOnEveryRay.lean#L411) |
| Finite tail moment forms of both signs | [`criticalState_tailProbeQuadratic_both_signs`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheStateHasIndefiniteFiniteProbeMatrices.lean#L97) |
| After the first charge, every archimedean mode has the sign of LF(½) | [`criticalState_resolvent_tail_half_re_pos`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean#L203), [`criticalState_left_prime_balance_re_pos`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean#L247) |

### 2.9 Index

| Result | Lean |
|---|---|
| At each ratio R > 0, orthonormal families of smooth unit tests with Q_R ≤ 0 have bounded size; critical ratios accumulate only at ∞ | [`exists_bound_orthonormal_nonpositive`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheConfinedFormHasFiniteIndexAtEveryRatio.lean#L98) |

### 2.10 Energy, charges and nonlinear tests

| Result | Lean |
|---|---|
| 9·(∫Ge^(u/2))² ≤ ∫G²e^(−8u), sharp at e_(17/2) | [`growingPolarCharge_sq_le_confinementMass`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Energy/PolarChargeCoercivity.lean#L90) |
| Coercivity on the charge-zero hyperplane; full energy plus one charge square is coercive | [`criticalState_charge_zero_coercivity`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Energy/PolarChargeCoercivity.lean#L175), [`criticalState_one_charge_coercivity`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Energy/PolarChargeCoercivity.lean#L230) |
| A pole-free representative of the full energy on the charge-zero subspace | [`fullEnergy_eq_chargeNeutral_poleFreeForm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Energy/PolarChargeCoercivity.lean#L152) |
| abs F has positive energy; the pole gain exceeds the Gamma loss plus the prime gain; positive and negative parts carry a quarter each | [`criticalState_modulus_energy_pos`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/ModulusEnergyDefect.lean#L98), [`criticalState_modulus_balance`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/ModulusEnergyDefect.lean#L117), [`criticalState_sign_parts_energy`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/ModulusEnergyDefect.lean#L130) |
| The arctan test: an exact balance, strict, with explicit terminal floors, and no uniform boundary floor | [`criticalState_arctan_balance`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/BregmanDissipation.lean#L118), [`criticalState_arctan_balance_strict`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/StrictBregmanBalance.lean#L138), [`criticalState_arctan_quantitative_balance`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/QuantitativeBregmanBalance.lean#L203), [`criticalState_no_uniform_positive_arctan_boundary_floor`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Nonlinear/VanishingBregmanBoundaryCost.lean#L110) |

### 2.11 The wall

| Result | Lean |
|---|---|
| Terminal mass ≤ Ch with a logarithmic gain; average square mass → 0; σ·abs LF(σ + iy) → 0 uniformly in y | [`criticalState_terminal_square_mass_linear`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheCriticalStateHasLinearTerminalSquareMass.lean#L91), [`criticalState_terminal_square_mass_logarithmic_gain`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheCriticalStateHasVanishingAverageWallMass.lean#L139), [`criticalState_terminal_average_tendsto_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheCriticalStateHasVanishingAverageWallMass.lean#L171), [`criticalState_uniform_right_laplace_o_inv`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheCriticalStateHasVanishingAverageWallMass.lean#L192) |
| The scaled archimedean wall balance tends to a finite positive mass or diverges; it is not o(1/t) | [`criticalState_archimedeanWall_asymptotic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheArchimedeanWallMassControlsTheLeftAsymptotic.lean#L196), [`criticalState_scaled_wall_not_tendsto_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheArchimedeanWallMassControlsTheLeftAsymptotic.lean#L235) |
| The growing charge is nonzero | [`criticalState_growingPolarCharge_ne_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/NonvanishingPolarForcing.lean#L30) |

### 2.12 The criterion and the models

| Result | Lean |
|---|---|
| Decomposition of the left remainder into the archimedean tail (holomorphic on Re p < 5/2) and Φ_F | [`globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L176), [`differentiableOn_archimedeanWallTail`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L92) |
| A seen zero with Re z < δ blocks continuation of Φ_F to Re p < δ, for every F in H | [`not_wallPrimeBalance_continues_of_seen_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L321) |
| The state fails the criterion and the sub-strip Hardy wave | [`criticalState_not_hasBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L380), [`criticalState_not_hasSubstripPrimeHardyWave`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L390) |
| The criterion ⇔ RH ⇔ no state ⇔ continuation of the bare prime heads on the pole-neutral subspace | [`zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L452), [`zetaBeyondTheWallPrimeContinuation_iff_no_criticalState`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L458), [`purePrimeHeadContinuation_iff_zetaBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L550) |
| A local factor with ‖β‖ < √p < ‖α‖ < p fails the model criterion; the obstruction sits at q* = ½ − log α/log p | [`not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean#L288) |
| Prime-two deformations (½ < θ < 1) and positive twins beyond any prefix fail | [`primeTwo_not_modelBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean#L550), [`exists_positive_euler_twin_failing_beyondTheWallContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/BeyondTheWallContinuationFailsOnTheModels.lean#L600) |
| Positive twins: exact functional equation, positive real axis, bounded multiplicative coefficients ≥ 1, passive scattering, an off-line zero, and no representation with nonnegative logarithmic coefficients | [`exists_positive_euler_twin_without_real_zeros`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/ThePositiveEulerTwinsHaveNoRealZero.lean#L54) |

*Reading.* Each model fails at its own off-line point: q* lies in −½ < Re q < 0 because ‖α‖ > √p. The criterion is equivalent to RH for ζ, so its failure on a model with an off-line zero is that model's failure of its own RH. The model table certifies the criterion as arithmetic in this sense only.

### 2.13 Probe samples

| Result | Lean |
|---|---|
| The samples LF(5 + n) satisfy no finite recurrence, and they determine every profile of H | [`criticalProbeSample_no_recurrence`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProbeSamplesHaveNoFiniteRecurrence.lean#L146), [`criticalProbeSample_eq_iff_ae`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProbeSamplesHaveNoFiniteRecurrence.lean#L165) |

### 2.14 What the proved layer says

*Reading.*

- Every proved property is compatible with the existence of the state. Each is a theorem about a hypothetical object.
- Arithmetic enters at four places: the Euler product through ζ'/ζ (residue transport); ζ ≠ 0 on (½, 1) (sign law, continuation along the real axis); Λ(n) in the prime heads (criterion); the zero-free half-plane Re s > 20999/24000 (averaged decay rate).
- The README separates soft properties (holding for the state of every symmetric zero configuration) from arithmetic ones (failing on a named model). In Lean only the criterion has a model table (§2.12); no Lean construction of model states exists (E-J8), so no other property is classified in Lean.
- Every decay result is a ruler: rate b gives the zero-free half-plane Re s > (17 − b)/2. Decay moves the width (family P), not RH.

## 3. Supporting machinery that ECS uses

| Neighbour | What ECS takes from it |
|---|---|
| ArithmeticHodgeTheoryOfDegenerations | Stage 0: the energy domain and the forms, the window threshold, the state, its weak equation, uniqueness, zero-free transform, exponential barriers, Lévy energy, Gamma contractions, terminal support, energy gap, causal translation, variational compactness |
| CriticalArithmeticCorrelationTheory | The Gamma, prime and pole mixed forms; L¹ limits upgraded to strong limits under bounded Weil energy |
| RHTower | Partial fractions of ξ'/ξ (`XiExplicitFormulaLogDeriv`), the two-channel resolvent kernel (`XiWeilTwoChannelResolvent`), Poisson–digamma reproduction, the Landau abscissa calculus (`LaplaceTransformMomentDerivative`), residues of ζ'/ζ (`Sieve/ZetaPoleLogDeriv`), zero-freeness on Re s = 1 (`ZetaMultipleLandauZeroFree`), Γℝ bounds, infinitely many zeros, the Volterra–Laplace calculus (`CCM/CCMUnitRieszVolterraLaplace`), L² translation continuity (`ConnesConvolutionKernelField`) |
| HTGeometry | Hardy boundary values on the half-line and the disc, half-line Laplace–Fourier inversion, vertical line shifts on decaying strips, the entire divided-difference contour, Carleman and Schur kernel bounds, digamma asymptotics, transforms of compact tests, real Taylor coefficients, cumulative Laplace bounds |
| AbsoluteGeometryOfSpecZ | Two vertical lines weigh the zeros of a function of order one |
| MetaplecticMobiusDescent | The zero-free half-plane Re s > 20999/24000 ([`riemannZeta_ne_zero_of_sub_seven_eighths_lt_re`](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147)) |
| BlackHoleRingdown, SelbergClass | Passivity of the positive twins; signs of positive finite Euler logarithms |
| HilbertMetric, BiScaleUncertainty | Symmetrized Bregman dissipation; the bounded-coordinate sign cone |

## 4. Obstacles that are just work

Each item lists what is to be proved, the Lean pieces, the missing step and what it gives.

### E-J1. The exact index law

**Statement.** Let ind(R) be the largest dimension of a space of smooth compactly supported half-line tests on which Q_R is negative definite. Then ind is finite and nondecreasing in R, ind(R) tends to the number of zeros right of the line (as a set) when R → ∞, and the critical ratios, each counted with the dimension of its null space, are as many as these zeros.

**Lean pieces.** Finite index at every ratio ([`exists_bound_orthonormal_nonpositive`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheConfinedFormHasFiniteIndexAtEveryRatio.lean#L98); it bounds orthonormal families of tests on which Q_R ≤ 0, so it bounds ind(R)). a(R) is a constant divided by R and W₈ ≥ 0, so ind increases with R and is bounded by the index of the bare form. The index of Weil's form on translates of one real test is the number of right zeros it sees ([`zeta_orientationIndex_law`](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationIndexOfACycle.lean#L154)), and the cubic spline sees all of them ([`seenRightZeros_cubicSpline`](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheSplineOrbitDecidesTheCriticalLine.lean#L155)); the general count is [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490) with [`temperedConfig_zeta`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/FarZerosAreFaintInTheLocalCamera.lean#L302), and [`negIndex_weilGram_le_offLineCount`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticHodgeIndexSignatureLaw.lean#L235) gives the upper bound. Weil's form is translation invariant, so finitely many compactly supported tests move jointly into u < 0. The index is 0 or at least 2 ([`negIndex_zetaKernel_le_one_iff`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L75)).

**Missing.** One lemma identifying ECS's bare form with the Weil Gram matrix on smooth half-line tests; min–max branches of the pencil Q_R for exactness at a jump (E-T1).

**Gives.** Off RH there are at least two critical ratios W₀ < R₂ (index ≥ 2, and the null space at W₀ is one-dimensional by uniqueness). There are finitely many critical ratios exactly when finitely many zeros lie off the line ([`zetaKernel_finiteIndex_tfae`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L104)). Stage 2 becomes a statement about finitely many critical states.

### E-J2. Higher critical states

**Statement.** At each critical ratio R_k the confined form has a null vector F_k, and every ECS theorem whose proof uses only membership in H and the weak equation holds for F_k with a_k = a(R_k): the state equation, the continuation and residues, the explicit formula, (★), the zero-side identities.

**Missing.** Existence of the null vectors (the confinement compactness of the ground state, applied in the min–max setting) and a restatement of the ECS theorems for any null vector of a confined form. Zero-freeness of LF_k on Re w ≥ 0 and uniqueness do not transfer; they come from ground-state arguments.

**Gives** (*reading*). Two critical states with a_j ≠ a_k are orthogonal for W₈ and for B: B(F_j, F_k) = −a_jW₈(F_j, F_k) = −a_kW₈(F_j, F_k). Their zero-value vectors are β-orthogonal and each is β-negative. Under a finite layer with N right zeros, the on-line part of β is nonnegative, so the N states project to an N-dimensional negative subspace of β on the 2N off-line coordinates. There β pairs each right zero with its reflection, and N is the largest dimension of a negative subspace. This is the finite-dimensional form of stage 2.

### E-J3. The zero Parseval identity under a finite layer

**Statement.** If only finitely many zeros lie off the line, then Σ_(on-line) abs LF(iγ)² < ∞ and

  Σ_(on-line) abs LF(iγ)² + Σ_(off-line) LF(z)LF(−z) = −a∫F²e^(−8u).

**Lean pieces.** [`criticalState_tendsto_zeroNorm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L755); for real F, LF(−iγ) is the conjugate of LF(iγ), so the on-line terms e^(−εγ²)·abs LF(iγ)² are nonnegative and increase as ε ↓ 0; monotone convergence; the off-line sum is finite.

**Gives.** Square-summability of the zero values on the line (asked for in general by the README) under the stage-2 hypothesis, and the off-line block carries the whole negative mass: Re Σ_(off-line) LF(z)LF(−z) ≤ −a∫F²e^(−8u).

### E-J4. The zero pairing of two general profiles

The state is paired with every profile ([`criticalState_tendsto_zeroPairing`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L699)). For two arbitrary profiles F, G of H the identity W(F, G) = lim Σ_z LF(z)LG(−z)e^(εz²) needs the heated zero series of a general profile; the two-line formula holds for every F in H ([`hasSum_zeroValues_two_lines`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TwoVerticalLinesCutOutTheZeroSeriesOfTheState.lean#L228)), with BF in place of −a·LF(· − 8). This is the remaining case of README Q2 and the same kind of work as the state case.

### E-J5. The probe form of RH and of W₀

**(a)** RH ⇔ the matrices ((D(p_i) + D(p_j))/(p_i + p_j)) are positive semidefinite for every finite set of real p_i > 4, that is, Weil's bare form is nonnegative on the real probe span. Pieces: the probe kernel ([`bareMixedEnergy_probe_eq_criticalLogDerivKernel`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/WeilsFormOnProbesIsTheCaratheodoryKernelOfXi.lean#L271)); a PSD Carathéodory kernel on any node set has an interpolant holomorphic with nonnegative real part on Re p > 0 ([`exists_caratheodory_interpolant`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryNevanlinnaPick.lean#L156)); D is holomorphic on Re p > 8999/24000, so the identity theorem extends D across every zero with Re z > 0, which is impossible at a pole; the converse is [`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel`](../../../formal/GaloisForLFunctions/RHTower/XiEulerSafeCauchyLoss.lean#L220). One assembly.

**(b)** On probes the confined form is (D(p) + D(q))/(p + q) + a(R)/(p + q − 8), and a(R)/(p + q − 8) is the shifted Carathéodory kernel of the constant a(R)/2 ([`isPSDKernel_shiftedCaratheodory`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryKernelPositive.lean#L543)). If the probe span is dense in H for the full energy, W₀ is the first ratio at which these real Pick matrices stop being positive semidefinite, and Galerkin approximation on probe spans converges to F. Missing: the density, a Müntz-type statement with control of the Gamma energy. [`criticalProbeSample_eq_iff_ae`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheProbeSamplesHaveNoFiniteRecurrence.lean#L165) gives injectivity of the sample map, not density in the energy norm.

**Gives.** (a) is an RH-equivalent reformulation, not a door. (b) gives a finite-dimensional, computable approximation of W₀ and F, and places the state in Krein–Langer theory: the negative squares of the probe kernel correspond to the poles of ξ'/ξ(½ + ·) in Re p > 0 (*reading*; the Hecke-orbit form of this count is [`negIndex_zetaKernel`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L52)).

### E-J6. Mode expansions at the rate of the zeros

**(a) The state.** Under a finite layer, shift the averaged inversion line of [`exists_bound_averagedState`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L627) past the finitely many poles right of Re w = −8. The averaged state becomes a finite sum of modes e^(−(8−z)t), with coefficients from the residues −m_ρLF(z)/a, plus O(e^(−(8−ε)t)). Pieces: the averaged line shift, the residue law ([`riemannHypothesis_or_criticalState_meromorphic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheTransformOfTheStateIsMeromorphicInThePlane.lean#L441)), bounds off the zeros ([`norm_globalRemainder_le_of_dist`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheContinuationIsPolynomiallyBoundedOffTheZeros.lean#L49)).

**(b) The prime side.** The same averaging applied to F⁺, whose Laplace transform is the continuation left of the strip, gives growth e^((κ+ε)x) of the averaged prime-side profile when every centred zero has Re z ≤ κ. With the seed this holds for every damping δ > 8999/24000: an averaged sub-strip Hardy wave down to the width.

**Gives.** (a) explains the sign changes of the state mode by mode; (b) is the averaged convergent half of the criterion. Both are rulers and move no wall (E-O4).

### E-J7. The archimedean wall tail as a trivial-zero sum

The Lévy density ω(x) = e^(−x/2)/(1 − e^(−2x)) = Σ_k e^(−(2k+½)x) has its exponential modes at 2k + ½. The first cancels the positive charge; the remaining exponents 2(k+1) + ½ are the reflected centred trivial zeros −σ_k, σ_k = −(2(k+1) + ½) ([`archimedeanWallTail`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L50), [`hasSum_levyHead_resolvents`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean#L90)). SignedWindowCriticality studies the same moments μ_(σ_k)(f) = ∫f e^(−σ_k u) on collars: they determine every collar test ([`eq_zero_of_trivialMoments_eq_zero`](../../../formal/GaloisForLFunctions/SignedWindowCriticality/TheCollarHankelForm.lean#L165)), decay geometrically, and give a Hankel form that is negative definite on the pole hyperplane ([`collarHankel_neg_of_poleMoment_zero`](../../../formal/GaloisForLFunctions/SignedWindowCriticality/TheCollarHankelForm.lean#L218)). The work is to transfer these lemmas to the state's archimedean tail. It gives the archimedean side of the left formula in closed trivial-zero form, and a test of whether the wall balance ([`criticalState_archimedeanWall_asymptotic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheArchimedeanWallMassControlsTheLeftAsymptotic.lean#L196)) has a Hankel sign.

### E-J8. Model states

Construct the confined half-line form and its critical state for models with off-line zeros: a tempered zero configuration, the over-regular Beurling system ([`overRegular_integers_do_not_constrain_zeros`](../../../formal/GaloisForLFunctions/RHTower/BeurlingOverRegularIntegersOffLineZeros.lean#L583)), a positive twin, and a curve configuration with a non-unitary root. The ECS proofs that use only the explicit formula, the Gamma pairing and the confinement transfer; the prime side becomes the model's own. This gives the README's soft/arithmetic classification in Lean, and stage-2, -3 and -4 claims can be tested on models before they are attempted for ζ.

### E-J9. The wall seen from the left

README "to build": the leading asymptotics of JF and ŜF as p → −∞; F⁺ in prime form, that is the remainder of the prime number theorem averaged by F; and its comparison with e^(−8u)F at the wall. Pieces: [`polarWallTerm_eq_continuumMainTerm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L217), [`criticalState_archimedeanWall_asymptotic`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheArchimedeanWallMassControlsTheLeftAsymptotic.lean#L196), the terminal-mass bounds. The leading term depends on F near u = 0, where only averaged bounds are known ([`criticalState_terminal_average_tendsto_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheCriticalStateHasVanishingAverageWallMass.lean#L171)), so the asymptotics may exist only in averaged form.

## 5. Open problems (not just work)

### E-O1. Stage 5: the property that excludes the state

**Statement.** [`ZetaBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L268), or equivalently [`PurePrimeHeadContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L273), or the sub-strip Hardy wave for every profile ([`HasSubstripPrimeHardyWave`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L281)).

**Status.** Equivalent to RH ([`zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L452), [`purePrimeHeadContinuation_iff_zetaBeyondTheWallPrimeContinuation`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L550)). *Reading:* it is the prime number theorem with square-root remainder in F-averaged form (§1.3). No ECS identity bounds the averaged remainder below the width; every bound on it in the corpus is a zero-free half-plane. There is no mechanism.

### E-O2. Stage 2: a finite layer

**Statement.** If only finitely many zeros lie off the line, no critical state exists. This is B13 (FiniteOffLine → RH), open and weaker than RH; B13 ⇔ the thick-lag bound under a finite layer ([`b13_iff_thick_lag_bounded`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheCrudeStepAndTheCount.lean#L242)).

**Walls.**

- A finite layer is Lindelöf-deep: a Weil kernel of finite index forces the Lindelöf hypothesis ([`lindelof_of_negIndex_zetaKernel_lt_top`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L119)). Proving that the layer is finite needs Lindelöf-strength input; stage 2 only asks to exclude it.
- A finite layer occurs in a model with nonnegative prime density: the over-regular Beurling system has finitely many zeros, one off-line pair, nonnegative prime and integer densities and an integer count with error tending to a constant ([`overRegular_integers_do_not_constrain_zeros`](../../../formal/GaloisForLFunctions/RHTower/BeurlingOverRegularIntegersOffLineZeros.lean#L583)). It has no functional equation. A proof of stage 2 has to use the exact functional equation.

**ECS form.** With E-J1–E-J3: N critical states, a finite indefinite block of zero values, a square-summable on-line block and the Parseval identity. A contradiction has to come from F⁺ being the prime heads of F and from the functional equation in Lévy form ([`levyGamma_eq_reflected_euler`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheGammaPairingIsTheFunctionalEquationOnTheStrip.lean#L504)).

### E-O3. Stage 4: Euler-log positivity

**Statement sought.** An identity of the state in which Λ ≥ 0 enters with a definite sign and contradicts the existence of F.

**What the corpus fixes.**

| Model | Exact functional equation | Λ ≥ 0 (nonnegative Euler logarithm) | Off-line zero | Lean |
|---|---|---|---|---|
| Positive Euler twins | yes | no | yes | [`exists_positive_euler_twin_without_real_zeros`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Models/ThePositiveEulerTwinsHaveNoRealZero.lean#L54) |
| Over-regular Beurling system | no | yes | yes | [`overRegular_integers_do_not_constrain_zeros`](../../../formal/GaloisForLFunctions/RHTower/BeurlingOverRegularIntegersOffLineZeros.lean#L583) |
| Beurling systems with the functional equation up to an L² defect | yes | yes | — | only ζ: [`beurlingSystem_rigidity_of_finiteEnergy_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/FiniteEnergyFunctionalEquationsDetermineThePrimes.lean#L171) |
| Finite rational Euler edits of ζ with an entire reflected completion | yes (by hypothesis) | only the trivial edit | — | [`not_exists_nontrivial_positive_finite_rational_twin`](../../../formal/GaloisForLFunctions/SelbergClass/FinitePrimeRationalEulerRigidity.lean#L197) |

*Reading.* An argument that uses both Λ ≥ 0 and the exact functional equation is an argument about ζ alone; the model test of stage 4 is passed only in the weak sense that every model lacks one of the two inputs. In the state equation Λ multiplies signed objects: the state changes sign on every ray, and the prime tail TF(p) and the prime heads ŜF(p) have no sign. The only definite signs in Lean are those of LF on (0, ∞) and of the archimedean modes ([`criticalState_resolvent_tail_half_re_pos`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean#L203)). No identity combining them with Λ ≥ 0 is known.

### E-O4. The decay side (off the RH path)

**(a) The unaveraged convergent half of the decay law** (README Q4): ∫F²e^(−bu) < ∞ for every b < 16 − 2κ when every centred zero has Re z ≤ κ. The averaged form is proved ([`exists_bound_averagedState`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheAveragedStateDecaysAtTheRateOfTheZeros.lean#L627)); the raw continuation does not decay on vertical lines (*readme*). *Reading:* by Paley–Wiener it needs square-integrable vertical traces of the continuation on κ − 8 < Re w < −4, that is L² bounds on vertical lines for Σ_z LF(z)/(w + 8 − z). With zeros of local density log T this asks for Σ_z abs LF(z)²·(number of zeros within distance 1 of z) < ∞, a regularity property of the state that ECS does not have (E-T4).

**(b) Decay is a ruler.** Rate b gives Re ρ ≤ (17 − b)/2 ([`criticalState_not_integrable_of_zero`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheDecayOfTheStateReadsTheZeros.lean#L316)); the barrier comparison absorbs exactly up to 15/2 ([`exponentialBarrier_forcingDominance_iff`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/SharpExponentialBarrier.lean#L33)); a decay improvement is a zero-free half-plane and meets the twin wall, because the multiplicative twins realize every abscissa ≥ Θ ([`wall_eq_seed_of_zetaTwins`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMultiplicativeTwinsRealizeEveryAbscissaAboveTheZeros.lean#L125)). Solving (a) moves no wall.

### E-O5. Stage 3: the collar

On −log 2 < u < 0 a test G meets no forward prime translate of F, and on windows of this length Weil's form is nonnegative: the window threshold is ⊤ up to twice the enlarged floor aperture, which exceeds log 2 ([`windowThreshold_eq_top_of_le_enlarged`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L77)), and windows shorter than log 2 + 1/50 carry at most one negative square ([`not_negative_plane`](../../../formal/GaloisForLFunctions/CohomologyOfWindowsOfSpecZ/ShortWindowsCarryAtMostOneNegativeSquare.lean#L92)). Whether the weak equation restricted to collar tests constrains the seen left zeros beyond (★) is open; there is no mechanism. Beyond the wall the situation is reversed: on 0 < x < log 2 every prime enters F⁺.

## 6. Questions

Tests: T1 not RH-equivalent; T2 answerable only by proof or refutation; T3 a written consequence; T4 not decided by a finite window; T5 false on at least one corpus fake; T6 a named input not refuted in Lean; T7 not a shape already answered in Lean without moving a wall.

| ID | Question | First lemma | Consequence | Tests |
|---|---|---|---|---|
| E-Q1 | Does Φ_F continue to Re p < 0 for every F in H? | — | RH | fails T1: the target, not a door |
| E-Q2 | Under a finite layer, do the N critical states (E-J2), the Parseval identity (E-J3) and the identity "F⁺ = prime heads of F" force N = 0? | E-J1–E-J3; then (★) on the off-line block for each F_k, with the Lévy functional equation | B13 in ECS coordinates; with [`b13_iff_thick_lag_bounded`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheCrudeStepAndTheCount.lean#L242) the thick-lag bound under a finite layer | passes T1–T7: weaker than RH; the analogous statement is false for the over-regular Beurling system (finite layer, Λ ≥ 0); named inputs the Lévy functional equation and [`beurlingSystem_rigidity_of_finiteEnergy_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/FiniteEnergyFunctionalEquationsDetermineThePrimes.lean#L171); not answered |
| E-Q3 | For a curve configuration with a non-unitary Frobenius root, what is the critical state, and which ECS identity does the Hodge-index statement (unitary roots ⇔ zero negative index, [`curve_hodgeIndex_tfae`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurfaceOfACurve.lean#L345)) violate for a genuine curve? Same question for the native Stepanov proof ([`riemannHypothesis_cubicCharacter`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAcidTestPassesForCubicCharacters.lean#L272)). | E-J8 for curve configurations | a stage-5 template: the ECS identity at which a proved positivity excludes the state | passes T1–T7: RH is a theorem there; a fake curve has right zeros, hence negative squares ([`curve_hodgeIndex_tfae`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurfaceOfACurve.lean#L345)); named inputs in Lean; not answered |
| E-Q4 | Does the weak equation on tests supported in (−log 2, 0), where Weil's form is nonnegative and only backward prime translates enter, constrain the zero values LF(z) at the left zeros beyond (★)? | write W(F, G) for collar tests G by its zero side ([`criticalState_tendsto_zeroPairing`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing.lean#L699)) and by its prime coordinates | a collar inequality on left zero values, or the theorem that the collar is soft | passes T1–T4, T6, T7; T5 is unchecked until model states exist (E-J8) |
| E-Q5 | If F(u)e^(−8u) is subexponential along a thick set of u → −∞, does AAL follow? The heated zero series is a lag function weighted by the zero values (§2.5), and every right zero is seen. | transfer [`asymptoticAbscissaLaw_of_thick_lag_bound`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheTowersOfZeta.lean#L194) to lag functions with nonvanishing weights | an ECS receiver for AAL | passes T1 (AAL is weaker than RH, [`riemannHypothesis_tfae`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheInfiniteRankWeilProof.lean#L64)), T2–T4, T6, T7; T5 expected but unproved; a translation that moves no wall |

E-Q2 and E-Q3 pass every test. None of the questions that pass every test implies RH.

## 7. Mathematical tools to develop

| ID | Tool | Needed for | Seeds in the corpus |
|---|---|---|---|
| E-T1 | Spectral calculus of the confined pencil Q_R = B + a(R)W₈: min–max eigen-branches, their monotonicity in R, null vectors at every critical ratio, multiplicity at a jump | E-J1, E-J2, E-Q2 | finite index ([`exists_bound_orthonormal_nonpositive`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheConfinedFormHasFiniteIndexAtEveryRatio.lean#L98)); ground-energy derivative and strict concavity ([`hasDerivAt_criticalHalfLineGroundEnergy`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningGlobalTransverseGapAndResponse.lean#L399), [`confiningHalfLineGroundEnergy_strict_jensen`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningHalfLineGroundEnergyCurvature.lean#L45)) |
| E-T2 | Model-state calculus: the confined half-line form and its critical state for a tempered zero configuration with its own prime side (Beurling systems, finite Euler edits, positive twins, curve configurations) | E-J8, E-Q3, E-Q4, the soft/arithmetic test of every stage | [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490) for tempered configurations; [`curve_hodgeIndex_tfae`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurfaceOfACurve.lean#L345); the model families of §2.12 and E-O3 |
| E-T3 | Pick calculus on real nodes: Krein–Langer for Carathéodory kernels with poles in the right half-plane, shifted kernels for the confinement, Schur steps on probe nodes | E-J5 | [`exists_caratheodory_interpolant`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryNevanlinnaPick.lean#L156), [`isPSDKernel_shiftedCaratheodory`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryKernelPositive.lean#L543), [`ne_zero_of_isPSDKernel_caratheodory`](../../../formal/GaloisForLFunctions/RHTower/XiShiftLoewnerCriticalGenerator.lean#L63), [`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel`](../../../formal/GaloisForLFunctions/RHTower/XiEulerSafeCauchyLoss.lean#L220) |
| E-T4 | Sampling and Hilbert-type inequalities on the zero set: Σ_z abs LF(z)²·(local zero count) from regularity of the state, and L² bounds for Σ_z c_z/(w − z) on vertical lines without a separation hypothesis | E-O4(a), square-integrable mode expansions | the zero-sum calculus of ECS ([`norm_globalRemainder_le_of_dist`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheContinuationIsPolynomiallyBoundedOffTheZeros.lean#L49)); E-J3 under a finite layer |
| E-T5 | Calculus of the F-averaged prime number theorem: F⁺ in prime form, its size and its sign as ∫_(x>v) F(v−x)e^(−x/2)d(ψ(e^x) − e^x) | E-J9, E-O1 | [`polarWallTerm_eq_continuumMainTerm`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheBeyondTheWallPrimeBalanceExcludesTheState.lean#L217), [`criticalState_prime_wave_changes_sign_on_every_ray`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/ThePrimeSideChangesSignOnEveryRay.lean#L411) |
| E-T6 | A sign mechanism: an identity of the state in which Λ ≥ 0 and the exact functional equation both enter with a definite sign | E-O3, E-O1 | none in the corpus; §2.8 lists the signs that exist |

## 8. Missed connections: corpus results that ECS does not use

ECS imports none of the modules below (import list of the folder).

| ID | Corpus result | Connection to ECS | Use |
|---|---|---|---|
| E-M1 | Index laws: [`pontryagin_law`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean#L490), [`temperedConfig_zeta`](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/FarZerosAreFaintInTheLocalCamera.lean#L302), [`zeta_orientationIndex_law`](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationIndexOfACycle.lean#L154), [`negIndex_zetaKernel`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L52), [`zetaKernel_finiteIndex_tfae`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L104), [`lindelof_of_negIndex_zetaKernel_lt_top`](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean#L119) | The negative squares of Weil's form are the right zeros; ECS proves finiteness of the index of the confined form at each ratio but not its value | the exact index law (E-J1); the Lindelöf wall of stage 2 (E-O2) |
| E-M2 | Carathéodory–Pick: [`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel`](../../../formal/GaloisForLFunctions/RHTower/XiEulerSafeCauchyLoss.lean#L220), [`exists_caratheodory_interpolant`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryNevanlinnaPick.lean#L156), [`isPSDKernel_shiftedCaratheodory`](../../../formal/GaloisForLFunctions/HTGeometry/CaratheodoryKernelPositive.lean#L543) | ECS proves that Weil's form on probes is the Carathéodory kernel of ξ'/ξ; the corpus has the positivity criterion and the interpolation theorem for that kernel | the probe form of RH and of W₀ (E-J5) |
| E-M3 | The Markov–pole split: [`weilQuad_eq_markov_add_pole`](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleHyperplaneIsTheHarmonicHyperplane.lean#L91), [`riemannHypothesis_iff_not_exists_negDef_markovPlane`](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovOneBoundState.lean#L539), [`riemannHypothesis_iff_forall_exp_half_moment_zero_markovEnergy_nonneg`](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovOnePoleHyperplane.lean#L105) | On the charge hyperplane LF(½) = 0 the pole term vanishes and the full energy is Markov energy + a·W₈; ECS's charge-zero coercivity ([`criticalState_charge_zero_coercivity`](../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Energy/PolarChargeCoercivity.lean#L175)) is the confined half-line form of the one-pole-hyperplane criterion, and its modulus defect is the half-line form of the Markov property (*reading*) | a quantitative half-line version of the one-bound-state law: off RH the Markov energy is negative somewhere on the hyperplane, and ECS bounds it below by −(a − γ)W₈ there |
| E-M4 | Short windows: [`windowThreshold_eq_top_of_le_enlarged`](../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean#L77), [`not_negative_plane`](../../../formal/GaloisForLFunctions/CohomologyOfWindowsOfSpecZ/ShortWindowsCarryAtMostOneNegativeSquare.lean#L92); the Green calculus of the prime-free window ([GreenCalculusOfThePrimeFreeWindow](../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow.lean)) | The collar −log 2 < u < 0 is a window on which Weil's form is nonnegative | the collar stage (E-O5, E-Q4) |
| E-M5 | The collar Hankel calculus of SignedWindowCriticality: [`eq_zero_of_trivialMoments_eq_zero`](../../../formal/GaloisForLFunctions/SignedWindowCriticality/TheCollarHankelForm.lean#L165), [`collarHankel_neg_of_poleMoment_zero`](../../../formal/GaloisForLFunctions/SignedWindowCriticality/TheCollarHankelForm.lean#L218) | Its trivial-zero moments are the coefficients of ECS's archimedean wall tail | E-J7 |
| E-M6 | The model table: [`beurlingSystem_rigidity_of_finiteEnergy_defect`](../../../formal/GaloisForLFunctions/EulerFETransportTheory/FiniteEnergyFunctionalEquationsDetermineThePrimes.lean#L171), [`overRegular_integers_do_not_constrain_zeros`](../../../formal/GaloisForLFunctions/RHTower/BeurlingOverRegularIntegersOffLineZeros.lean#L583), [`not_exists_nontrivial_positive_finite_rational_twin`](../../../formal/GaloisForLFunctions/SelbergClass/FinitePrimeRationalEulerRigidity.lean#L197) | ECS's model file covers prime-two deformations and positive twins; the Beurling model with Λ ≥ 0 and the functional-equation rigidity are absent | E-O2, E-O3; the models of E-J8 |
| E-M7 | Thick-lag receivers: [`b13_iff_thick_lag_bounded`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheCrudeStepAndTheCount.lean#L242), [`asymptoticAbscissaLaw_of_thick_lag_bound`](../../../formal/GaloisForLFunctions/InfiniteRankWeilTheory/TheTowersOfZeta.lean#L194) | The heated zero series of the state is a lag function weighted by the zero values, and its growth is the decay of the state (*reading*) | stage 2 in thick-lag form (E-O2); E-Q5 |
| E-M8 | Function-field RH in Lean: [`curve_hodgeIndex_tfae`](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurfaceOfACurve.lean#L345), [`riemannHypothesis_cubicCharacter`](../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheAcidTestPassesForCubicCharacters.lean#L272) | A calibration in which the state is excluded by a proved positivity | E-Q3 |
| E-M9 | Ringdown: [`not_thetaCuspHawkingEKGUniversalFiniteQNMOnlyComplete`](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingEKGContinuumQNMOnlyCompletenessNoGo.lean#L113) | ECS proves the mode expansion of the state, Σ_z LF(z)e^(−zu), in heated and smooth-test form; the theta-cusp model shows that finite mode sets are incomplete there | a caution for any L² completeness claim for the modes of the state (the quasinormal question of obstacles summary §2.7) |

## 9. The route in one paragraph

*Reading.* ECS has reduced RH to the non-existence of one function and made the reduction exact: the state's transform is meromorphic with the zeros as poles, the state is the Cauchy transform of its zero values, and its zero values form a negative vector of the zero pairing. Its decay, sign, index and energy laws are theorems, and all of them are compatible with the existence of the state. The last step is the F-averaged prime number theorem with square-root remainder (E-O1); the route has no mechanism for it. The concrete openings are the finite-dimensional form of stage 2 (E-J1–E-J3, E-Q2), a calibration in function fields where the exclusion is a theorem (E-Q3), and model states that separate soft from arithmetic properties (E-J8). Stage 4 has a fixed shape: it must use Λ ≥ 0 and the exact functional equation together, and the corpus shows that among Beurling systems only ζ has both (E-O3).
