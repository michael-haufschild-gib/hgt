# 39 SignedArithmeticHodgeTheory — mathematical facts log

Programme builds on AID's fixed integer-log carrier `closedFixedLogCellGraph` and its Weil projection P (`fixedLogCellWeilProjection`), A = graphWeilOperator, source graph = CHMD complete source graph.

## TheArithmeticSchurComplementHasCertifiedErrorBounds
- arithmeticResidual = id − P; arithmeticStationarity D = orthogonal projection onto carrier ∘ A; ⟨Dx, u⟩ = W(x,u) for u in carrier.
- W(Px) ≤ 2‖Dx‖², ‖Px‖ ≤ 2‖Dx‖ (only the carrier restriction of A is charged).
- Trial correction u in carrier: W(x − u) = W(res x) + W(Px − u) (exact); interval W(x−u) − 2‖D(x−u)‖² ≤ W(res x) ≤ W(x−u) − ½‖Px − u‖²; graph error ‖Px − u‖ ≤ 2‖D(x−u)‖; equality iff u = Px (unique minimizer on affine fibre).
- Mixed: |W(x−u, y−v) − W(res x, res y)| ≤ 2‖D(x−u)‖‖D(y−v)‖.

## OneStationarityBudgetControlsTheWholeSourceFamily
- Family F: E → graph, trial U: E → carrier; familyStationarity = D∘(F − U).
- 0 ≤ W(Fc − Uc) − W(res Fc) ≤ 2‖familyStationarity‖²‖c‖²; graph error ≤ 2‖·‖‖c‖; all mixed entries ≤ 2‖·‖²‖c‖‖d‖ (one operator budget, no entrywise charge).

## TheSignedComplementRetainsExactlyTheWeilRadical
- arithmeticComplement = ker P; arithmeticWeilRadical = ker A. Residuals lie in complement; D x = 0 ⇔ x ∈ complement.
- Radical ⊆ complement; r in complement is W-null against the complement ⇔ r ∈ radical (no new radical created).
- P(x + z) = Px, res(x + z) = res x + z for z in radical.
- exists_infinite_arithmeticWeilRadical: theta family (CHMDThetaTranslate.sequence) linearly independent, in radical, fixed by residual.

## TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound (uses ACS TheLambdaRingOfTheScalingSurface; RHTower WeilMarginSuperexponentialLaw)
- sourceTranslate: W(translated) = W(f) (full Weil form incl. Gamma, poles translation invariant).
- Riemann theta kernel decays faster than every exponential ⇒ sourceGraphMassWeight = cosh(u/2)/K(u) ≥ e^{B|u|}/K_B for every B.
- translatedSourceGraph_all_exponential_lower_bounds: f ≠ 0 ⇒ ‖lift(f translated by t)‖² ≥ c e^{B|t|} for every B (graph norm superexponential along orbit at constant Weil energy).
- ‖x‖² ≤ 4W(x) + (4C_W + 2)‖res x‖²: escape persists in the arithmetic residual.
- Scalar renormalization: energy/graph ratio decays exponentially; any exponential amplitude e^{−a|t|} still escapes at rate e^{|t|}.
- Every translated nonzero orbit eventually leaves the coercive carrier.

## BoundedWindowsAdmitSourceCompatibleScaleTransport
- ∫f² ≤ K‖lift f‖² globally (B = 0 weight bound).
- exists_boundedWindow_scaleTransport: support radius R, |t| ≤ T ⇒ ‖lift(translate_t f)‖² ≤ C(R,T)‖lift f‖² (constant = sup of theta mass weight on enlarged window; not uniform under exhaustion). Two-sided version (inverse translation).

## CompletedAperturesCarryTheLiteralScaleTransport (uses RHTower CHMDFixedApertureQuotientLanding, CHMDShiftedFourierReadout)
- apertureScaleTransport a t: continuous extension of translation from smooth aperture cores to the completed aperture graph space (apertureGraphCompletion).
- Preserves weilForm and every mixed weilBilin; two-sided norm bounds for |t| ≤ T; injective; lands in completion of enlarged aperture a + |t|.
- Strip Fourier readouts (|Im z| ≤ 1/2, incl. both poles) pick up exactly e^{izt}.

## GrowingRamanujanFamiliesHaveAUniformGramBudget (uses RAPT TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal; HTGeometry ShiftPartialSummation)
- Periodic p with period q: |Σ_{n≤N} p(n)/n − mean(p)·H_N| ≤ Σ_{i<q}|p(i+1) − mean| (Abel summation, harmonic increments telescope to 1).
- ramanujanPoleProfile_gram_error_le: |Σ_{n≤N} ρ_m(n)ρ_l(n) − δ_{ml}H_N| ≤ 2ml, uniform in N.
- Family: |Σ_n(Σ_m c_mρ_m(n))² − H_N Σc_m²| ≤ 2(Σ_{m∈S} m²)Σc_m²; with |H_N − log N| ≤ 1: |… − log N·Σc²| ≤ (1 + 2Σm²)Σc² (explicit conductor cost).

## TheRamanujanCorrectionHasAnExplicitConductorCost (uses RAPT TheRamanujanPoleProfilesArePrimeQuasimodes)
- localMangoldtTail(p,y) = reciprocal Mangoldt mass on the p-tower beyond y ≤ (log p/(p−1))/p^K for p^K ≤ y, hence ≤ 2 log p / y.
- ramanujanCorrectionTail(m,y) = 2φ(m)Σ_{p|m} localTail ≤ 4φ(m)log m / y (Σ_{p|m} log p ≤ log m).
- Normalized row correction: |poleProfileCorrection(ρ̃_m, y, n) + (log m + tameDifferent m)ρ̃_m(n)| ≤ 4√φ(m) log m / y, uniform in row n.

## OneArithmeticRemainderControlsEveryRamanujanResidual (uses ArithmeticEffectivityTheory, ArithmeticIntersectionTheory)
- |ρ̃_m(n)| ≤ √φ(m) (complete-period normalization).
- primeMertensRemainderProfile(y) = |Mertens sum − log y + γ| + 1/y; conductor cost √φ(m)(1 + 4 log m).
- ramanujanPrimeResidual(m,N,n) = Σ_{j≤N} weilPrimeKernel(n,j)ρ_m(j) − (log N − adjunction energy(m))ρ_m(n): |·| ≤ cost(m)·profile(⌊N/n⌋)/√n (one Mertens/floor remainder for all conductors and rows).
- Family: Σ_n(Σ c_m residual)² ≤ Σc²·Σcost²·primeMertensSquareBudget(N), budget = Σ_n profile(⌊N/n⌋)²/n; profile → 0; budget/log N → 0.

## TheArithmeticResidualBudgetIsUniformInTheHorizon (uses RHTower MertensConstantAndCesaroIntegerLagBridge; PNTPlus Wiener)
- Mertens deviation ≤ A e^{−c√log y} ⇒ profile(y) ≤ C/(1 + log y) globally.
- Floor/log kernel comparison; Wiener kernel Σ_{n≤N}(1/n)(1 + (log(n/N)/2π)²)^{−1} ≤ 1 + 2π² (PNT+ library).
- exists_uniform_primeMertensSquareBudget: budget ≤ B for all N. exists_uniform_ramanujanPrimeResidual_family_bound: Σ_n(Σ c_m residual)² ≤ B·Σcost²·Σc², uniform in horizon, conductors, coefficients.

## RamanujanFamiliesHaveAnExplicitLocalCaptureCost
- ρ_m(n)² ≤ φ(m)/n; local mass on [1,L] ≤ H_L·Σφ(m)·Σc².
- Capture bound: (log N − (1 + 2Σm²))·local ≤ H_L·Σφ·global; above threshold local fraction ≤ H_LΣφ/(log N − D).
- eventually_ramanujanPoleProfile_family_local_mass_le: fixed finite modal span loses its normalized mass on every fixed window (local ≤ ε·global for large N, uniform in coefficients).

## BoundedPrimeEnergyEscapesEveryFixedIntegerWindow (uses RAPT TheRenormalizedPrimeEnergyControlsTheDefect)
- primeHorizonWindowMass L x = Σ_{n≤L} x_n²; ≤ ‖x‖²; ≤ 2‖x − v‖² + 2·window(v).
- eventually_primeHorizonWindowMass_le_of_energy_le: unit vectors with renormalizedPrimeEnergy ≤ T lose all mass on any fixed integer window [1,L] as N → ∞ (finite Ramanujan approximation of sublevels + local capture). Literal integer-coordinate norm.

## TheLogCellClockHasACompleteWanderingDecomposition (uses RHTower ThetaEulerLogCellResidueChannels)
- Weighted dyadic cell shift W = logCellShift 2 on ℓ²(ℕ+): isometry; W^j range vanishes on coordinates < 2^j ⇒ ⋂ ranges = 0 (pure isometry, no unitary part).
- Wandering space = (range W)^⊥; W^j(wandering) mutually orthogonal; orthogonal to all levels ⇒ 0; levels span dense (Wold decomposition).
- logCellEmbedding ∘ W^j = (half-line right shift by log 2)^j ∘ embedding (clock = literal log-2 translation).

## BalancedCellDetailsFormTheWanderingBasis
- Children 2a, 2a+1; weights √(logCell(2a)/logCell(a)), √(logCell(2a+1)/logCell(a)), squares sum to 1.
- W e_a = left·e_{2a} + right·e_{2a+1} (coarse direction); balanced detail = right·e_{2a} − left·e_{2a+1} ∈ wandering; unit, orthogonal.
- First cell e_1 ∈ wandering; {e_1} ∪ {details} orthonormal and total ⇒ logCellDyadicWanderingBasis: Hilbert basis indexed by Option ℕ+.

## EveryFiniteCellSourceHasFiniteDyadicCoordinates
- logCellDyadicOrbit (j, i) = W^j(generator i). Inverse rotation: e_{2a} = left·We_a + right·detail_a, e_{2a+1} = right·We_a − left·detail_a.
- Strong induction: every cell e_m lies in the finite span of orbits; finite cell sources have finite dyadic expansions.
- Orbits orthonormal and dense ⇒ logCellDyadicBasis (ℕ × Option ℕ+); logCellDyadicCoordinates: isometric isomorphism ℓ²(ℕ+) ≅ ℓ²(ℕ × Option ℕ+) (no quotient); coordinate = ⟨orbit, x⟩.

## TheDyadicDetailsAreTheLiteralBalancedHaarSources (uses ACS HaarCellPrimeCompression)
- logCellEmbedding(√logCell(a)·e_a) = cellAtom a (physical cell).
- √haarMass(a)·embedding(detail_a) = haarAtom a exactly; commutes with dyadic levels ((log 2 shift)^j) and every integer translation T_{log p}.

## ArithmeticTranslationsHaveAnExactDyadicLevelMatrix
- logCellShift p commutes with W (logCellShift_comp: shifts multiply).
- Level matrix of T_p in dyadic coordinates: ⟨W^j u, T_p W^k v⟩ = [k ≤ j]·⟨W^{j−k}u, T_p v⟩ (lower triangular, Toeplitz in level).
- W kills level-0 coordinates and advances level j → j+1 (prime two = exact unilateral shift on each generator chain).

## TheSiblingGammaChargePaysItsParentVariance (uses ACS IntervalVarianceRemainder, CompleteCellVariancePayment; SSHA TheSelfEnergyOfAnAtomHasConstantOne)
- Var[a,c] = Var[a,b] + Var[b,c] + ((b−a)(c−b)/(c−a))(mean_l − mean_r)² (exact).
- sibling_gamma_ge_parent_variance: width ≤ 1 ⇒ (min child width/(2·width))·Var(parent) ≤ ∫∫_{left×right} gammaDifference (ω ≥ 1/(2·width) on short spans).
- Log sibling pair (translated by any t): each child ≥ parent width/4 ⇒ Var(parent)/8 ≤ sibling Gamma rectangle; holds for complete cell profiles with arbitrary means.

## OneGammaReservePaysAllDyadicParentVariances (uses HTGeometry DyadicSiblingPartition; RHTower LogFloorExpBridge)
- Sibling rectangle at level j, label a, translation t: (left child) × (right child) of parent [t + j log2 + log 2a, t + j log2 + log(2a+2)).
- Floor labels: ⌊e^{x−t}⌋/2^j = 2a, ⌊e^{y−t}⌋/2^j = 2a+1 determine (j, a) uniquely (DyadicSibling level uniqueness) ⇒ rectangles pairwise disjoint across all levels and labels.
- Σ sibling charges ≤ ∫∫gammaDifference = 2Γ ⇒ sum_logCellDyadicParentVariance_le: Σ_{(j,a)∈S} Var(parent) ≤ 16Γ(f) for every finite S, every translation t, any BV compact f (complete profiles: means free).

## DyadicVarianceSplitsIntoTheLiteralHaarReadout
- logCellHaarReadout(t,(j,a),f) = √haarMass(a)·(mean_left − mean_right); ∫haarProfile_a(x − t − j log2)f = √haarMass·readout.
- readout² = parallel-mass mean term of adjacent variance split; readout² ≤ Var(parent).
- Children of level-(j+1) parent a are level-j parents 2a, 2a+1 ⇒ exact conservation: Var(j+1,a) = Var(j,2a) + Var(j,2a+1) + readout(j+1,a)².

## BinaryVarianceFlowCountsEveryAncestor
- Orbit sums over levels: HaarOrbitEnergy(a) + VarOrbit(2a) + VarOrbit(2a+1) ≤ VarOrbit(a) (binary flow).
- Tail flow lemma: tail_G(M) + tail_F(2M) ≤ tail_F(M); telescoping at powers of 2 ⇒ Σ_a (⌊log₂a⌋+1)·G(a) ≤ tail_F(1) (each ancestor counted, variance spent once).
- sum_logCellAncestorWeight_orbit_le: Σ_a ancestorWeight(a)·HaarOrbitEnergy(a) ≤ 16Γ(f); 1 + log a ≤ 2·ancestorWeight ⇒ Σ(1 + log a)·orbit energy ≤ 32Γ.
- Full ancestor-weighted square function summable: Σ_{(j,a)} ancestorWeight(a)·readout² ≤ 16Γ; Σ(1 + log a)readout² ≤ 32Γ on finite selections (logarithmic Haar square function bounded by Gamma, any translation t).

## HighGeneratorTailsAreSmallAcrossAllLevels (uses HTGeometry LpCoordinateProjection)
- High-label tail summed over all levels: Σ_{a≥A} HaarOrbitEnergy(a) ≤ 32Γ(f)/(1 + log A); same for level-by-generator readouts (cutoff on labels only; every translation level retained).
- logCellHaarAnalysis (square-summable readouts), logCellHaarOrbitHead A (keeps labels < A, all levels); ‖analysis − head‖² ≤ 32Γ/(1 + log A); complete profiles inherit it.

## DyadicHaarCoordinatesReadTheOriginalSource
- wholeLineLogCellEmbedding = half-line extension ∘ logCellEmbedding (isometry); zero extension turns nonnegative half-line shifts into whole-line translates.
- Normalized dyadic detail orbit (j, a) embeds as haarProfile_a(x − j log 2)/√haarMass.
- physicalLogCellCoordinates f (j, some a) = logCellHaarReadout 0 (j,a) f: Hilbert coordinates of the cell component of the actual source are the literal translated Haar readouts.

## CompactDetailsDoNotMakeTranslationOrbitsCompact (uses AID GammaBoundedCompleteProfilesHaveCompactDetails; SSHA TheArchimedeanPairingOfTwoAtoms)
- Each fixed level j: unit-Gamma details have compact envelope (image of AID compact closure under (log-2 shift)^j).
- First Haar atom's dyadic orbit: orthogonal, each mass haarMass(1), pairwise distance² = 2haarMass(1), injective, not totally bounded; every member has the same Gamma energy (translation invariance), BV compact.
- Finite-generator approximation does not give compactness across levels; keep whole translation orbits.

## FiniteGeneratorOrbitsApproximateThePhysicalCellSource (uses ACS SmoothFiniteCellArithmeticForm)
- logCellGeneratorHead A: orthogonal cutoff keeping root and detail labels < A at every level (finitely many generators); fixes retained orbits, kills others.
- Physical cell component of any compact BV source: ‖x − head_A x‖² ≤ 32Γ(f)/(1 + log A).
- Finite cell sources (wholeCellProfile) are fixed by cell projection ⇒ entire finite cell source approximated by finitely many full generator orbits with error 32Γ/(1 + log A).

## GeneratorOrbitCutoffsReduceTheDyadicClock
- Whole-orbit cutoff acts only on generator coordinate ⇒ commutes with W and all W^k; head ⊥ tail for all pairs.
- dyadic_correlation_sub_head: ⟨W^k x, x⟩ − ⟨W^k Hx, Hx⟩ = ⟨W^k(x − Hx), x − Hx⟩ (no mixed correlations); |Re·| ≤ ‖x − Hx‖² uniformly in lag k.
- Original source: ‖x − H_A x‖² ≤ 32Γ(f)/(1 + log A); finite cell sources: every dyadic lag error ≤ 32Γ/(1 + log A).

## OneGammaReserveControlsTheDyadicEulerTail (uses AID TheEntirePrimeTwoEulerMixedSourceIsGammaSmall)
- dyadicEulerCorrelation x = Σ_k primeTwoPowerWeight(k)·Re⟨W^{k+1}x, x⟩; absolutely summable; |·| ≤ total·‖x‖² (total = 2 log2/(√2 − 1)).
- Exact split: Euler(x) − Euler(Hx) = Euler(x − Hx); error ≤ total·‖x − Hx‖² ≤ total·32Γ/(1 + log A).
- logCellShift(2^{k+1}) = W^{k+1}; dyadic Euler correlation = physical prime-2 correlation series on half-line; on finite cell sources = Σ_k w_k ∫F(u)F(u + log 2^{k+1}).
- exists_physicalDyadicEuler_finite_generator_approximation: ∀δ ∃A: finite generator orbits approximate the entire physical prime-2 Euler correlation within δ·Γ (all levels, all horizons).

## EveryTranslationHasAnAllLevelGammaTailBound (uses RHTower CCM CCMRestrictedWeilBoundedRemainder)
- wholeLineGeneratorTail A = U(id − H_A)U*; a tail vector reads only the other source's tail: ⟨Tail F, G⟩ = ⟨Tail F, Tail G⟩.
- ‖Tail(source f)‖² ≤ 32Γ(f)/(1 + log A); |⟨Tail f, g⟩| ≤ 16(Γf + Γg)/(1 + log A) (no coarse norm factor).
- Translation preserves Γ ⇒ |⟨Tail f, T_t f⟩| ≤ 32Γ/(1 + log A) for every real t; adjoint version.
- abs_allLevel_translation_head_error_le: |corr_t(F) − corr_t(F − Tail F)| ≤ 96Γ(f)/(1 + log A) at every real lag t (three payments; no commutation with odd-prime translations assumed).
- Finite cell sources: |∫F(x)F(x+t) − corr_t(head)| ≤ 96Γ/(1 + log A) for all real t.

## FiniteEulerFactorsHaveAllLevelGeneratorApproximation (uses AID EveryFixedEulerMixedSourceIsGammaSmall)
- wholeLinePrimeEulerCorrelation p F = Σ_k w_{p,k}·corr_{log p^{k+1}}(F); absolutely summable; |·| ≤ total_p‖F‖².
- Head error per prime ≤ total_p·96Γ/(1 + log A); on original source = Σ_k w ∫f(x)f(x + log p^{k+1}).
- Finite prime families: error ≤ (Σ_{p∈P} total_p)·96Γ/(1 + log A); ∀δ ∃A: δ·Γ on finite cell sources (no all-prime summability claimed).

## CriticalEulerCoefficientMassStartsAtCubes (uses RHTower RandomEulerAbscissa)
- criticalEulerTailWeight r = 2Λ(p^{k+r+1})/√p^{k+r+1} over all (p, k).
- summable_criticalEulerTailWeight_iff: summable over all primes ⇔ r ≥ 2 (cubes and higher). not_summable_criticalPrimeCoefficients (exponent 1), not_summable_criticalSquareCoefficients (2 log p/p). Concerns coefficient mass only, not correlations or pole cancellation.

## AllHigherPrimePowersHaveAllLevelGeneratorApproximation
- higherEulerCoefficientTotal = Σ over exponents ≥ 3, all primes; wholeLineHigherEulerCorrelation absolutely summable on all of L²; |·| ≤ total‖F‖².
- Head error (full series, Σ of absolute errors, every finite truncation S) ≤ total·96Γ/(1 + log A).
- exists_allPrimeHigherEuler_allLevel_generator_approximation: one cutoff A pays the whole infinite-prime cube-and-higher source and every finite exhaustion stage within δ·Γ, all horizons, all dyadic levels.

## EveryGeneratorCutoffStopsAtAnActualDyadicCell
- H_A fixes cells e_n with n < 2A (strong induction via inverse rotation); keeps/removes unshifted details by label.
- logCellStoppingAncestor A n: ascend n ↦ ⌊n/2⌋ until label < 2A; terminal label in [A, 2A) when n ≥ A; stopping vector W^j e_label (unit, retained by H_A).
- H_A self-adjoint; H_A e_n = ⟨stop_n, e_n⟩·stop_n: projection of each original cell = orthogonal component along its stopping cell (real coefficient).

## GeneratorCutoffsAreLogarithmicBlockAverages
- Stopping label = ⌊n/2^j⌋; all cells in one block (same quotient) share the stopping ancestor.
- W^j e_a = Σ_{r<2^j} √(logCell(a2^j + r)/logCell a)·e_{a2^j + r} (block of original cells).
- Explicit nonnegative block matrix: (H_A e_n)_m = √(ℓ_n/ℓ_a)√(ℓ_m/ℓ_a) on the block, else 0; support < 2n.
- Physical height (coordinate/√ℓ_n) of H_A x = logarithmic-length weighted average of heights over the stopping block (weights ℓ_m/ℓ_a sum to 1); constant on each block. Generator cutoffs are logarithmic block averages.

## ActualGeneratorHeadsPreserveTheSourceMean (uses AID TheCenteredSquareSourceHasAGammaMassBound)
- finiteLogCellProfile n c = Σ c_i·rawCell(n_i) (repeated labels allowed); ∫ = Σ c_i·logCell(n_i); realizes finiteLogCellVector; complete-cell profiles are instances.
- actualGeneratorHeadProfile: stopped labels/heights (cell mass / stopping-block length) = H_A(source) as literal BV compact profile; tail = source − head.
- ∫head = ∫source (block weights sum to 1) ⇒ tail has zero mean; head ⊥ tail in L²; ∫source² = ∫head² + ∫tail².
- Square-prime mixed (source − head − tail) = centred mixed (both corrections cancel); ∫tail² ≤ 32Γ(source)/(1 + log A).
- exists_actualGenerator_square_mixed_bound: |mixed| ≤ ε(Γhead + Γtail) + C·32Γ(source)/(1 + log A).

## TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost
- |centred square source f| ≤ εΓf + C∫f² (diagonal via homogeneity f+f = 2f).
- Tail has zero mean ⇒ square(tail) = centred(tail) + squareRegular(0)∫tail².
- exists_actualGenerator_square_head_bound: |square(source) − square(head)| ≤ ε(Γhead + Γtail) + C·32Γ(source)/(1 + log A). Only Γ of the constructed head and tail remain unpaid (no bound for them assumed).

## ComparableIntervalsHaveComparableGammaKernels (uses ACS GammaExteriorSubsets)
- stoppingGammaKernelConstant = 32e². ω(s) ≤ 7e·ω(t) for s ≤ t ≤ 7s, t − s ≤ 2; 1 ≤ 2e·t·ω(t) for t ≤ 2.
- Separated short intervals with width-scale gap (widths ≤ 3·gap): interval kernel ≤ C·|I||J|ω(far distance). Comparable touching intervals (ratio ≤ 3): same bound via integrated boundary defect (no pointwise comparison at common endpoint). Exterior rows with width/3 gap ≤ C·far charge.

## GradedIntervalAveragesHaveUniformGammaControl (uses ACS GammaMeanVarianceCapacity)
- Symmetric kernel on finite disjoint intervals with zero exterior square: ∫∫ = Σ_{ij} blocks + 2Σ_i exterior rows.
- levyEnergy_interval_average_le: g = piecewise interval means of f on short (≤ 1), adjacent-comparable (ratio 3), gap-comparable intervals, nonzero-mean cells separated from the exterior by width/3 ⇒ Γ(g) ≤ 32e²·Γ(f) (homogeneous, via coherent mean-variance far-charge capacity).

## StoppingCellsFormAUniformlyGradedPartition
- Padded stopping grid: width_0 = log 2 (zero cell at [−log2, 0)), then logCell labels; beyond A the band A..2A−1 repeats.
- Widths ≤ 1; consecutive ratios ≤ 3 (uniform in A, level); boundaries strictly increasing; initial boundaries = log k; band starts = j log 2 + log A; every band endpoint = j log2 + log(A + r) (literal stopping-cell endpoints).

## PaddedGradedGridsHaveUniformGammaControl
- Complement of a finite interval chain = two exterior half-lines a.e.
- levyEnergy_padded_grid_average_le: strictly increasing grid, widths ≤ 1, adjacent ratio ≤ 3, f, g vanish outside, g = cell means of f, first and last means zero ⇒ Γ(g) ≤ 32e²Γ(f).

## ActualGeneratorHeadsAreLocalIntervalMeans
- Dyadic block [log(a2^j), log((a+1)2^j)) = j log 2 + [log a, log(a+1)), width logCell a; block source = interval indicator; its coordinate vector = √ℓ_a·W^j e_a, fixed by H_A when a < 2A.
- Self-adjointness ⇒ ∫_block head = ∫_block source; head constant on each stopping block (j = 0 or a ≥ A) ⇒ head = interval mean of source on its stopping interval.
- Finite sources vanish on x < 0 and beyond Σ log(n_i + 1).

## ActualGeneratorHeadsAndTailsHaveUniformGammaBounds (uses ACS DisjointStepsHaveLogarithmicGammaCost)
- Each stopping-grid cell (k > 0) is a dyadic block with a < 2A and (j = 0 or a ≥ A); padding with zero cells at both ends (grid reaches beyond support).
- actualGeneratorHead_gamma_le: Γ(head) ≤ 32e²·Γ(source).
- actualGeneratorHead_tail_gamma_le: Γ(head) + Γ(tail) ≤ (2 + 96e²)·Γ(source), uniform in cutoff A, horizon, coefficients, translation levels; complete-cell sources included.

## AllEvenPrimePowersHaveOriginalGammaApproximation
- |square(source) − square(head)| ≤ (ε + C/(1 + log A))·Γ(source) (stability constant pays head/tail energies).
- exists_allEvenPrimePowers_generator_approximation: ∀δ ∃A₀: every A ≥ A₀ makes the complete even-prime-power source error ≤ δΓ(source) for every finite real cell source (all translation orbits of retained generators present).
