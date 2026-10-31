# 38 ArithmeticIndexDescent — mathematical facts log

## TheIndexIsPaidByTransverseEnergy (uses AE TheTransverseEnergyOfTheZeroDivisor, ACS ArithmeticHodgeIndexSignatureLaw, RHTower CCMZetaWeilSmoothIdentity; `#print axioms` lines)
- divisorTransverseEnergy (AE): ½Σ_j angularEnergy(j), angular term (Re ρ_j − Re ρ_k)²/|ρ_j − ρ_k|². A right packet s (Re > 1/2) and its horizontal reflection are disjoint; each member carries ≥ 1 unit ⇒ |s| ≤ divisorTransverseEnergy (also on the actual ζ carrier).
- negIndex_weilGram_le_divisorTransverseEnergy: negative index of any finite smooth Weil Gram (C² compact tests) ≤ transverse energy (via ACS negIndex ≤ #off-line zeros right of 1/2). posIndex of intersection Gram ≤ 1 + energy (pole plane gives one positive square).

## TheArithmeticSourcePaysTheIndex (uses AE TheSelbergWorkExhaustsTheTransverseEnergy)
- firstZeroCopy (one multiplicity copy per distinct zero) injective ⇒ divisorTransverseEnergy ≤ xiCopyTransverseEnergy (multiplicity-weighted).
- negIndex ≤ xiCopyTransverseEnergy. xiDampedSourceWork(R) → copy energy as damping removed ⇒ every b < negIndex is eventually exceeded by damped source work, and (double limit) by finite tapered source work xiTaperedSourceWork(n+4, N).

## BoundedSourceWork (uses ArithmeticCorrespondencePositivity)
- copyAngularTerm between multiplicity copies (transverseAngular of signed depth and height differences), symmetric, ≤ 1/(1 + Δheight²) (strip confinement |Δdepth| ≤ 1) ⇒ each row summable.
- Critical zeros do not interact transversally (term = 0 when both on line).
- xiCopyTransverseEnergy = ½Σ_p copyAngularEnergy(p); finite off-line support ⇒ finitely many copies ⇒ copy energy ≤ 2Σ_{p∈F}rows < ∞.
- xiCopyTransverseEnergy_lt_top_iff: finite copied energy ⇔ finite off-line support. eventually_bounded_dampedSourceWork_iff: eventually bounded damped work ⇔ finite off-line support; dampedSourceWork_tendsto_top_iff: work → ∞ ⇔ infinitely many off-line zeros.

## TheEnergyStrictlyExceedsTheIndex (uses RHTower RiemannVonMangoldt)
- reflectionDiagonalAngle(ρ) = (2Re ρ − 1)²/((2Re ρ − 1)² + (2 Im ρ)²) > 0 off the line: angle to 1 − ρ. Off-line zero: angularEnergy ≥ 1 + diagonal angle > 1 (horizontal partner gives 1, FE reflection gives extra).
- Nonempty right packet: |s| < energy (strict). negIndex_eq_zero_or_lt_divisorTransverseEnergy: finite Weil negative index is 0 or strictly below the energy.
- One right zero + its conjugate ⇒ energy > 2. riemannHypothesis_iff_divisorTransverseEnergy_le_two: RH ⇔ energy ≤ 2 (closed threshold; RH ⇔ energy = 0 already in AE). No uniform lower bound on the diagonal angle asserted.

## TheSourceWorkHasAClosedQuantumThreshold
- xiCopyTransverseEnergy = 0 ⇔ RH; RH ⇔ copy energy ≤ 2. RH ⇒ damped source work ≡ 0.
- riemannHypothesis_iff_cofinally_dampedSourceWork_le_two: RH ⇔ cofinally many n with xiDampedSourceWork(n+4) ≤ 2 (no upper bound on work proved; identifies target).
- negIndex_eq_zero_or_eventually_sourceWork_gt_index: finite Weil negative index is 0 or eventually (damping then taper) strictly below finite tapered work — no ε loss.

## DampingIncrementPositivity (uses AE ReflectedTransverseWork)
- heightDamping(R,t) rational damping; derivative in R = 4R³·dampingVelocity(R,t), dampingVelocity = t²/(R²+t²)³ ≥ 0.
- Relative Lipschitz above the zero-free gap |t|,|u| ≥ 4: 2|v(t) − v(u)| ≤ |t−u|(v(t)+v(u)) (explicit polynomial identity).
- dampingVelocity_work_nonneg: reflectedWork with velocity weights ≥ 0 (near-collision |t−u| ≤ 1 and far-field bounds absorb reflected cross term), x²+y² ≤ 1.
- reflectedWork_monotoneOn_scale: every reflected pair work is monotone in damping scale R ≥ 0 above the height gap.
- heightDamping_doubling_gap: R ≤ |t| ≤ 2R ⇒ heightDamping(2R,t) − heightDamping(R,t) ≥ 21/100, attained at |t| = 2R.

## SourceWorkIncrementsPayForNewZeros (uses RHTower ZetaZeroFreeRegionAllZeros)
- |Im ρ| ≥ 4 for every ζ zero (zero-free height gap) ⇒ xiDampedPairWork monotone; xiDampedSourceWork monotone on [4,∞).
- RightXiZeroCopy (signed depth > 0); quartet vertices p, line-conjugate p̄; each of the 4 ordered pairs has pair work = heightDamping(R, height) exactly.
- sum_damping_increment_le_sourceWork_increment: Σ_{p∈s}(damping increment) ≤ work(S) − work(R) for R ≥ 4.
- annular_zero_copies_paid_by_sourceWork_increment: right copies with height in [R,2R] cost ≥ 21/100 each of work(2R) − work(R); visible in finite tapered work up to ε.
- finite_offLineSupport_or_arbitrarily_high_quantum_increments: finite off-line support or quantum increments ≥ 21/100 at arbitrarily high scales.

## VanishingScaleIncrementsCharacterizeFiniteSupport
- work(R) ≤ copy energy for R ≥ 4; finite off-line support ⇒ work(R) → energy (real limit, all exterior rows retained).
- doubledSourceWorkIncrement(R) = work(2R) − work(R) ≥ 0; → 0 on finite support.
- eventually_subquantum_increment_iff: eventually increment < 21/100 ⇔ finite off-line support; doubledSourceWorkIncrement_tendsto_zero_iff: increments → 0 ⇔ finite off-line support. No arithmetic upper estimate supplied.

## EveryOffLineQuartetCostsAStrictScaleQuantum
- quartet of an off-line zero (conjugate × line reflection) has 4 copies of equal |height|; 16 ordered pair works: heightDamping(R, Im ρ)·(1 if same height side else diagonal angle); total 8·heightDamping·(1 + diagonal angle) (no unequal-weight mixed terms).
- offLineQuartet_increment_payment: 2(damping increment)(1 + diagonal angle) ≤ work(S) − work(R).
- Own-height gap: heightDamping(2|t|,t) − heightDamping(|t|,t) = 39/100 ⇒ offLineQuartet_strict_increment: 39/50 < work(2|Im ρ|) − work(|Im ρ|).
- eventually_closed_quantum_increment_iff: eventually increment ≤ 39/50 ⇔ finite off-line support. riemannHypothesis_iff_all_scale_increments_le_quantum: RH ⇔ ∀R ≥ 4, work(2R) − work(R) ≤ 39/50.

## TheQuadraticScaleWorkDetectsEveryException (uses RHTower PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization)
- R²(heightDamping(2R,t) − heightDamping(R,t)) → (3/2)t² (exact critical decay R⁻²).
- quadraticIndexUnit = (3/2)·xiOrderTwentyThreeOptimizedHeightSq (certified arithmetic off-line height floor²); quadraticExclusionQuantum = 2·unit > 0.
- quadraticWorkIncrement(R) = R²·(work(2R) − work(R)); = 0 under RH; ≥ 0; tapered version converges.
- Quartet charge 3(Im ρ)²(1 + diagonal angle) > exclusion quantum (height floor + positive angle). RH or eventually quadraticWorkIncrement > quantum (also in finite tapered readings, damping-then-taper order).
- riemannHypothesis_iff_cofinally_quadraticIncrement_le_exclusionQuantum: RH ⇔ cofinally quadraticWorkIncrement ≤ quantum (excludes finite and infinite exceptions).
- quadraticWorkIncrement_tendsto_atTop_of_infinite: infinite off-line support ⇒ quadratic increment → ∞.

## TheCriticalRateClassifiesAllOffLineSupport
- quadraticPacketSourceMoment(F) = (3/2)Σ_{p∈F} height²·signedDepth·xiSourceField(p) (signed individual terms).
- Finite off-line support: tapered and damped work are exact finite sums over off-line copies of signedDepth·damping·sourceField (critical copies drop out; exterior fields retained).
- quadraticWorkIncrement → finite source moment on finite support; quartet charge ≤ moment; moment > exclusion quantum when ¬RH; 3(Im ρ)² < moment for each exception (localizes exceptions in height).
- eventually_bounded_quadraticIncrement_iff, quadraticIncrement_has_finite_limit_iff: bounded / finite limit ⇔ finite off-line support.
- quadratic_source_rate_trichotomy: (RH ∧ increment ≡ 0) ∨ (finite exceptional support, ¬RH, limit L > quantum) ∨ (infinite support, increment → ∞).

## TheCriticalRatePaysEveryNegativeSquare
- rightPacketQuadraticCharge(s) = (3/2)Σ height²; R²Σ damping increments → charge and ≤ quadraticWorkIncrement(R).
- indexUnit·|s| ≤ charge (certified height floor per right copy); charge ≤ finite source moment.
- exists_rightCopy_packet_of_weilGram: every finite smooth Weil negative index k has a packet of k right copies (Pontryagin bound).
- Each negative square pays quadraticIndexUnit at the critical rate: b < unit·negIndex ⇒ eventually b < quadraticWorkIncrement (also finite tapered readings); finite stratum: unit·negIndex ≤ source moment.

## TheSourceBudgetMakesTheIndexCostQuadratic (uses RHTower XiWardCriticalBudgetProbe, Sieve.HarmonicCauchySchwarz)
- Strip-edge resolvent mass Σ xiBudgetMassAt(1/2) ≤ 3/50; packet + reflections spend twice ⇒ Σ_{p∈s}1/(height² + 1) ≤ 3/100.
- resolventIndexCharge(k) = 50k² − (3/2)k ≤ packet charge (weighted Cauchy–Schwarz k² ≤ (Σ1/(h²+1))(Σh² + k)).
- Each finite Weil index k forces quadratic resolvent charge 50k² − 3k/2 eventually in quadraticWorkIncrement; ≤ source moment on finite stratum. Forcing law, no upper bound on work.

## TheCriticalSourceRateIsMonotone
- inverseScaleDamping(r,t) = 1/(1 + rt²)², heightDamping(R,t) = inverseScaleDamping(1/R², t). Second r-derivative weight curvatureHeightWeight = t⁴/(1 + rt²)⁴; relative Lipschitz above |t| ≥ 4 (fourth-power ratio bounds).
- inverseScale_reflectedWork_convex: reflected pair work is convex in inverse-square scale r ≥ 0 above the zero-free gap.
- Convex secant: R²·(pair work(2R) − pair work(R)) = secant slope between r/4 and r ⇒ monotone in R (xiQuadraticPairWork_monotoneOn).
- quadraticWorkIncrement(R) = ¼Σ xiQuadraticPairWork (absolutely convergent) ⇒ quadraticWorkIncrement monotone on [4,∞) (no derivative-sum interchange).
- Pair limit: xiQuadraticPairWork → (3/2)reflectedWork(Δdepth, Σdepth, Δheight, h_p², h_q²).

## TheCriticalSourceRateHasACanonicalEnergy
- xiHeightSquarePairEnergy = (3/8)reflectedWork(…, h_p², h_q²) ≥ 0; pointwise majorant of each normalized pair increment (monotone limit). Critical exterior row: (3/4)h_p²·transverseAngular(depth_p, Δh) (own height weight cancels).
- xiCriticalSourceEnergy = Σ over all ordered copy pairs (ℝ≥0∞).
- quadraticWorkIncrement_tendsto_criticalEnergy (dominated convergence when summable; large finite sums otherwise); every finite scale ≤ energy.
- Finite stratum: energy = finite source moment; infinite support ⇒ energy = ⊤; energy ≠ ⊤ ⇔ finite support; RH ⇒ energy = 0.
- riemannHypothesis_iff_criticalEnergy_le_quantum: RH ⇔ critical energy ≤ quadraticExclusionQuantum. Index charges: unit·negIndex ≤ energy; resolventIndexCharge(negIndex) ≤ energy. Not asserted to be a PSD Gram kernel.

## TheWorkAndIndexHaveTheSameFiniteStratum (uses SSHA UnboundedOverlapIsTheRiemannHypothesis)
- splineIndex(S) = negative index of the Weil Gram on cubic-spline translates at S ⊆ integer logs.
- Right carrier finite ⇔ off-line support finite. bounded_splineIndex_iff_offLineSupport_finite (via zeta_splineAtomic_negIndex_law): uniform bound on spline indices ⇔ finite off-line support ⇔ eventually bounded damped source work. Identifies finiteness endpoints of the two programmes (not finiteness with absence of defects).

## ArithmeticSectionsHaveOnlyPresentationRadicals (uses ACS ArithmeticSectionsPayThePole, SourceDeterminantalSectionsAndArithmeticRiemannRoch; HTGeometry FactorThroughRange)
- realWeilForm: complete real Weil pairing as symmetric bilinear form on realTests; realTestSynthesis Σx_if_i; realWeilMixed matrix.
- arithmeticSectionTests N w (ACS, w ≤ fullSectionRatio·δ_N): Weil form ≥ ∫q² on sections (square-mass floor).
- arithmeticSection_gram_kernel_iff: section Gram kernel = kernel of test synthesis (only presentation relations).
- Null section combinations annihilate all ambient mixed Weil entries; distinct coefficient lifts of one mixed column give the same section; every ambient test has a Weil-orthogonal mixed lift (coefficients non-unique).
- arithmeticSection_mixed_range: mixed block = section Gram · X unconditionally (range compatibility).

## ArithmeticSectionProjection
- arithmeticSection_exists_unique_projection: unique actual section p in span with Weil(f_i, g − p) = 0; projection linear, idempotent, reproduces sections.
- Residual pair identity W(g−Pg, h−Ph) = W(g,h) − W(Pg,Ph) (full completed form, both pole moments). Projected section has W ≥ 0 (square-mass floor) ⇒ residual energy ≤ W(g,g).
- arithmeticSectionProjection_minimizes_with_square_gap: W(g − Pg) + ∫(Pg − q)² ≤ W(g − q) for every section q.

## SingularRefinement (uses HTGeometry HaynsworthInertia)
- If mixed block = A·X (A Hermitian, possibly singular): triangular congruence gives fromBlocks(A, AX, (AX)ᴴ, C) ≅ A ⊕ (C − XᴴAX); complement independent of lift X. negIndex, posIndex, nullIndex split additively. Range compatibility is the exact condition; no invertibility.

## TheSectionComplementCarriesAllNegativeSquares (uses ACS FiniteConfigurationPontryaginLaw; RHTower WeilPaperPacketRealification, XiGaussianHeatWindowPrimeTwoMargin)
- complexWeilMixed (complexified real Weil pairing) = literal weilGram (primes, Gamma, poles) on real tests (imaginary part 0).
- Narrow section Grams have negIndex 0 even with complex coefficients (re/im split).
- negIndex_weilGram_section_extension_eq_residual: negIndex of Weil Gram on (sections ⊔ g) = negIndex on residual tests g_j − P g_j. Exact index descent, no nonsingularity assumption.

## TheSourceKernelIsLocallyBounded (uses BSU ProbeParsevalLaw; RHTower WeilFullConeSpectralConsistency)
- Real C² compact tests are Admissible (Gamma integrability). weilSourceKernel g (u) = full Weil functional of the translated reflected test: continuous (pole + prime + arch parts).
- realWeilForm_eq_sourceKernel: W(p,g) = Re∫p(u)·K_g(u)du (both poles, prime comb, Gamma retained).
- exists_sourceKernel_window_bound: on a fixed window |u| ≤ R, |W(p,g)| ≤ C·‖p‖₁ (independent of derivatives/presentation).

## TheProjectionCostIsBoundedOnEachWindow (uses RHTower WeilMarginSuperexponentialLaw)
- Arithmetic sections supported in [0, log N + w]; projections stay sections.
- exists_uniform_arithmeticSectionProjection_energy_bound: W(Pg,Pg) ≤ B = 2LC² for every finite section family (W(Pg,Pg) = W(Pg,g) ≤ C‖Pg‖₁, ‖Pg‖₁² ≤ 2L∫(Pg)² ≤ 2L·W(Pg,Pg)). Independent of dimension, derivatives, conditioning.

## FiniteGramDescent (uses HTGeometry KreinIndexEscapeStratification; ACS TheHodgeDefectIsCyclic)
- eventually_negIndex_limit_le: entrywise convergence G_t → H ⇒ eventually negIndex H ≤ negIndex G_t (negative subspaces survive).
- eventually_negIndex_limit_le_presentation: with growing dimensions and arbitrary coefficient maps C_t, if C_tA_tC_tᴴ → H entrywise then eventually negIndex H ≤ negIndex A_t (rectangular pullback cannot increase negative index). Arithmetic application needs convergence of every pulled-back mixed entry of the complete form.

## TheSectionProjectionHasACanonicalLimit
- finiteSectionProjection over finite subsets S of one narrow section space (directed). finiteSectionEnergy ≥ 0, monotone; nested pair W(P_Sg, P_Tg) = E_S; increment W(P_T − P_S) = E_T − E_S; ∫(P_Tg − P_Sg)² ≤ E_T − E_S.
- Bounded by window bound ⇒ sectionCompletionEnergy = sup, finite energies converge; finite projections Cauchy in L² (square-mass).
- sectionCompletionPair by polarization; symmetric bilinear PSD form sectionCompletionForm; completedSectionResidualForm = W − completion: ≤ W on diagonal, vanishes against every section (descends through the whole narrow section space).
- Residual mixed entries converge; completedSectionResidualGram Hermitian, actual mixed-Gram limit; each negative square of completed complement witnessed at a finite refinement.

## TheCompletedSourceComplementIsPaidByWork
- exists_actual_weilGram_dominating_completion_index: completed residual index ≤ index of an actual smooth Weil Gram (finite-stage residual tests).
- Completed residual index is 0 or strictly below divisorTransverseEnergy; 0 or eventually below finite tapered source work (damping then taper).

## TheSourceKernelEnergyBoundsTheSchurCost (uses HTGeometry GramPairingCauchySchwarz)
- arithmeticSectionSupport = ⋃_{n≤N}[log n, log n + w] (compact; sections vanish off it including gaps).
- sourceKernelEnergy(s, g) = ∫_s|K_g|². W(p,g)² ≤ ∫p²·sourceKernelEnergy(s,g) for p supported in s.
- Every finite section projection and the whole completion: energy ≤ sourceKernelEnergy(support, g). completedSectionResidualForm(g,g) ≥ W(g,g) − sourceKernelEnergy.

## ShrinkingCellsRemoveVanishingEnergy
- vol(support) ≤ Nw; w ≤ 1 ⇒ support ⊆ [0, log N + 1] ⇒ sourceKernelEnergy ≤ B·w (B = N·sup|K_g|²).
- Completion energy ≤ Bw ⇒ vanishes as w → 0 at fixed N; residual returns to original W(g,g). Uniform over profile families at fixed N, not over growing N.

## ThePolePaymentRetainsTheUnusedWidthReserve (uses ACS arithmeticSection/sectionReserve, poleA/poleB)
- sectionPoleCost(N,w) = wN(e^w + 1); weighted pole C–S (Young with L = 1 + log N): 2AB ≥ −sectionPoleCost·sectionReserve.
- W(section) ≥ ∫(section)² + (1/8 − sectionPoleCost)·reserve (Markov form ≥ reserve, ACS).
- Width fraction a: w ≤ a·fullSectionRatio·δ_N ⇒ sectionPoleCost ≤ a/8 ⇒ W(section) ≥ ∫² + ((1−a)/8)·reserve.

## TheCompletedIndexIsReachedAtAFiniteStage
- negIndex_antitone_of_hermQuad_le: A ≤ B as quadratic forms ⇒ negIndex B ≤ negIndex A.
- Completed residual ≤ every finite residual (quadratic forms, complex readings) ⇒ finite residual index ≤ completed index; with eventual reverse inequality: eventually equal. exists_actual_weilGram_with_completion_index: completed index = index of an actual smooth Weil Gram.

## SeparatedSupportsRemoveTheGammaSingularity (uses ACS ArithmeticSectionSpace; RHTower WeilPhiDoobArchimedeanJumpAndHalfLineFolding, CHMDMasslessContinuationPieces)
- Polarized Lévy identity: (1/2π)∫Re(f̂ ĝ̄)·gammaBracket = gammaBracket(0)∫fg + ∫_0^∞ω(x)∫(f − f(·+x))(g − g(·+x)) (absolutely integrable).
- Disjoint supports: arch cross = −∫_0^∞ω(x)·sourceCollarCorrelation(f,g,x), collar = ∫f g(·+x) + f(·+x)g; |collar| ≤ sectionMass f + sectionMass g (∫f², ∫g²) independent of widths/derivatives.
- Support gap d > 0: collar vanishes for |x| ≤ d; |arch cross| ≤ (∫_{x>d}ω)·(‖f‖² + ‖g‖²) (Lévy tail).

## TouchingSupportsHaveBoundedGammaInteraction (uses RHTower CCM CCMRestrictedWeilGammaBoundaryPairing)
- norm_gammaBoundaryPair_le: for L² u supported in x ≤ 0, v in x ≥ 0: |∫_0^∞ Gamma density·⟨T_h v, u⟩| ≤ π(‖u‖² + ‖v‖²) (half-line Hankel operator ccmGammaBoundaryCLM, norm ≤ 2π).
- realProfileL2 embeds compact continuous real profiles; ordered supports (f left of b, g right of b): only one orientation of the collar survives.
- abs_sourceGammaCollar_le_of_ordered / abs_archCross_le_of_ordered: touching ordered supports (no gap) ⇒ |Gamma cross| ≤ π(sectionMass f + sectionMass g), uniform over boundaries, widths, profiles.
- archCross_eq_neg_sourceCollar_of_disjoint (C², disjoint): spectral Gamma cross = −literal collar.

## GammaBoundaryHasAnExactSchurWeight (uses RHTower GammaHardyPhaseRateLevyKhintchine; HTGeometry CarlemanSchurWeight)
- Schur weight W(t) = e^{t/2}/√(e^{2t} − 1) = e^{−t/2}/√(1 − e^{−2t}); exponential change of variable sends the weighted Gamma row to the Carleman row (arctan primitive).
- integral_gammaBoundarySchurRow: ∫_0^∞ ω(s+t)W(t)dt = (π/2)W(s) exactly (ω = archLevyDensity).
- Weighted C–S + Tonelli: ∫_0^∞(∫ω(s+t)F(t)dt)²ds ≤ (π/2)²∫F²; norm_ccmGammaBoundaryCLM_le_pi_half: half-line Gamma Hankel operator norm ≤ π/2 (sharpens 2π).

## TheGammaBoundaryReserveIsAnExactSquare
- gammaBoundaryPairReserveDensity(f,g)(s,t) = ω(s+t)W(s)W(t)|g(s)/W(s) − f(t)/W(t)|²/2 ≥ 0, integrable for all L²(0,∞) pairs.
- integral_gammaBoundaryPairReserveDensity: ∫reserve = (π/4)(‖f‖² + ‖g‖²) − Re⟨g, Γf⟩ (exact identity).
- gammaBoundary_quadratic_deficit: (π/2)‖f‖² − Re⟨f, Γf⟩ = ∫ reserve density (f,f).

## TheGammaBoundaryBoundHasNoNonzeroEqualityCase
- W(t)² = e^{−t}/(1 − e^{−2t}); (e^{−1}/2)t^{−1} ≤ W² on (0,1]; W² ≤ t^{−1} on (0,∞). W² not integrable at 0 (W ∉ L²).
- Zero reserve ⇒ f = c·W a.e. ⇒ c = 0. gammaBoundary_quadratic_eq_iff: Re⟨f, Γf⟩ = (π/2)‖f‖² ⟺ f = 0; strict deficit for every f ≠ 0 (no uniform spectral gap claimed).

## TruncatedGammaWeightsHaveLogarithmicMass
- truncatedGammaWeight a = 1_{(a,1]}·W ∈ L²(0,∞); ‖·‖² = ∫_a^1 W² ≥ (e^{−1}/2)log(1/a); at a = e^{−(n+1)}: ≥ (e^{−1}/2)(n+1) (unbounded).

## TheGammaBoundaryOperatorHasNoNormMaximizer
- gammaBoundary_pair_reserve_eq_zero_iff: mixed reserve(f,g) = 0 ⟺ f = g = 0.
- norm_ccmGammaBoundaryCLM_apply_lt: ‖Γf‖ < (π/2)‖f‖ for every f ≠ 0 (apply mixed rigidity to (Cf, Γf)); no norm maximizer.

## BoundaryTruncationLosesOnlyBoundedGammaEnergy
- W(t) ≤ t^{−1/2}; ω(s+t)W(s)W(t)/2 ≤ s^{−3/2}t^{−1/2} (ω ≤ 2/(s+t), Carleman bound).
- Truncated weight reserve lives where exactly one argument is in (a,1]; four power rectangles (∫ = 4 each) ⇒ reserve ≤ 16 independent of a.
- Rayleigh lower: (π/2)‖f_a‖² − 16 ≤ Re⟨f_a, Γf_a⟩; with log-growing mass: norm_ccmGammaBoundaryCLM_eq_pi_half: ‖Γ‖ = π/2 exactly (sharp, not attained). Explicit truncations reach Rayleigh > (π/2 − δ).

## BoundedWindowsHaveFinitePrimeInteraction (uses RHTower WeilFullConeSpectralConsistency)
- weilTest(f,g)(x) = sectionCorr f g (−x); |·| ≤ (‖f‖² + ‖g‖²)/2.
- Common window |u| ≤ R ⇒ weilTest vanishes for |x| > 2R ⇒ prime part is a finite sum over n < e^{2R}.
- exists_primePart_window_mass_bound: |prime part(f,g)| ≤ C_R(‖f‖² + ‖g‖²), C_R = Σ_{n<e^{2R}} Λ(n)/√n; uniform over profiles, derivatives, signs.

## TheSeparatedMixedSourceIsBounded (uses RHTower WeilPolarConeKernelTransformForm)
- Window |u| ≤ R: poleA², poleB² ≤ 2Re^R·‖f‖²; |mixed pole poleB f·poleA g + poleA f·poleB g| ≤ 2Re^R(‖f‖² + ‖g‖²).
- Decomposition W(f,g) = mixed pole − Re prime part + arch cross (realWeilForm_eq_source_parts).
- exists_separatedWeil_window_mass_bound: gap d > 0, window R ⇒ |W(f,g)| ≤ (2Re^R + C_R + ∫_{x>d}ω)(‖f‖² + ‖g‖²).
- exists_separatedWeil_mass_payment: rescaling ⇒ 2|W(f,g)| ≤ ε‖f‖² + (4(C+1)²/ε)‖g‖² for any ε > 0.

## TouchingCellsPayTheFullMixedSource (uses EveryShortCellPaysAnyFixedMassCharge)
- exists_orderedWeil_window_mass_bound: ordered across any boundary b (no gap), window R ⇒ |W(f,g)| ≤ (2Re^R + C_R + π)(‖f‖² + ‖g‖²); same ε/D payment.
- exists_touchingCell_diagonal_extension: for any ε, L, a short cell g in (b, b+δ), δ < δ₀, adjacent to old p (supported left of b): W(p+g) ≥ W(p) − ε‖p‖² + L‖g‖² (short-cell coercivity pays D + L).

## TheOrderedGammaTailRetainsPolarCancellation (uses RHTower CHMDStage6PolarDoubleZeroAndContinuumLogMomentCollapse)
- ω(h) = e^{−h/2} + e^{−2h}ω(h) (first-mode recursion, archLevyDensity_first_mode).
- Ordered f | g across b: ∫_0^∞ e^{−h/2}·collar = poleA f·poleB g (first Gamma exponential is exactly the inward polar product).
- Gamma collar = poleA f·poleB g + orderedGammaTail; realWeilForm_ordered_pole_cancellation: W(f,g) = poleB f·poleA g − Re prime part − orderedGammaTail (one polar product cancels exactly).
- Tail = Gamma collar of exponentially tilted profiles e^{2(u−b)}f, e^{−2(u−b)}g ⇒ |tail| ≤ π(leftBoundaryMass + rightBoundaryMass) (mass weighted by e^{−4·distance to cut}).

## TheOrderedWeilSourceIsACenteredChebyshevDefect (uses ArithmeticIncidencePositivity LagChebyshevAbelSummation)
- orderedSourceLagWeight q(h) = e^{−h/2}·sectionCorr f g h; C¹, vanishes for h ≤ 0 and h ≥ S.
- Prime part = Σ_n Λ(n)q(log n) (one orientation only, no factor 2); surviving pole poleB f·poleA g = ∫_0^∞ e^h q(h)dh (continuum density).
- realWeilForm_ordered_eq_centered_chebyshev: W(f,g) = −∫_0^∞(ψ(e^h) − e^h − c... i.e. chebyshevError(h) − c)·q'(h)dh − orderedGammaTail, any constant c (q(0) = 0 ⇒ ∫q' = 0).
- |W(f,g)| ≤ ∫|chebyshevError − c|·|q'| + π(left + right boundary masses).

## TheOrderedWeilSourceRetainsItsGammaSquareReserve
- Translate cut to 0, reflect left profile: leftBoundaryTestL2, rightBoundaryTestL2 in L²(0,∞) with full mass preserved.
- sourceGammaCollar_eq_boundary_pair: ordered literal collar = Re⟨right, Γ left⟩ (Γ = ccmGammaBoundaryCLM).
- Tilt tests e^{±2(u−b)}: orderedGammaTail = Re⟨tilted right, Γ tilted left⟩ = (π/4)(leftBoundaryMass + rightBoundaryMass) − orderedGammaSquareReserve (≥ 0).
- realWeilForm_ordered_eq_chebyshev_add_gammaReserve: W(f,g) = −∫(chebyshevError − c)q' − (π/4)(L + R masses) + square reserve; hence W(f,g) ≥ −∫(chebyshevError − c)q' − (π/4)(L + R). Sharper constant π/4 (vs π) with reserve kept.

## ThePrimeTwoMixedBlockReadsCoarseDifferences (uses ACS HaarCellCoarseSplitting, HaarCellGammaPayment; LogCells)
- logCellWidth(2a) + logCellWidth(2a+1) = logCellWidth(a); coarse atoms (pair averages) orthogonal with masses logCellWidth.
- Prime-2 translation of Haar detail atom a = haarLeftCoeff·coarse(2a) − haarRightCoeff·coarse(2a+1).
- ⟨T_{log2} haarAtom a, coarseSection q⟩ = haarMass a·(q(2a) − q(2a+1)); other orientation (coarse shifted onto detail) vanishes.
- primeTwoMixedSource = (2Λ(2)/√2)·Σ haarMass a·d_a·(q(2a) − q(2a+1)); odd horizon 2Y+1 retains whole block.
- Signed Young: |primeTwoMixedSource| ≤ ε·detailMass + ((Λ(2)/√2)²/ε)·coarseVariation (Σ haarMass·(q(2a) − q(2a+1))²).

## TheGammaMeanGraphPaysThePrimeTwoMixedBlock (uses ACS CompleteCellMeanGraph)
- Coarse Gamma edge (a,b) = w_a w_b (q_a − q_b)²·ω(max span); adjacent pair (2a, 2a+1): = haarMass a·(w_a ω(w_a))·(q(2a) − q(2a+1))²; hω(h) ≥ e^{−1/2}/2 for h ≤ 1.
- primeTwoCoarseVariation_le_meanGraph: (e^{−1/2}/4)·coarseVariation ≤ (1/2)·completePairMeanGraph.
- primeTwoDetailCharge = 1 + 4(Λ(2)/√2)²e^{1/2}; |primeTwoMixedSource| ≤ charge·detailMass + (1/2)·meanGraph.
- completePair_gamma_after_primeTwoMixed: levyEnergy(complete pair profile) − |prime-2 block| ≥ Σ log(a)·haarMass·d_a² − charge·detailMass.
- exists_high_detail_gamma_pays_primeTwo: details only at a ≥ A (A > e^{charge}) ⇒ |prime-2 block| ≤ levyEnergy, all coarse coefficients free.

## ThePrimeTwoMixedTailIsGammaSmall
- Graph fraction δ: |block| ≤ (charge/δ)·detailMass + δ·(meanGraph/2).
- exists_primeTwo_gamma_small_tail: ∀δ ∃A: |prime-2 block of details a ≥ A| ≤ δ·levyEnergy(full untruncated profile), uniform in horizon Y and coarse data (log detail reserve).
- Additivity in details; exists_primeTwo_finite_detail_approximation: finitely many detail coordinates approximate the prime-2 mixed source within δ·Gamma energy.

## TheCoarseDetailPrimePairIsTheLiteralSource
- Hilbert coarse/Haar sections have real representatives averageSectionProfile, haarSectionProfile; completePairProfile = sum.
- Shifted Hilbert pairings = physical correlation integrals ∫f(x)g(x+t).
- primeTwoMixedSource_eq_integrals: block = (2Λ(2)/√2)(∫haar·avg(·+log2) + ∫avg·haar(·+log2)); = full prime-2 correlation minus both diagonal prime-2 terms (polarized).
- Original-integral forms of high-detail payment and δ-small tail.

## ThePrimeTwoMixedFormHasUniformFiniteIndex (uses ACS FiniteConfigurationPontryaginLaw)
- primeTwoGammaProfileForm = levyEnergy(complete profile) − prime-2 mixed block, on finite families x ↦ Σx_i(q_i, d_i).
- exists_uniform_primeTwoGamma_negative_dimension: ∃A: every negative subspace injects into first A detail readouts ⇒ negIndex ≤ A, uniform in horizon, family size n, profiles. (Pure coarse prime form, other primes, poles not included.)

## MergedCellVariancePaysCoarseDifferences (uses ACS CompleteCellVariancePayment, IntervalVarianceRemainder)
- Variance on merged [a,c] ≥ ((b−a)(c−b)/(c−a))·(mean_[a,b] − mean_[b,c])² (parallel mass).
- Merged cell [log 4a, log(4a+4)] (width w_a): variance of complete profile ≥ haarMass a·(q(2a) − q(2a+1))².
- completePair_gamma_ge_log_coarseVariation: Σ log(a)·haarMass a·(q(2a) − q(2a+1))² ≤ levyEnergy (disjoint merged pairs, log(1/width) ≥ log a).

## ThePrimeTwoMixedTailHasLogarithmicDecay
- log(A)·|prime-2 block of details a ≥ A| ≤ (1 + (Λ(2)/√2)²)·levyEnergy (Young per term; Gamma controls both log-weighted detail mass and log-weighted coarse variation, not as disjoint shares).
- Tail and head error ≤ (1 + (Λ(2)/√2)²)·levyEnergy / log A: inverse-log decay, uniform in horizon.

## TranslatedDetailsAreUniformlySmallInGammaEnergy (uses SSHA TheArchimedeanPairingOfTwoAtoms; HTGeometry DyadicLatticeCover)
- Balanced Haar cell a reads only the local variance of g: 2|d·∫haar_a·g| ≤ haarMass a·d² + Var_{[log2a, log(2a+2)]}(g).
- cellGammaWeight a = log(1/w_a) > 0 (also a = 1: w_1 = log 2 < 1), monotone, ≥ log a.
- Σ cellGammaWeight(a)·Var_pair_a(g) ≤ levyEnergy g (disjoint pairs, BV compact g).
- 2·cellGammaWeight(A)·|∫ haar-tail_{a≥A}·g| ≤ Σ cellGammaWeight·haarMass·d² + levyEnergy g.
- Translation invariance of levyEnergy ⇒ uniformly in lag t: cellGammaWeight(A)·|∫ detail-tail·profile(·−t)| ≤ levyEnergy(profile); full detail (A = 1) ≤ levyEnergy/cellGammaWeight(1); inverse-log decay at every real lag.

## EveryEvenPrimeLagHasGammaSmallMixedTails
- integerMixedSource m = (2Λ(m)/√m)(both oriented detail–coarse correlations at lag log m); additive in details.
- Even m: translated detail middle boundary (2a+1)m is even, never an odd target detail boundary ⇒ detail–detail pairing vanishes ⇒ mixed source = pairing of translated detail with full complete profile.
- cellGammaWeight(A)·|even-lag mixed tail| ≤ (2Λ(m)/√m)·levyEnergy; whole even-lag source ≤ (2Λ(m)/√m)·levyEnergy/cellGammaWeight(1); prime-2 block paid at every horizon X (terminal half-pairs included).

## TheEntirePrimeTwoEulerMixedSourceIsGammaSmall (uses BVI EnergyMeanOfThePowerDampedSourceTendsToOne; RHTower HeatRemainderDerivative)
- primeTwoPowerWeight k = 2Λ(2^{k+1})/√(2^{k+1}); Σ = 2log2/(√2 − 1) (critical Euler factor at 2 converges absolutely).
- primeTwoEulerMixedSource = Σ_k integerMixedSource(2^{k+1}) (all powers of 2 even ⇒ full-profile payment); absolutely summable; |·| ≤ total·levyEnergy/cellGammaWeight(1); tail ≤ total·levyEnergy/cellGammaWeight(A).
- ∀δ ∃A: whole prime-2 Euler mixed tail ≤ δ·levyEnergy; finite detail head approximates within δ. Pure coarse Euler term separate.

## ThePrimeTwoEulerMixedFormHasUniformFiniteIndex
- levyEnergy − full prime-2 Euler mixed source: negative dimension ≤ A uniformly in horizon, family, profiles (kernel of first A detail readouts is nonnegative).

## GammaBoundedCompleteProfilesHaveCompactDetails (uses HTGeometry FiniteApproxTotallyBounded)
- ‖haarSection d X‖² = Σ haarMass a·d_a².
- cellGammaWeight(A)·‖detail tail ≥ A‖² ≤ levyEnergy(complete profile); A = 1: cellGammaWeight(1)·‖details‖² ≤ levyEnergy.
- totallyBounded_gammaUnitDetails / isCompact_closure_gammaUnitDetails: details of all complete profiles with levyEnergy ≤ 1 (any coarse data, any horizon) have compact closure in half-line L² (finite-dim heads in span of first A Haar atoms, A > e^{1/ε²}).

## EveryIntegerPrimeLagHasGammaSmallMixedTails (uses HTGeometry PaperHalfLineCalkin)
- Half-line right shift is a contraction.
- Odd-boundary incidence (2a+1)m = 2b+1 ⇒ a ≤ b: translated high detail pairs only with high target detail.
- integerMixedSource m = (2Λ(m)/√m)(full-profile probe − detail correction ⟨T_{log m}c, d⟩), any integer m ≥ 2.
- cellGammaWeight(A)·|mixed tail at lag m| ≤ 2(2Λ(m)/√m)·levyEnergy; whole ≤ 2(2Λ(m)/√m)·levyEnergy/cellGammaWeight(1).

## FiniteFirstPrimeMixingSharesTheFullPolarReserve (uses TheFullNonfirstSourceRetainsAlmostAllGamma)
- finiteFirstPrimeMixedSource P = Σ_{p∈P} integerMixedSource p (first powers only); cost Σ 2(2Λ(p)/√p); tail ≤ cost·levyEnergy/cellGammaWeight(A); ∀δ ∃A δ-small.
- finiteFirstPrimeFullPolarSource = fullPolarNonfirstSourceForm − first-prime mixed: within ε·levyEnergy of levyEnergy + 2cosh² − 2sinh² (full polar), when details below A vanish.
- Reserve: (1−ε)levyEnergy + 2cosh² ≤ source + 2sinh²; negative index ≤ A + 1 (A detail readouts + one sinh half-moment readout), uniform in horizon.

## EveryFixedEulerMixedSourceIsGammaSmall
- primePowerMixedWeight p k = 2Λ(p^{k+1})/√p^{k+1}; Σ_k = 2 log p/(√p − 1).
- primeEulerMixedSource p = Σ_k integerMixedSource(p^{k+1}); absolutely summable; tail ≤ 2·total_p·levyEnergy/cellGammaWeight(A).
- finiteEulerMixedSource P; cost(P) = Σ_{p∈P} 4 log p/(√p − 1); ∀δ ∃A δ-small tail; finite-head approximation, uniform in horizon.

## FiniteEulerMixedFormsHaveUniformFiniteIndex
- levyEnergy − finiteEulerMixedSource P: negative dimension ≤ A uniformly (fixed finite P; all powers; all horizons). No all-prime conclusion.

## TheGammaReservePaysEulerHeadsUpToTheSquareOfTheDepth (uses RHTower PrimeMassLowerBound; Mathlib SumPrimeReciprocals)
- Depth law: cost(P) ≤ δ log A ⇒ tail ≤ δ·levyEnergy; cost(P) ≤ log A ⇒ negIndex ≤ A; negIndex ≤ ⌈exp cost(P)⌉.
- Per prime: 2·total_p ≤ 16 log p/√p. Head p ≤ Y: cost ≤ 32√Y log Y (Σ1/√n ≤ 2√Y).
- Reach: 32√Y log Y ≤ log A ⇒ head negIndex ≤ A; reach Y ≈ (log A)² up to logs; head p ≤ (log N)^a has negIndex ≤ exp(C(log N)^{a/2} log log N).
- not_summable_primeEulerMixedWeightTotal (each ≥ 1/p); exists_eulerHead_cost_gt: for every depth A some head costs more than cellGammaWeight A. Coefficient-wise Gamma payment of the whole first prime layer fails at every finite depth; the tail beyond reach needs cancellation among primes (square-root count).

## TheSharpEulerHeadCouplesDetailsToFarWindows (uses RHTower FreeLagSymbolBoundaryLayer, FreeLagTraceCertificateObstruction, SelbergPrimePolynomialHighMoments, CCM CCMFirstClockPrimePowerTowerCollapse)
- sqrtChebyshev(x) = Σ_{n≤x}Λ(n)/√n ~ 2√x (PNT form). headWindowMass(Y,γ) = Σ_{m≤Y, m<γY}Λ(m)/√m: /√Y → 2√min(γ,1) (window law); ≤ 2C√Y (Chebyshev).
- Proper prime powers: Σ_{n≤M, n not prime}Λ(n)/√n ≤ 144 M^{1/4}.
- Head p ≤ Y reindexed by prime powers: |Σ_{p≤Y}Σ_k F(p^{k+1}) − Σ_{m≤Y}F(m)| ≤ 288B·M^{1/4} if F vanishes beyond M < (Y+1)² and |F| ≤ B·2Λ(m)/√m.
- detailUnit a; coarseWindow Y b = pairs Yb ≤ n < Y(b+1) = translated coarse pair b by log Y. Mixed source of detail a vs window b at lag m = (2Λ(m)/√m)·k_{ab}(log m − log Y), |k_{ab}| ≤ 2, vanishes beyond.
- headCoupling B_Y[a,b] = finite Euler head source; |B_Y − Σ_{m≤Y} headTerm| ≤ 576(Y(b+1))^{1/4}.
- headTrace T_Y(u) = 2(H_Y(β) − H_Y(α)), α = 2be^{−u}, β = (2b+2)e^{−u}; 0 ≤ T_Y ≤ 4C√Y; T_Y/√Y → s_b(u) = 4(√min(β,1) − √min(α,1)).
- tendsto_headCoupling: B_Y[a,b]/√Y → L[a,b] = ∫h_a s_b (dominated convergence; proper powers O(Y^{1/4}) negligible).
- L lower triangular: L[a,b] = 0 for a < b (window beyond detail unreached). Diagonal L[a,a] = −4√(2a)·J_a, J_a = ∫h_a e^{−u/2} > 0 (strict convexity of e^{−s/2}) ⇒ L[a,a] < 0.
- Edge of head at m = Y visible at scale √Y.

## TheIndexOfAGrowingEulerHeadIsUnbounded (uses ACS DisjointStepsHaveLogarithmicGammaCost; SSHA TheArchimedeanPairingOfTwoAtoms)
- Mixed source bilinear in (detail, coarse) coefficients; levyEnergy(cf) = c²levyEnergy(f); levyEnergy(f+g) ≤ 2(Γf + Γg).
- Lower triangular L with nonzero diagonal ⇒ ∃σ>0: Σ_j(Σ_i x_i L_ij)² ≥ σ‖x‖² (injective ⇒ antilipschitz).
- Test: details a = 1..K, coarse windows b = 1..K at log Y + [log 2b, log(2b+2)) with coefficients (s/√Y)Lᵀx. Gamma of windows translation-invariant: O(s²/Y); details cost ≤ 2‖x‖²ΣΓ(h_a); coupling gains s·σ‖x‖².
- eventually_eulerHead_negative_family: ∀K, for large Y, every horizon X ≥ max(K, (K+1)Y − 1) carries K-dim space where Γ − head(p ≤ Y) mixed source is negative definite (s = (4ΓH + 1)/σ).
- not_exists_uniform_eulerHead_index: no uniform negative-index bound over all heads.
- eventually_logPowerHead_negative_family: ∀A > 0, heads p ≤ (log N)^A at horizon N have negative index → ∞.

## AllHigherPrimePowerMixedTailsAreGammaSmall (uses RHTower XiMassPrimePowerVerticalIdeal)
- 2Λ(p^{k+1})/√p^{k+1} = 2·xiMassPrimePowerCriticalWeight p k; (p,k) ↦ p^{k+3} injective.
- Critical weights summable over all primes and exponents ≥ 3 ⇒ higherPrimePowerMixedSource (all cubes and higher, all primes) absolutely summable; tail ≤ cost·levyEnergy/cellGammaWeight(A) (cost includes factor 2 for odd-detail correction); ∀δ ∃A δ-small; finite-head approx. Prime and square layers excluded.

## AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex
- levyEnergy − higherPrimePowerMixedSource: negative dimension ≤ A uniformly in horizon, family, profiles.

## TheSquarePrimeBoundaryHasAGammaGap (uses RHTower DirichletArchimedeanSymbolPositivity, XiLogDerivFactorization, XiLogDerivRePositiveRightOfStrip, Sieve ZetaLogDerivRegular, GammaHardyPhaseRateLevyKhintchine)
- gammaIncrementSymbol t = 2(Hardy phase rate(t) − rate(0)) = Re ψ(1/4 + it/2) − Re ψ(1/4).
- squarePrimeRegularSymbol t = 2 Re(regular part of −ζ'/ζ)(1 + 2it) (pole removed).
- Duplication + reflection: Re ψ(1/2 + it) − Re ψ(1/4 + it/2) = log 2 + π/(2cosh πt).
- Exact gap (t ≠ 0): Γ-symbol − square-regular = γ + log 4π + π/2 − π/(2cosh πt) − 2/(1+4t²) + 2Re(ξ'/ξ)(1+2it).
- Re(ξ'/ξ) ≥ 0 on Re s ≥ 1 (zero-free edge, no RH) ⇒ gap ≥ γ_Euler > 1/2 for all t. Pole of prime series separate.

## TheSquarePrimeBoundaryHasItsMeanPole (uses RHTower ConstrainedWeilFourierMultiplier, XiMassPrimeSquareAsymptoticCarrier; HTGeometry GoldenRuleSelfEnergy)
- Pole multiplier at abscissa 1 + 4πε, height 4πξ = (1/2)·half-plane Poisson kernel P_ε(ξ).
- As ε → 0+: ∫ pole·|û|² → (1/2)|∫u|² (half squared mean).
- Every polynomial envelope (1+|cξ|)^k integrable against Schwartz spectral density |û|².
- Regular zeta boundary has polynomial envelope (degree 9) on 1 ≤ σ ≤ 2 ⇒ damped regular pairing integrable for ε ≥ 0 and converges as ε → 0+ (dominated convergence).

## TheSquarePrimeSourceIsItsBoundaryPairing (uses RHTower VonMangoldtLineSeriesSwap; ArithmeticElectrostatics TheExternalFieldIsAPrimeSum)
- dampedSquarePrimeSource(u,σ) = 2Σ Λ(n)n^{−σ}·Re autocorr_u(2 log n) = ∫2Re L(Λ, σ + 4πiξ)·|û(ξ)|² (σ > 1; Fourier inversion + absolute Dirichlet summation).
- Critical square coefficient: 2Λ(n²)/√(n²) = 2Λ(n)/n.
- For SuzukiRestrictedWeilCore tests: compact support ⇒ finite cutoff N; damped source continuous in σ; at σ = 1 equals literal squarePrimeSource = 2Σ(Λ(n)/n)·corr(2 log n).
- Damped source at 1 + 4πε = pole part + regular part. squarePrimeSource_eq_regular_add_mean: literal critical square-prime source = ∫ regular boundary(ε=0)·|û|² + (1/2)|∫u|².

## TheXiEdgeFieldHasLogarithmicGrowth (uses RHTower ZetaTypicalLocalZeroCount, XiLogDerivLineOneWindowLower)
- Line-conjugate pair (β, 1−β) at Re s = 1: paired Poisson ≥ 1/(1+v²) (width-free).
- Window: Re(ξ'/ξ)(1+iT) ≥ (N(T+h) − N(T−h))/(2(1+h²)).
- exists_xi_edge_logarithmic_lower: Re(ξ'/ξ)(1+iT) ≥ c log T for T ≥ T₀ (fixed-window zero count ≥ log).

## TheSquarePrimeBoundaryRetainsGammaEnergy (uses HTGeometry GammaProjectiveBoundary; RHTower HardyZPhaseAsymptotic, XiLogDerivSymmetry)
- gammaIncrementSymbol ≥ 0, even, continuous; ≤ 2 log t for large t (digamma vertical log bound).
- Gap ≥ γ + 2Re(ξ'/ξ)(1+2it) (t ≠ 0).
- exists_squarePrime_regular_retained_gamma: ∃δ > 0: δ·Γsym(t) + γ/2 ≤ Γsym(t) − squareRegular(t) for all t (log Xi edge growth beats log Gamma at large t; compact interval by floor).

## TheSquarePrimeBoundaryIsLowerOrder (uses RHTower Sieve ZetaLogDerivIsSublogarithmic)
- Γsym(t) ≥ (log|t|)/2 for |t| ≥ T.
- Pole has zero real part off origin: squareRegular(t) = −2Re(ζ'/ζ)(1+2it), t ≠ 0.
- ζ'/ζ sublogarithmic on Re s = 1 ⇒ ∀ε ∃T: |squareRegular(t)| ≤ ε·Γsym(t) for |t| ≥ T.

## TheCenteredSquareBoundaryHasAGammaMassBound
- squarePrimeRegularSymbol differentiable (regular part analytic on Re s ≥ 1).
- Γsym(t) ≥ 16t²/(1+4t²) (first Gauss-series term): quadratic floor at 0.
- On |t| ≤ R: (squareRegular(t) − squareRegular(0))² ≤ K·Γsym(t) (divided difference bounded).
- At infinity: |centred| ≤ ε·Γsym.
- exists_centeredSquare_gamma_mass_bound: ∀ε ∃C: 2|centred(t)||a||b| ≤ εΓsym(t)(a² + b²) + Cb², uniform in t, a, b (mass charged only to second factor).

## TheSquarePrimeSourceRetainsGammaEnergy (uses RHTower WeilMarkovOddSectorTrivialZeroSquares)
- Plancherel: ∫Γsym(2πξ)|û|² = levyEnergy u (Gamma jump energy, no mass shift); ∫|û|² = ∫u².
- squarePrimeSource = ∫squareRegular(2πξ)|û|² + (1/2)(∫u)².
- squarePrimeSource_gamma_gap_core: γ∫u² ≤ levyEnergy u − squarePrimeSource u + (1/2)(∫u)².
- exists_squarePrime_retained_gamma_core: ∃δ > 0: δ·levyEnergy + (γ/2)∫u² ≤ levyEnergy − squarePrimeSource + (1/2)(∫u)², all smooth compact real cores.

## TheSquarePrimeEstimateHoldsOnCompleteProfiles (uses ACS SmoothCompleteWeilTransfer, CompleteCellVariancePayment)
- Pole-preserving smoothing: ∫poleSmooth f n = poleNormalizer⁻¹·∫f → ∫f; common support ⇒ finitely many square lags ⇒ square source converges.
- Square coercivity (gap and δ-retained Gamma) transfers to every compact BV profile, in particular complete cell profiles (averages and details both kept).

## TheCenteredSquareSourceHasAGammaMassBound (uses RHTower Suzuki SuzukiCCMMixedScrewWeilBridge)
- centeredSquarePrimeSource f = squarePrimeSource f − (1/2)(∫f)² − squareRegular(0)·∫f².
- Mixed part on cores: |centered(u+v) − centered(u) − centered(v)| ≤ ε(Γu + Γv) + C∫v² (pointwise symbol bound + |‖z+w‖² − ‖z‖² − ‖w‖²| ≤ 2‖z‖‖w‖).
- Transfers to compact BV profiles via pole-preserving smoothing (centred source converges).

## OddHigherPrimePowerMixedTailsAreGammaSmall
- oddHigherPrimePowerMixedSource: only odd exponents ≥ 3, all primes (disjoint from even powers in squarePrimeSource); dominated by higher-power budget; ∀δ ∃A δ-small tail.

## SquaresAndOddHigherMixedPowersHaveUniformFiniteIndex
- squareOddHigherGammaSourceForm = levyEnergy − squarePrimeSource (all even powers) − odd higher mixed.
- Details below A vanish ⇒ (γ/2)∫profile² ≤ form + (1/2)(∫profile)².
- exists_uniform_squareOddHigherGamma_negative_dimension: negative dimension ≤ A + 1 (A detail readouts + ordinary mean), uniform in horizon and family.

## OddHigherPrimePowersPayTheirWholeDetailBlock
- oddHigherPrimePowerPairing(u,v) = Σ_{odd exponents ≥3} w·Re⟨T_{log m}u, v⟩ on half-line L²; absolutely summable (shift contraction); quadratic source on complete profile = literal correlation sum.
- Integer translate of pair average ⊥ every target detail ⇒ source(coarse + detail) − source(coarse) = pairing(detail, complete) = mixed + pure-detail block.
- |pairing(detail tail ≥ A, complete)| ≤ cost·levyEnergy/cellGammaWeight(A) (translated-detail bound per lag); ∀δ ∃A.
- squareOddHigherRefinementSourceForm = levyEnergy − squarePrimeSource − (odd source(complete) − odd source(coarse)). Detail head A vanishing ⇒ (γ/2)∫² ≤ form + (1/2)mean²; negative dimension ≤ A + 1. Coarse odd source and first-prime source remain unpaid.

## CompleteCellAveragesAreBoundedInGammaEnergy (uses ACS DisjointStepsHaveLogarithmicGammaCost, CompleteCellGammaAccounting)
- haarGammaUpperConstant; Γ(rawCell n) ≤ const·cellGammaWeight(a)·w_n for n ≤ 2a+1; Γ(haarProfile a) ≤ 2·const·cellGammaWeight(a)·haarMass a.
- Γ(detail section) ≤ 4·const·Σ cellGammaWeight·haarMass·d² (disjoint pairs); Σ cellGammaWeight·haarMass·d² ≤ Γ(complete profile).
- Γ(details) ≤ 4c·Γ(complete); Γ(averages) + Γ(details) ≤ (2 + 12c)·Γ(complete): homogeneous, no mass error.
- Equivalence: Γ(complete) ≍ Γ(averages) + Σ cellGammaWeight·haarMass·d².
- exists_squareOddHigherRefinement_coarse_detail_reserve: after detail head A, η(Γ(averages) + weighted detail mass) + (γ/2)∫² ≤ refinement form + (1/2)mean².

## TheMixedSquareSourceHasUniformSmallTails
- Pair averages ⊥ balanced details in L² (∫avg·haar_a = q_a∫haar_a = 0); ∫complete = ∫avg; ∫complete² = ∫avg² + ∫detail².
- squarePrimeMixedSource = square(complete) − square(avg) − square(detail) = centred mixed (mean/constant corrections cancel exactly).
- |mixed| ≤ ε(Γavg + Γdetail) + C∫detail² (no coarse mass charged).
- exists_uniform_small_squarePrimeMixed_tail: ∀ε ∃A: |mixed square source with details ≥ A| ≤ ε·Γ(complete profile), uniform in horizon.

## GammaCouplingHasUniformFiniteHeads (uses ACS GammaCouplingUsesOnlyDetailMass)
- completeGammaMixed (Γ cross coarse/detail)² ≤ 128e^{1/2}·Γavg·∫detail² (ACS). cellGammaWeight(A)·mixed_tail² ≤ const·Γ(complete)².
- exists_uniform_finite_head_for_gamma_mixed: finite detail head approximates mixed Gamma block within ε·Γ(complete).

## TheFullDetailSourceRetainsCoarseGamma (uses ACS HaarCellEffectivity)
- fullDetailPrimeGap = 1 − 1/√2 > 0 (Gamma log coefficient 1 vs full-prime log coefficient 1/√2 on Haar details).
- haarLogarithmicMass = Σ cellGammaWeight·haarMass·d²; cellGammaWeight a ≤ log a + 1.
- roughWeil(detail) ≥ gap·logMass − (20 − 2·rate(0) + gap)∫detail² (full Haar Weil diagonal: all prime powers, arch mass, pole product).
- |completeGammaMixed| ≤ εΓavg + (32e^{1/2}/ε)∫detail².
- fullDetailCoupledSourceForm = Γ(complete) − Γ(detail) + roughWeil(detail) = Γ + 2rate(0)∫detail² − haarPrimeEnergy + 2cosh² − 2sinh² (entire prime series, both poles).
- (1−ε)Γavg + gap·logMass − massCost(ε)∫detail² ≤ form; detail head A ⇒ (1−ε)Γavg + (gap/2)logMass + ∫detail² ≤ form.
- Also pays all higher mixed prime powers (exponent ≥ 3): (1−ε)Γavg + (gap/4)logMass + ∫detail² ≤ form − higherMixed; negative dimension ≤ A uniformly.

## EveryMixedExponentAboveOneLeavesACoarseReserve
- fullDetailNonfirstMixedSourceForm = fullDetailCoupledSourceForm − squarePrimeMixed − oddHigherMixed (every mixed exponent ≥ 2).
- One detail head A: (1−ε)Γavg + (gap/4)logMass + ∫detail² ≤ form; negative dimension ≤ A uniformly.

## TheFullPolarNonfirstSourceHasUniformFiniteIndex
- Detail pole: 2cosh²(detail) − 2sinh²(detail) ≤ 2∫detail² (exponential moments² ≤ Σ haarMass·d²).
- fullPolarNonfirstSourceForm = Γ(complete) + 2rate(0)∫detail² − haarPrimeEnergy − squareMixed − oddHigherMixed + 2cosh²(complete) − 2sinh²(complete) (full actual pole incl. coarse and mixed polar terms).
- (1−ε)Γavg + (gap/8)logMass + ∫detail² + 2cosh²(complete) ≤ form + 2sinh²(complete); negative dimension ≤ A + 1 (detail head + single sinh readout).

## TheHaarPrimeMultiplierTailIsGammaSmall
- haarPrimeMatrixOn s (directed prime matrix restricted to multipliers s), entries ≥ 0; pairing = Σ 2M_{ab}d_a e_b.
- Row bound: Σ_b M_{ab} ≤ 16 haarMass a (horizon independent). Column bound for multipliers ≥ N: Σ_a M_{ab} ≤ (log(2b+1)/√N)·haarMass b (divisor identity ΣΛ(m|2b+1) = log(2b+1)).
- haarLogarithmicMass ≤ Γ(complete) (averages arbitrary); Σ log(2a+1)haarMass·d² ≤ (1 + 2/cgw(1))·logMass.
- Weighted Young: t|pair| ≤ (16t²/cgw(1) + (1+2/cgw(1))/√N)·logMass.
- exists_haarPrime_multiplier_tail_small: ∀ε ∃N: multipliers ≥ N contribute ≤ ε·logMass, uniform in profile, detail cutoff, horizon.

## TheFullHaarPrimeSourceHasUniformFiniteHeads
- haarPrimeEnergy (all prime powers on Haar details) = pairOn over multipliers 2..2X+1. Head error = oriented pairing(full, high target) (upward incidence).
- Multiplier m ≤ N cannot carry source index < B to target ≥ N(B+1): pairing reduces to (high source, high target) ⇒ cgw(B)·|·| ≤ logMass.
- exists_haarPrime_finite_head_logMass: ∀ε ∃A: |haarPrimeEnergy(d) − haarPrimeEnergy(head_A d)| ≤ ε·logMass (small multipliers via high-target; large via multiplier tail). Hence ≤ ε·Γ(complete); tail-only Haar prime energy ≤ ε·Γ(complete).

## TheFullNonfirstSourceRetainsAlmostAllGamma
- Detail head A ⇒ |fullPolarNonfirstSourceForm − (Γ(complete) + 2cosh² − 2sinh²)| ≤ ε·Γ(complete) (Haar prime diagonal, square mixed, odd higher mixed, constant 2rate(0)∫detail² each ≤ ε/4).
- (1−ε)Γ(complete) + 2cosh² ≤ form + 2sinh².

## TheEntireSquareSourceSharesTheFullDetailReserve
- fullSquarePolarSourceForm = fullPolarNonfirst − square(avg) = Γ + 2rate(0)∫detail² − (haarPrime(detail) − square(detail)) − square(complete) − oddHigherMixed + full pole: entire even-prime source counted once.
- Reserve: c·Γavg + (γ/2)∫avg² + (gap/8)logMass + ∫detail² + 2cosh² ≤ form + 2sinh² + (1/2)(∫complete)²; negative dimension ≤ A + 2 (detail head + sinh moment + mean).

## ThePrimePolarCutoffIsSmallInGammaNorm (uses ArithmeticCompensationTheory ThePrimePolarCutoffHasUniformFrequencyBounds)
- Eventually in S: |primePolarCutoffSymbol S t| ≤ ε e^{S/2}(1 + Γsym(t)) for all t (small on bounded intervals, bounded by 17e^{S/2} everywhere, Γsym → ∞).

## ThePrimePolarCutoffRepresentsTheFullSource
- Fourier inversion + integrable polar kernel: ∫ primePolarCutoffSymbol(S,2πξ)|û|² = 2(Σ_{n≤e^S}Λ(n)n^{−1/2}·cutoff·autocorr(log n) − ∫_0^∞ polarDensity·autocorr).
- Cutoff = 1 on correlation support (S ≥ 2·supportRadius + 1) ⇒ primeSum u unchanged.
- 2cosh² − 2sinh² = 4∫_0^∞ cosh(s/2)·autocorr(s).
- primeSum_sub_poles_eq_primePolarCutoff_integral: primeSum u − (2cosh² − 2sinh²) = cutoff multiplier pairing.

## TheFullPrimePolarSourceCancelsInGammaNorm
- Eventually in S, for cores with 2·radius + 1 ≤ S: |primeSum − poles| ≤ εe^{S/2}(Γu + ∫u²).
- exists_primePolar_gamma_bound_bv: for compact BV f supported in [−R,R], R ≥ R₀: |primeSum f − (2cosh² − 2sinh²)| ≤ εe^R(Γf + ∫f²) (prime–polar cancellation lower order than aperture mass e^R; via pole-preserving smoothing).

## EveryShortCellPaysAnyFixedMassCharge
- Single-site section: (2rate(0) + log(1/w) − spacingConstant − (e + 1))·∫f² ≤ W(f,f) for f supported in [0,w] (log gain as w → 0; pole cost bounded by e + 1).
- exists_shortProfile_weil_coercivity / exists_shortCell_weil_coercivity: ∀L ∃δ₀: any C² profile supported in an interval of width δ < δ₀ (any centre) has W(g,g) ≥ L∫g².

## AShortNewCellPaysItsOwnInteraction
- Disjoint profiles: masses add.
- exists_shortCell_diagonal_extension: old p (window R, gap d from centre b), new short cell g at b: W(p+g) ≥ W(p) − ε∫p² + L∫g² (separated mixed payment + short-cell coercivity). No sign of old form assumed.

## AnAdditionalCellPreservesTheOldSections
- Any exterior point b ∉ arithmeticSectionSupport has positive gap.
- exists_smallCell_extension: for b ∉ support, short new cell at b: (1−ε)∫p² + ∫g² ≤ W(p+g) uniformly over all old sections p and new profiles g (old widths fixed); half version.

## FixedCellWidthsSupportNestedPositiveSections
- Any strictly increasing centres b_n: envelopes min(1, (b_{n+1}−b_n)/2); new centre outside old envelope with gap; finite prefix window.
- exists_fixedCellWidths_coercive: one choice of widths w_n ∈ (0,1] such that every finite independently profiled prefix Σ_{i<N} G_i (G_i supported within w_i/2 of b_i) has W ≥ ∫(Σ G_i)². Induction with decreasing reserve a_n = 1 + 1/(n+1), losses ε_n = a_n − a_{n+1} summable. Widths chosen once, never shrunk later.
- exists_fixedLogCellWidths_coercive: centres log(n+1) (integer-log carrier).

## TheGraphNormIsControlledBySectionEnergy (uses RHTower CHMDPolarTransfer, CHMDSignedGraphPolarization)
- realTestGraphLift = inverse Doob lift into complete source graph; additive; weilForm(lift f) = W(f,f) (both poles).
- Source mass in graph = ∫f²·cosh(u/2)/riemannKernel(u); on window ≤ K∫f².
- ‖lift f‖² ≤ W(f,f) + C∫f² on window (penalty 2(1 + ‖tanh‖²)); for narrow sections (floor ∫² ≤ W): ‖lift p‖² ≤ C'·W(p,p).

## FixedCellsControlTheCompleteSourceGraph
- weightedSectionMass ω f = ∫f²ω; additive on disjoint profiles; ≥ ∫f² if ω ≥ 1.
- exists_fixedCellWidths_weighted_coercive: any continuous ω ≥ 1, fixed widths with weightedMass(prefix) ≤ W(prefix) for all finite prefixes.
- Exact: ‖lift f source‖² = weighted mass with sourceGraphMassWeight = cosh(u/2)/riemannKernel(u); ‖lift f‖² ≤ W + penalty·weightedMass.
- exists_fixedCellWidths_graph_coercive: ‖lift(prefix)‖² ≤ (1+ε)W(prefix); integer-log carrier: ≤ 2W. No lower width bound, no exhaustion of the full test space.

## TheUnboundedCellCarrierHasAWeilProjection (uses TheClosedSectionHasABoundedWeilProjection; RHTower CHMDInfiniteCriticalModes)
- cellProfileSpace (finitely supported independent profiles in fixed cells), synthesis; fixedLogCellTests = all finite sums on fixed integer-log cells (fixedLogGraphCellWidth). ‖lift f‖² ≤ 2W(f) on the whole algebraic carrier.
- closedFixedLogCellGraph = closure in source graph; coercivity ‖p‖² ≤ 2·weilForm p survives closure.
- Cusp escape (normalized, graph norm² → 2, weilForm → 0) eventually not in carrier ⇒ closed carrier ≠ ⊤ (proper, no off-line zero assumed).
- exists_fixedLogCellWeilProjection: bounded Weil projection P via coercive compression (Lax–Milgram); unique, idempotent; residual identity W(x−Px, y−Py) = W(x,y) − W(Px,Py).
- Cost: weilForm(Px) ≤ 2‖Ax‖² (A = graphWeilOperator), ‖Px‖² ≤ 4‖Ax‖²; W(x − Px) ≥ W(x) − 2‖Ax‖².
- Theta critical modes are W-null against everything ⇒ P(critical) = 0: infinite linearly independent zero-energy family survives in the complement.

## TheSectionProjectionConvergesInTheSourceGraph (uses RHTower CHMDBirmanSchwingerBound)
- weilBilin(lift f, lift g) = W(f,g). Closure of narrow section carrier keeps ‖p‖² ≤ C·weilForm p.
- Finite section projections Cauchy in Weil energy ⇒ Cauchy in graph norm ⇒ sectionGraphProjection exists in closure; weilForm = completion energy; mixed pairings = sectionCompletionPair.
- sectionGraphResidual = lift g − projection: W(res g, res h) = completedSectionResidualForm(g,h); orthogonal to the whole closed old section space.

## TheUnusedReserveReducesTheSourceCost
- sectionDualWeight(N,n,a) = 1 + ((1−a)/8)·sectionReserveWeight(N,n) ≥ 1.
- Below spacing, cells disjoint: sourceKernelEnergy(support) = Σ_n cell energies.
- weightedSectionKernelEnergy = Σ_n cellEnergy_n / dualWeight_n ≤ unweighted (= at a = 1).
- At width fraction a: Σ dualWeight·∫G_n² ≤ W(section); per-cell Young ⇒ finite projections and completion energy ≤ weightedSectionKernelEnergy; residual ≥ W(g,g) − weighted cost.

## TheCompleteCellsCaptureEveryFiniteIndex (uses ACS CompleteWeilSourceTransfer)
- completeCellSourceGram entries → literal Weil entries on common log-cell window (polarization of weilQuad = realWeilForm).
- exists_completeCell_index_capture: every finite compact C² family has a cell exhaustion whose matrices eventually carry all negative squares of the Weil Gram (lower bound only; no upper index estimate).

## TheClosedSectionHasABoundedWeilProjection (uses HTGeometry CoerciveOperatorInvertible)
- realTestGraphMap linear; graphWeilPairing bounded bilinear; graphWeilOperator A with ⟨Ap, q⟩ = W(p,q).
- closedSectionGraph (closure of narrow section range) coercive ⇒ compression invertible ⇒ bounded projection P onto closed carrier, W-orthogonal residual, unique, idempotent; equals finite-subset limit on literal tests; signed Schur subtraction on entire graph.

## TheFullWidthStillRetainsArithmeticReserve
- fullSectionRatio < 1; fullWidthPoleCost = r(e^r + 1) < 1/8 ⇒ fullWidthSectionReserve = 1/8 − cost > 0.
- Full-width sections: ∫² + reserve·sectionReserve ≤ W; (1 + reserve)∫p² ≤ W(p,p) (mass floor > 1).
- Projection and completion energy ≤ sourceKernelEnergy(support)/(1 + reserve).

## MovingArithmeticBandsDecoupleFromFixedTests
- Upper band N/2 ≤ n ≤ N translated by −log N: supported in [−log 2, 1] (fixed window); movingBandFloor(N) = 1 + reserve(1 + (1 + log N)/2) ~ log N.
- movingArithmeticBand_mass_floor: floor(N)·∫p² ≤ W(p,p). Source coupling: floor(N)·W(p,g)² ≤ sourceKernelEnergy([−log2,1], g)·W(p,p).
- movingArithmeticBand_unit_energy_pairing_tendsto_zero: energy-unit band sections become invisible to every fixed probe g (|W(p,g)| → 0 uniformly), though the cell count grows.

## FixedCoarseCellsControlTheEntireWeilIndex (uses ACS HaarCellEffectivity: exists_haarTail_roughWeil_floor)
- Full roughWeil (all primes, Gamma, poles) on complete profiles with R fixed coarse coefficients and arbitrary details: negative dimension ≤ R + A (R coarse readouts + universal detail head A, pure Haar tail form nonnegative).

## TheFullPrimeWindowCancelsTheGrowingHeadPole (uses SMAP ThePoleHyperplaneIsTheHarmonicHyperplane)
- Full prime window m ≤ (b+1)Y (beyond it every head term vanishes by support). For u ≥ log 2: √(b+1)·s_b(u + log(b+1)) = 4(√(2b+2) − √(2b))e^{−u/2} (truncations inactive).
- fullPrimeWindowCoupling(h_a)/√Y → 4(√(2b+2) − √(2b))·J_a (window PNT, dominated convergence).
- Coupling = finite Euler source over p ≤ (b+1)Y = headCoupling(p ≤ Y) + fullPrimeWindowTail = Σ over all primes of primeEulerMixedSource.
- Mixed pole (both cross terms of 2coshsinh form on detail a, window b at log Y): /√Y → same limit (∫coarse·e^{u/2} = 2(√(2b+2) − √(2b)); far window scales √Y; other term O(1/√Y)).
- tendsto_allPrimesMixedSource_sub_pole_div_sqrt: (all-prime mixed source − mixed pole)/√Y → 0. The growing-head √Y coupling of TheIndexOfAGrowingEulerHeadIsUnbounded is exactly cancelled by the pole once the full prime window is included.
- fullPrimeWindowRemainder_uniform_finite_family: cancellation uniform over bounded coefficients on any fixed finite (detail, window) family.
