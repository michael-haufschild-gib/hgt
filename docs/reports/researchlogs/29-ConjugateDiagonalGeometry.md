# ConjugateDiagonalGeometry working log (mathematical facts)
Namespace GaloisForLFunctions.ConjugateDiagonalGeometry. 61 modules.
## DefectKernel (Mathlib only)
- depthKernel k(L,d) = 2cosh(2dL) − 2 = 4sinh²(dL) ≥ 0; 4L²d² ≤ k; k = 0 ⇔ d = 0 ∨ L = 0; doubling k(2L,d) = 4k(L,d) + k(L,d)²; k(L,d) ≤ k(L,e) ⇔ |dL| ≤ |eL|; monotone in |d|.
## ZetaDepthDistribution (imports DefectKernel, APol.HeckeInvarianceOfTheCollidedPolarizationIsRH)
- CompactTest = C² compactly supported f; zetaDepth ρ = Re ρ − ½, |depth| ≤ ½; zetaWeight = mult·|tr f(ρ)|² ≥ 0, summable (zeta_summable_collided, from APol/Zeta23).
- All kernel moments Σ w·k^n converge (strip bound). heckeDefect E(f,L) = Σ w·k(L,depth) ≥ 0; PILLAR heckeDefect_eq_second_difference: E(L) = D(τ_L f) + D(τ_{−L} f) − 2D(f) (D = collidedForm).
- E ≤ k(L,½)·D; depthTail: k(L,b)·tail(|depth| ≥ |b|) ≤ E (Chebyshev); 4L²·Σ w·depth² ≤ E; E(2L) = 4E(L) + Σ w·k². No zero-density or positivity assumption.
## TwoScaleDepthRigidity (imports ZetaDepthDistribution, HTGeometry.PairwiseVarianceIdentity)
- depthDispersion = D(E(2L) − 4E(L)) − E(L)² = ½ Σ_{ρ,σ} w_ρ w_σ (k_ρ − k_σ)² ≥ 0 ⇒ E(L)² ≤ D(E(2L) − 4E(L)). Equality ⇔ all weighted zeros have one absolute depth |depth·L| (unit_scale_shell_rigidity). Two scales read variance of depth, not zero depth.
## SourceCurvatureCalculus (imports HTGeometry.ComplexC2Laplacian, ComplexLaplacianGreenIdentity)
- radialLogPotential ½log(|z|² + ε): C², Δ = 2ε/(|z|² + ε)² > 0. Δ(u∘g) = |g'|²Δu∘g (holomorphic g). source_green_identity ∫φΔu = ∫Δφ·u (φ compact C², u C², no decay on u).
## XiSourceCurrent (imports ZetaDepthDistribution, HTGeometry.EntirePoincareLelong, RHTower.WindingXiCircle, CompletedPrimeFluxFittingAttachment, EvenSectorFullPositivity)
- sourceCutoff n: smooth bump, 1 on |z| ≤ n+1, eventually 1 at each z. tr f is entire ⇒ C² in real coordinates. sourceDepthKernel |tr f(z)|²·k(L, Re z − ½)^j (nonholomorphic, C²).
- sourceCurrentReading = ∫ log|ξ|·Δ(cutoff·kernel). xi_realDivisorPairing_eq_carrier: compact pairing = Σ_ρ mult·φ(ρ) (zero multiplicity of ξ = of ζ in strip). PILLAR sourceCurrentReading_eq_trace = 2πΣ cutoff·w·k^j (Poincaré–Lelong for entire ξ). Exhaustion: reading → 2πΣ w·k^j (dominated convergence); collided form and Hecke defect are limits of integrals defined only from ξ and the test. Not an estimate by primes.
## XiLogRegularization (imports SourceCurvatureCalculus, HTGeometry.PlanarLogNormIntegrability, RHTower.RiemannTower)
- sourceRegulator 1/(n+1). xiLogPotential ½log(|ξ|² + ε); xiCurvatureDensity ε|ξ'|²/(|ξ|² + ε)² ≥ 0; Δ potential = 2·density.
- log|ξ| locally integrable (meromorphic); ξ ≠ 0 a.e.; |½log(r²+ε)| ≤ r + |log r| (ε ≤ 1). Regularized potentials → log|ξ| pointwise off zeros and in L¹_loc against continuous compact weights (any multiplicity).
## XiPositiveSourceMetric (imports XiSourceCurrent, XiLogRegularization)
- xiPositiveReading = ∫ cutoff·kernel·density_k ≥ 0. 2∫φ·density = ∫ potential·Δφ (Green). Regulator removal → ½∫log|ξ|Δφ = π·Σ cutoff·w·k^j.
- xiSourceMoment = π^{−1}·lim_n lim_k reading (definition contains no zero sum) = Σ w·k^j. xiSourceMetric = collidedForm (PILLAR xiSourceMetric_eq_collided); moment 1 = Hecke defect.
- sourceTranslate; translation second difference holds on positive densities before limits (xiPositiveReading_second_difference); xiSourceMetric second difference = first source moment ≥ 0.
## UniversalSourceWeight (imports ZetaDepthDistribution)
- universalSourceWeight W(z) = e^{(Re z)²}/(1 + (Im z)²)² > 0, C². PILLAR normSq_tr_le_universalSourceWeight: every compact C² test has |tr f(z)|² ≤ C_f·W(z) (decay |tr f| ≤ e^{|Re z−½|a}B/(1+|Im z|)², a = support radius; 2|x−½|a ≤ a²+a+x²). summable_universalSourceWeight: Σ mult·W(ρ) < ∞ (W(ρ) ≤ (5e/4)/(1+|γ(ρ)|²)). One test-independent weight controls all tails.
## XiLogL1Convergence (imports XiLogRegularization)
- log|ξ| ≤ regularized potential off zeros; xiLocalLogError (local L¹ error) = difference of integrals; → 0 on every disc (no zero-free or simplicity condition).
## SourceCutoffControl (imports XiPositiveSourceMetric)
- sourceCutoffDerivative, sourceCutoffLaplacian as bounded continuous functions; sourceCutoffControl = 1 + sup norms. tsupport Δφ ⊆ tsupport φ; Δ(cutoff·φ) = 0 outside closedBall(0, n+2).
## StripSourceCutoff (imports SourceSquareCalculus)
- stripSourceScale 1/(4(n+1)); stripSourceCompression (re, scale·im); stripSourcePoint = compression − ½; stripSourceCutoff n = bump₀ ∘ point: support has |Re z − ½| ≤ 2 (fixed width) and |z| ≤ 11(n+1); = 1 on strip 0 ≤ Re ≤ 1, |Im| ≤ n+2. Affine pullback formulas; directional derivatives bounded uniformly in n (vertical ones scaled by ≤ 1); stripSourceCutoffControl fixed constant.
- Δ(stripSourceCutoff) = ∂₁² bump + scale²·∂_I² bump; |Δ| ≤ fixed constant (height-independent); Δ(cutoff·φ) vanishes off support / outside closedBall(0, 11(n+1)).
## SourceLocalCutoff (imports StripSourceCutoff, RHTower.SelbergPlanarTestScaling)
- sourceLocalCutoff c r = bump₀ rescaled: 1 on closedBall(c,r), support ⊆ closedBall(c,2r), Δ = r^{−2}·Δbump₀(…), |Δ| ≤ control/r². For centre in the zero strip with |Im c| ≤ n/2, r ≤ 1/8: stripSourceCutoff = 1 on its support ⇒ cutoff·local = local (no cutoff error).
## SourceLocalTrace (imports SourceLocalCutoff, CommonSourceRegulator, RHTower.ModulusSlopeQuantization)
- PILLAR sourceLocalTrace_mass_sandwich: xiBallOrderSum(c,r) ≤ zetaSourceTrace(local cutoff) ≤ xiBallOrderSum(c,2r) (multiplicities). Zero-free disc ⇒ order sum 0; positive local trace ⇒ zero in closedBall(c,2r); zero in closedBall(c,r) ⇒ trace ≥ 1.
## CommonSourceRegulator (imports XiPositiveSourceMetric, UniversalSourceWeight, XiLogL1Convergence, SourceCutoffControl)
- xiCompactSourceReading n k φ = π^{−1}∫cutoff·φ·density_k; xiCurrentPairing φ = (2π)^{−1}∫log|ξ|Δφ; zetaSourceTrace φ = Σ mult·φ(ρ). xiCurrentPairing_eq_trace (compact C²).
- sourceLocalAccuracy e^{−n⁴}/control. commonSourceIndex n = least k ≥ n with |reading(W) − pairing(cutoff·W)| < 1/(n+1) and local log error on disc(0,n+2) < accuracy (Nat.find; defined from ξ, ξ', integration only). commonSourceReading φ n = reading at that index.
- Exhaustion of a summable trace is regulator-independent; commonSourceReading W → trace W (mass of universal weight fixed); for compact C² φ, commonSourceReading φ → zetaSourceTrace φ (one schedule for all tests).
## CommonSourceMetric (imports CommonSourceRegulator)
- commonSourceReading monotone, additive, linear at every finite stage (positivity of density). Exhaustion sandwich lemma.
- PILLAR tendsto_commonSourceReading_of_dominated: nonnegative C² φ ≤ C·W ⇒ commonSourceReading φ → zetaSourceTrace φ (lower bound cutoff·φ, upper bound cutoff·φ + C(W − cutoff·W); mass of W fixed by the schedule).
- tendsto_commonSourceReading_collided: one test-independent sequence recovers collidedForm(f) for every compact test. sourceDepthKernel second difference raises moment order by one; every moment kernel ≤ C·W (induction); all depth moments and the Hecke defect recovered by the same sequence.
## ThetaSourceMetric (imports CommonSourceMetric, RHTower.ThetaTailFirstMomentKreinTransform)
- thetaSourceAmplitude ∫θ_full(x)e^{(½−z)x}dx = ξ(z); thetaSourceFirstMoment ∫xθ e^{(½−z)x} = −ξ'(z). thetaSourceCurvature η|M₁|²/(|M₀|² + η)² = xiCurvatureDensity. thetaSourceMomentReading ≥ 0 = commonSourceReading; literal theta integrals recover all collided depth moments, collided form, Hecke defect.
## XiCompactCurrentError (imports XiPositiveSourceMetric, XiLogL1Convergence)
- PILLAR abs_xiCurvatureReading_sub_current_le: |∫φ·density_k − ½∫log|ξ|Δφ| ≤ ½·B·localLogError(c,R,k) when Δφ supported in closedBall(c,|R|) with |Δφ| ≤ B. No zero separation.
## CommonSourceError (imports CommonSourceRegulator, XiCompactCurrentError)
- abs_commonSourceReading_sub_current_le: |commonSourceReading φ n − pairing(cutoff·φ)| ≤ (2π)^{−1}·B·e^{−n⁴}/control_n.
## SourceSquareCalculus (imports SourceCutoffControl, DifferentialGeometry Laplacian)
- Δ|g|² = 4|g'|² (holomorphic g). |∂_v|g|²| ≤ 2|g||g'||v|. Product Laplacian Δ(uφ) = uΔφ + φΔu + 2∂₁u∂₁φ + 2∂_Iu∂_Iφ. |Δ(cutoff·|g|²)| ≤ 4·control·B² when |g|,|g'| ≤ B.
## SourceTransformGrowth (imports UniversalSourceWeight, XiSourceCurrent, Mathlib Liouville)
- |tr f(z)| ≤ A e^{|z|²} (A ≥ 1). shiftedSourceTransform e^{(z−½)u}·tr f(z − iτ) entire; |·| ≤ A exp(|z − iτ|² + |u|(|z| + ½)). Cauchy on unit circle: value and derivative ≤ A exp((R+1+|τ|)² + |u|(R + 3/2)) on |z| ≤ R.
## SourceTestApertureBounds (imports SourceTransformGrowth)
- sourceTestSize = 4(‖f‖₁ + ‖f''‖₁). |tr f(z)| ≤ e^{|Re z−½|a}·size/(1+|Im z|)² (support in [−a,a]); |tr f|² ≤ size²e^{2|Re z−½|a}/(1+Im²)²; on strip 0 ≤ Re ≤ 1: ≤ size²e^a/(1+Im²)²; whole plane |tr f| ≤ size·e^{a²+a}e^{|z|²}.
## SourceStripTransformBounds (imports SourceTestApertureBounds)
- On |Re z − ½| ≤ R: |tr f| ≤ size·e^{Ra} (height-independent); shifted transform ≤ size·e^{R(a+|u|)} (ordinate modulation free); value and derivative ≤ size·e^{(R+1)(a+|u|)}.
## SourceMovedTests (imports XiPositiveSourceMetric, SourceTransformGrowth, APol.ThePriceOfEllipticLocalization)
- sourceTwist τ (ordinate modulation) stays in CompactTest; translations compose; tr(translate u (twist τ f)) = shiftedSourceTransform f u τ.
## SourceMomentLaplacianBound (imports SourceMovedTests, SourceSquareCalculus, CommonSourceMetric)
- sourceSquareEnvelope A n τ d = 4·control_n·A²·exp(2((n+3+|τ|)² + d(n+7/2))), monotone in d. |Δ(cutoff·|tr moved f|²)| ≤ envelope(|u|) on |z| ≤ n+2. Cutoff Laplacian respects the moment recurrence; |Δ(cutoff·moment_j of moved f)| ≤ 4^j·envelope(|u| + j|L|) (induction via second differences, no differentiation of k^j).
## StripSourceMomentBounds (imports StripSourceCutoff, SourceStripTransformBounds, SourceMomentLaplacianBound)
- Fixed-strip version: |Δ(stripCutoff·|g|²)| ≤ 4·stripControl·B². stripSourceSquareEnvelope = 4·stripControl·size²·e^{6(a+d)}. Ordinate motion free on the strip support. |Δ(stripCutoff·moment_j(moved f))| ≤ 4^j·envelope(|u| + j|L|).
- abs_laplacian_stripCutoff_aperture_moment_le(_global): physical + Hecke aperture a + j|L| ≤ 2log(n+1) ⇒ |Δ| ≤ 4^{j+1}·stripControl·size²·(n+1)^{12} everywhere (polynomial cost of logarithmic aperture).
## SourceWindowError (imports CommonSourceError, SourceMomentLaplacianBound, RHTower.RiemannGaussian.GaussianArchimedeanContour)
- sourceMomentCurrentError_le: |commonReading(moment_j twist τ) − pairing(cutoff·…)| ≤ (2π)^{−1}4^{j+1}A²·exp(−n⁴ + 2((n+3+|τ|)² + j|L|(n+7/2))).
- Window |τ| ≤ n, j|L| ≤ 2log(n+1): envelope (2π)^{−1}4^{j+1}A²exp(−n⁴ + 50n² + 56) → 0. PILLAR commonSourceReading_uniform_cutoff_current: uniform in τ, L over the moving window. Divisor tail is separate.
## SourceRegularityWindow (imports SourceWindowError)
- For any fixed aperture coefficient b (j|L| ≤ b·log(n+1), |τ| ≤ n): error ≤ 4^j·(2π)^{−1}4A²exp(−n⁴ + (36+14b)(n²+1)) → 0 (quartic regulator decay absorbs any logarithmic aperture).
## MovingSourceTailControl (imports SourceMovedTests, UniversalSourceWeight)
- k(L, depth ρ) ≤ 2e^{|L|}. Zeros with |Im ρ| ≤ n are inside cutoff n. Outside cutoff, |τ| ≤ n/2, j|L| ≤ 2log(n+1): W(ρ − iτ)·k^j ≤ 40e·2^j/(1 + |γ(ρ)|²) (ordinate comparable to distance from moving centre; fourth-order decay absorbs (n+1)²). sourceDepthKernel_moving_tail_bound: one summable majorant C_f/(1+|γ(ρ)|²) for all omitted moving moments.
## MovingSourceTail (imports MovingSourceTailControl, CommonSourceRegulator)
- sourceReferenceTail n = Σ(1 − cutoff_n)·mult/(1 + |γ(ρ)|²) → 0 (dominated convergence; no zero-counting premise). moving_depth_trace_tail_le: |trace(moment) − trace(cutoff·moment)| ≤ C·tail_n uniformly in window. uniform_moving_depth_trace_tail.
## SourceRegularityTail (imports MovingSourceTail, SourceTestApertureBounds, RHTower.ImaginaryShiftQuadraticFourierDefect)
- sourceRegularitySize f r = 2^r(‖f‖₁ + ‖f^{(r)}‖₁); C^r test: |tr f| ≤ e^{|Re−½|a}·size_r/(1+|Im|)^r; on strip |tr f|² ≤ size_r²e^a/(1+|Im|)^{2r}.
- PILLAR sourceDepthKernel_regularity_tail_le / source_regularity_moving_trace_tail_le: C^{k+2} test pays aperture j|L| ≤ (2k+2)log(n+1); tail ≤ (5·2^{2k+2}size_{k+2}²e^a·2^j)·sourceReferenceTail n. Regularity buys logarithmic Hecke aperture linearly.
## SourceApertureMovingTail (imports SourceTestApertureBounds, MovingSourceTail)
- Shared aperture a + j|L| ≤ 2log(n+1): omitted moment ≤ size²·40·2^j/(1+|γ(ρ)|²); tail bound size²·40·2^j·sourceReferenceTail n (uniform in test up to size²).
## StripSourceTail (imports StripSourceCutoff, SourceApertureMovingTail)
- Zero not retained by strip cutoff ⇒ outside radial cutoff (radial cutoff 0 there). Strip exhaustion inherits the same tail bound.
## MovingSourceMetric (imports SourceWindowError, MovingSourceTail)
- PILLAR commonSourceReading_uniform_moving_moments: one regulator schedule recovers Σ w(twist τ f)·k^j uniformly over |τ| ≤ n/2, j|L| ≤ 2log(n+1) (current error + tail error).
## UniformThetaSourceMetric (imports ThetaSourceMetric, MovingSourceMetric)
- thetaSource_uniform_moving_moments / _collided / _heckeDefect: literal theta amplitude and first-moment integrals compute moving collided moments, norms, Hecke defects uniformly in the window. Evaluates the positive trace and its Hecke defect; does not force the defect to vanish.
## TheConductorForcingGap (imports RHTower.IsolatedDeepZeroHodgeIndex)
- companionCost (majorant of the companion-forcing theorem). deepZeroEnergy ≤ N/2·e^{δa}; 2E² ≤ N²/2·e^{2δa}. forcing_requires_exponential_aperture: successful certificate ⇒ 768A log(|γ|+3) < e^{2δa}. PILLAR conductor_forcing_disjoint: for 0 ≤ δ ≤ ½, conductor horizon C + (4+ε)e^a + 2 ≤ log(1 + |γ|/8) and forcing are incompatible at every height (no asymptotic threshold). The deep-zero forcing route is closed by the conductor horizon.
## XiCanonicalLogBound (imports HTGeometry.PlanarLogSquare, RHTower.RiemannGaussian.FiniteToEntireBoundaryLowerBound, GaussianXiGrowth, RiemannTower)
- Gaussian ξ = −2ξ. xiCanonicalLogMass n z = Σ_divisor mult·planarLogKernel(2R_n)(z − i) ≥ 0 over the canonical ball divisor. Residual lower bound log|residual| ≥ −2A(R_n+1)² on |z| ≤ R_n/4 (growth |ξ| ≤ e^{A(|z|+1)²}). PILLAR exists_abs_log_norm_gaussianXi_canonical_bound: |log|ξ(z)|| ≤ 2A(R_n+1)² + canonical log mass on inner discs (multiplicities kept).
## XiLogSquareIntegral (imports XiCanonicalLogBound, HTGeometry.PlanarLogSquareMass)
- Canonical mass = finite sum; square-integrable; ∫_disc mass² ≤ (total multiplicity)²·8π(2R)². Standard ξ: +log 2. Combined with zero count from growth ⇒ PILLAR exists_xi_log_square_polynomial_bound: ∫_{|z| ≤ n+2} log²|ξ| ≤ C(n+1)⁶ for one C.
## XiArbitraryRegulator (imports XiPositiveSourceMetric, XiLogL1Convergence)
- xiLocalPotentialError η (arbitrary positive regulator); Green identity at any η > 0; |∫φ·density_η − ½∫log|ξ|Δφ| ≤ ½B·localPotentialError(η).
## XiExpRegulatorError (imports XiLogSquareIntegral, XiArbitraryRegulator, SourceCutoffControl, HTGeometry.LogRegularizationSquareError)
- explicitSourceLogScale K_n = e^{(n+1)⁴}·control_n; explicitSourceRegulator e^{−K_n} (prescribed, no error test, no divisor coordinates). Pointwise |potential(e^{−K}) − log|ξ|| ≤ ½e^{−K/2} + (8/K)log²|ξ| (K ≥ 4). PILLAR exists_explicitSourceLocalError_bound: control_n·localError ≤ (π(n+2)²/2 + 8C(n+1)⁶)e^{−(n+1)⁴}.
## PolynomialSourceScale (imports StripSourceCutoff, XiExpRegulatorError)
- stripSourceIntegerControl = ⌈stripControl⌉; polynomialSourceLogScale K_n = M(n+1)^{20}; polynomialSourceRegulator e^{−K_n}; polynomialThetaIntegerCutoff N_n = (M+4)(n+1)^{20}. K_n ≥ 4; K + 4 ≤ N; 3K ≤ (N+1)²; control/K ≤ (n+1)^{−20}; control·e^{−K/2} ≤ 2(n+1)^{−20}; control·e^{K − (N+1)²} ≤ (n+1)^{−20}. Everything polynomial in height.
## PolynomialSourceError (imports PolynomialSourceScale)
- ∫_{|z| ≤ 11(n+1)} log²|ξ| ≤ C(n+1)⁶. PILLAR exists_polynomialSourceLocalError_bound: stripControl·localError(polynomial regulator, disc 11(n+1)) ≤ D/(n+1)^{14}.
## ExplicitSourceWindowBounds (imports SourceWindowError)
- Window exponent ≤ 50n² + 56; π(n+2)²/2 + 8C(n+1)⁶ ≤ (2π+8C)(n+1)⁶; combined ≤ (2π+8C)e^{−n⁴ + 56n² + 62} → 0.
## ExplicitSourceMetric (imports XiExpRegulatorError, ExplicitSourceWindowBounds, MovingSourceMetric)
- explicitSourceReading φ n = π^{−1}∫cutoff·φ·density(explicit regulator). Current error ≤ (2π)^{−1}·B·localError; moving moment error ≤ (2π)^{−1}4^{j+1}A²(2π+8C)e^{−n⁴+56n²+62}. PILLAR explicitSourceReading_uniform_moving_moments: the prescribed regulator recovers all moving collided moments uniformly in the window.
## ExplicitThetaSourceMetric (imports ThetaSourceMetric, ExplicitSourceMetric)
- explicitThetaSourceMomentReading ≥ 0 = explicitSourceReading; uniform moving moments, collided norm, Hecke defect from literal theta integrals with prescribed regulator.
## SourceReferenceTailArithmetic (imports MovingSourceTail, RHTower.LorentzianZeroMass, ACS.ZeroDensityFilteredWeilPositivityAndCoercivity)
- sourceReferenceTail n ≤ 2·lorentzMassW(n,0) (omitted zeros have |Im| > n; 1/(1+|γ|²) ≤ 2/(n²+Im²)) ≤ (16/n)·Re(ξ'/ξ)(widthPoint n) ≤ (16/n)(C + log(n+4)). Tail controlled by right-half-plane ξ data: O(log n/n).
## ExplicitThetaErrorCertificate (imports ExplicitThetaSourceMetric, SourceReferenceTailArithmetic)
- exists_explicitThetaSource_moving_error_bound: error ≤ B e^{−n⁴+56n²+62} + D·tail_n; _sourceLogDeriv_ and PILLAR _logarithmic_error_bound: ≤ B e^{…} + D(16/n)(C + log(n+4)). Explicit arithmetic error certificate.
## FiniteThetaRegulatorScale (imports XiExpRegulatorError, RHTower.ThetaCusp.ThetaCuspFiniteAmplitudeBounds)
- explicitThetaIntegerCutoff N_n = ⌈K_n⌉ + n + 10; control ≤ K ≤ e^K; (n+1)⁴+1 ≤ K; 2K − K² ≤ −(n+1)⁴; K² + (n+10)² ≤ (N+1)²; theta amplitude envelope² at radius n+2 = c·e^{(n+19/2)²/12}. finiteTheta_potential_envelope_le: control·(tail const·envelope²·e^{K−(N+1)²}) ≤ c·e^{−(n+1)⁴}.
## FiniteThetaSourceCurvature (imports FiniteThetaRegulatorScale, ThetaSourceMetric, HTGeometry.RegularizedLogStability)
- finiteThetaSourcePotential/Curvature: same construction with finite integer theta amplitude (N summands); Δ = 2·curvature ≥ 0 (finite amplitude entire though source has a cusp). Potential stability: |finite − ξ potential| ≤ tailConst·envelope(R)²e^{−(N+1)²}/η on |z| ≤ R. With explicit regulator and cutoff N_n: control·|error| ≤ finiteThetaPotentialConstant·e^{−(n+1)⁴}. Green identity for finite curvature.
## PolynomialThetaPotential (imports PolynomialSourceScale, FiniteThetaSourceCurvature, RHTower.ThetaCusp.ThetaCuspStripAmplitudeBounds)
- Strip version |Re z| ≤ R (ordinate-free); stripThetaPotentialConstant; on stripCutoff support stripControl·|error| ≤ const/(n+1)^{20} with polynomial regulator and polynomial prefix.
## FiniteThetaReadingError (imports FiniteThetaSourceCurvature, ExplicitSourceMetric)
- finiteThetaSourceReading φ n = π^{−1}∫cutoff·φ·finite curvature. |finite − explicit reading| ≤ (2π)^{−1}·B·const·e^{−(n+1)⁴}·π(n+2)² (B from Laplacian/control). Moving window: ≤ (2π)^{−1}4^{j+1}A²·4π·const·e^{−n⁴+56n²+62}.
## FiniteThetaReadingsRecoverCompactCurrents (imports FiniteThetaReadingError)
- exists_finiteTheta_compact_current_error: |finite reading φ − zetaSourceTrace φ| ≤ B e^{−n⁴+56n²+62} eventually. PILLAR tendsto_finiteThetaSourceReading_compact: finitely many integer theta summands (prescribed, polynomially many in log-scale) recover every compact C² divisor test.
## FiniteThetaProductCurrents (imports FiniteThetaReadingError)
- exists_uniform_finiteTheta_compact_current_error: one K for all compact C² φ with support inside the cutoff and |Δφ| ≤ B: |finite reading − trace| ≤ K·B·e^{−n⁴+56n²+62}.
- thetaTestStage R n B = n + R + 4 + ⌈B⌉ (stage dominates support radius and differential cost); −x⁴+56x²+62 ≤ −x for x ≥ 8 ⇒ error along this stage → 0 for any smooth compact test sequence (tendsto_thetaTestStage_error).
- finite reading: nonneg, monotone, linear, finite sums, |·| ≤ reading of |·|, continuous in a parameter family (dominated), Lipschitz in pointwise error.
- PILLAR abs_finiteThetaProductSourceReading_sub_finitePair_le: positivity telescopes separate row and column errors into a product-current error (iterated reading of a pair test vs Σ m(z)m(w)F(z,w)) ≤ A(reading χ + Σ m χ).
- Pair test separate Laplacians continuous; pairTestDifferentialBound (sup of row/column Laplacians on the support + cutoff Laplacian norm) ≥ 1, symmetric; global row bound ≤ bound·cutoff_{R+1}(z). zetaSourceTrace on a ball = finite multiplicity sum.
## HorizontalCollisionGaussian (imports RHTower.EulerShiftPairIncidenceCurrent, FiniteThetaReadingError, Mathlib SmoothTransition)
- horizontalCollisionGaussian q z w = e^{−q(Im z−Im w)²}(1 − e^{−q(Re z−Re w)²}) = e^{−q ΔIm²} − e^{−q|z−w|²} ≥ 0, zero on diagonal. finiteCoordinateGap / finiteCollisionGap (least nonzero coordinate separation) > 0.
- On finite divisor (S, m): |Σ m m·G_q − Σ m m·[Im z = Im w, z ≠ w]| ≤ (Σm)²e^{−qδ²}. Gaussian kernel tends to the horizontal collision indicator.
- collisionHeightCutoff T n y (smooth, → indicator of [0,T)); collisionWindowCutoff = sourceCutoff·height cutoff; collisionWindowPairTest = cutoff⊗cutoff·G_{n²} (C², |·| ≤ 1, compactly supported). collisionWindowRadius T = ⌈|T|⌉ + 2; window cutoff → indicator of stripZeros T at zeros.
- exists_xiWindowGaussianPairSum_error: |Σ mult·mult·G_q over strip zeros − xiHorizontalCollisionCharge T| ≤ (total order)²e^{−qδ²}.
## ThetaPrefixesReadHorizontalCollisionCharge (imports FiniteThetaProductCurrents, HorizontalCollisionGaussian, FiniteThetaReadingsRecoverCompactCurrents)
- finiteThetaPairSourceReading F n = iterated finite readings. exists_finiteTheta_pair_current_error: |pair reading − Σ_z Σ_w m m F| ≤ ε(2·reading(cutoff) + ε), ε = K·B·e^{−k⁴+56k²+62} (B = separate Laplacian bound). thetaCollisionStage (stage dominating the sharpening Gaussian test's differential cost); finiteThetaCollisionReading; error → 0.
- collisionWindowSeparationSet adds endpoints 0, iT; collisionWindowGap (min nonzero coordinate / endpoint separation) > 0; threshold ⌈1/gap⌉: beyond it window cutoffs are exact indicators on the finite divisor and the pair sum equals the Gaussian window sum.
- finiteThetaCollisionReading_error: |reading − xiHorizontalCollisionCharge T| ≤ ε(2Q+ε) + (total order)²e^{−n²δ²}. PILLAR tendsto_finiteThetaCollisionReading: integer theta prefixes recover the multiplicity-weighted horizontal collision charge (no divisor locations used). PILLAR eventually_floor_finiteThetaCollisionReading: rounding eventually gives the exact integer.
## PolynomialThetaReadingError (imports PolynomialThetaPotential, PolynomialSourceError, StripSourceMomentBounds)
- polynomialSourceReading (strip cutoff, polynomial regulator); polynomialThetaSourceReading (finite prefix). |finite − full| ≤ (2π)^{−1}B·const·(n+1)^{−20}·π(11(n+1))²; for moving moments in aperture a + j|L| ≤ 2log(n+1): ≤ 4^j size²·242·const/(n+1)⁶. exists_polynomialSourceMomentCurrentError_bound: |full − current| ≤ 4^j size²·E/(n+1)² (universal E). Polynomial (not quartic-exponential) rates with polynomial resources.
## FiniteThetaMetric (imports FiniteThetaReadingError, ExplicitThetaErrorCertificate)
- finiteThetaSourceMomentReading ≥ 0. finite ≈ explicit uniformly; PILLAR finiteThetaSource_uniform_moving_moments: prescribed finite integer theta prefix + regulator recover Σ w·k^j uniformly over |τ| ≤ n/2, j|L| ≤ 2log(n+1); logarithmic error certificate B e^{−n⁴+56n²+62} + D(16/n)(C + log(n+4)); moving collided form and Hecke defect.
## FiniteThetaApertureMetric (imports FiniteThetaMetric, SourceApertureMovingTail)
- e^{2(a²+a)}e^{−n⁴+56n²+62} ≤ e^{−n⁴+68n²+66} for a ≤ 2log(n+1). PILLAR exists_finiteThetaSource_aperture_error_bound: one B for all tests, orders, motions: |reading − trace|/4^j ≤ size²(B e^{−n⁴+68n²+66} + 40·tail_n); logarithmic form with (640/n)(C + log(n+4)). finiteThetaSource_uniform_test_aperture_moments: threshold N chosen before test (size ≤ 1), aperture, order, motion.
## PolynomialThetaMetric (imports PolynomialThetaReadingError, StripSourceTail, SourceReferenceTailArithmetic, MovingSourceMetric)
- polynomialThetaSourceMomentReading ≥ 0 (strip cutoff, polynomial regulator, polynomial prefix). exists_polynomialThetaSource_aperture_error_bound: |reading − trace|/4^j ≤ size²(B/(n+1)² + 40·tail_n).
- exists_polynomialThetaSource_aperture_logarithmic_bound: ≤ size²(B/(n+1)² + (640/n)(C + log(n+4))). polynomialThetaSource_uniform_test_aperture_moments (one stage for whole normalized family).
## PolynomialThetaLocalMetric (imports PolynomialThetaReadingError, SourceLocalCutoff)
- polynomialSourceLocalRadius r_n = 1/(16(n+1)⁶) ≤ 1/8; 1/r² = 256(n+1)^{12}. polynomialThetaLocalReading n c ≥ 0. PILLAR exists_polynomialThetaLocalReading_error_bound: |local reading − zetaSourceTrace(local bump)| ≤ E/(n+1)² uniformly in centres c in the strip with |Im c| ≤ n/2 (no zero-free boundary, no separation bound).
## PolynomialThetaLocalSelection (imports PolynomialThetaLocalMetric, SourceLocalTrace)
- exists_polynomialThetaLocalReading_mass_sandwich: xiBallOrderSum(c,r_n) ≤ reading + E/(n+1)², reading − E/(n+1)² ≤ xiBallOrderSum(c,2r_n). PILLAR polynomialThetaLocalReading_uniform_zero_detector: ∃N, ∀n ≥ N, ∀c in window: zero in closedBall(c,r_n) ⇒ reading > ½; reading > ½ ⇒ zero in closedBall(c,2r_n). A finite arithmetic theta source localizes zeros to radius ~n^{−6} uniformly at height ≤ n/2.
## ThetaSourceRegularityMetric (imports SourceRegularityWindow, SourceRegularityTail, ThetaSourceMetric, MovingSourceMetric)
- thetaSource_uniform_regularity_moments: C^{k+2} test, window j|L| ≤ (2k+2)log(n+1): normalized moments uniform. PILLAR thetaSource_uniform_smooth_log_windows: smooth tests admit every fixed logarithmic Hecke aperture |L| ≤ c·log(n+1) and every moment order along the same schedule.
