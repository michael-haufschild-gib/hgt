# Theta folder → stage 3: Lean programme ledger

Goal: formalize, unconditionally, every paper theorem of every card in this folder; move each
card to `3-formalized/theta/` when all its displayed results have closed Lean theorems
(`lake env lean` clean, `#print axioms` = propext/Classical.choice/Quot.sound only, wired into
`RHTower.lean`). Delete this file when the folder is empty.

## Shared layers (build once, reuse)

| Layer | Content | Module | Status |
|-|-|-|-|
| L1 deletion | finite prime deletion `D_S`, atom Mellin for complex `w`, `L_w k_S = XiC(iw)∏(1-p^{-1/2-w})`, coprime atom sum | `ThetaPrimeDeletionMellin` (+ `ThetaPrimeDeletionSpectralEscape`: `PrimeExhaustion`, real Mellin laws, positivity) | done |
| L2 flux | normalized flux `b_f`, `b_k = 2π∑n²e^{-πn²t}`, shift law, CM ⇔ positive rate measure, dominated representation | `ThetaCriticalFluxBernstein` (+ `ThetaFluxSource`, linearity, deletion flux, rate lattice in `ThetaPrimeDeletionBernsteinPureRay`) | done |
| L2b gauges | real-shift gauges `∑ c_i k(·+s_i)`: flux atom expansion, grouped Bernstein criterion, rate-coefficient cone, `L_w g = M(w) XiC(iw)`, zero-order transfer | `ThetaTranslationGaugeFlux` | done |
| L2c measure gauges | `∫ k(·+s) dν`, Fubini flux, Laplace laws, CM under integrals/limits, seed limit, signed Laplace positivity, all-sieve theorem | `ThetaTranslationMeasureGauge` | done |
| L2d rate measures | `A_n`, deletion parts, Euler sums, window-finite Möbius classification (gap / `M_q`, `q > 3/2`), unbounded Bernstein–Widder, Laplace order, deleted fluxes, Tonelli flux of positive (possibly infinite) translation mixtures | HTGeometry `RateMobiusInversion`; `ThetaRateLaplaceBernstein`, `ThetaRateMobiusSourceTransfer` | done |
| L3 zero division | outward sine Green operator `T_α`, relative bounds, ODE, Fourier division, complex divisions along lists, `P_L`, basis sources `ŝ_j P = F z^{2j}` | `ThetaZeroDivisionSource`, `ThetaZeroDivisionRealization`, `ThetaEndpointMomentFiltration` | done |
| L4 renewal | `P,ν,Q,D`, renewal log series, `Xi(2iλ)=(a+λ)D(λ)+(a-λ)D(-λ)`, cosh factorization, waiting-time law `μ`, phase `Φ`, exit density, compound workload, quadrant law | `ThetaRenewalIncrement`, `ThetaRenewalLogKernel`, `ThetaRenewalAnalyticContinuation`, `ThetaRenewalCoshFactorization`, `ThetaRenewalSeamGerm`, `ThetaRenewalWaitingTime`, `ThetaRenewalProbabilityPhase`, `ThetaRenewalPhaseSlope`, `ThetaRenewalPhaseLevel`, `ThetaRenewalExitDensity` (+ HTGeometry `VolterraConvolutionAlgebra`, `VolterraConvolutionCalculus`, `DecreasingSineTransformPositivity`) | done |
| L5 quantile | CDF/quantile/`B,D,T,A` on `L²(0,1)` (partly in corpus) | existing Hedenmalm modules | audit |
| L7 tail calculus | theta-tail class, Laplace asymptotics, tail integrals `I`, shear Fubini, resolvent `T_β = β²I²(1−T_β)`, tail series and symbols, expansions in `e^{-2x}` (product, inverse), Gaussian-base integration by parts | `ThetaTailScalingAsymptotics`, `ThetaTailIntegralCalculus`, `ThetaTailGermExpansion` | done |
| L8 causal kernels | quasi-polynomials `Σ p_μ(s)e^{μs}` (Laplace transform, pole orders, uniqueness, reality, top asymptotics, `limsup log‖E‖/s`), causal kernel `K` of a zero division with `u = ck + ∫K k(·+s)`, `r(−q²) = c + ℒK`, poles ↔ exponents; Gaussian-rate derivative towers of deleted fluxes | HTGeometry `QuasiPolynomialLaplaceCalculus`; `ThetaZeroDivisionCausalKernel`, `ThetaZeroDivisionRateDerivativeWitness` | done |
| L9 ℓ²(ℕ₊) block operators | division-block operators `f ↦ w(m) f(⌊m/b⌋)` (Gram identity, adjoints, isometries, composition, HS, compact truncations, essential norm = limit of block masses), cell isometry, half-line translations `T_a`, `L_a`, synthesis operators; Blaschke steps as `L²` isometries of quasi-polynomials, derivative of the Laplace transform | HTGeometry `PositiveIntegerBlockOperators`; `ThetaEulerLogCellResidueChannels`, `QuasiPolynomialBlaschkeIsometry`, `ThetaEulerLogCellSeedVacuum` | done |
| L10 index-set sources | termwise Laplace laws for `S_A = Σ_{n∈A} a_n`, flux potentials `H_A = ∫_x^∞ e^{t/2}S_A` (boundary values, exhaustions, IBP test limits), dilated Riemann sums, Laplace-class orbit transforms `T_k` (holomorphic, pairing, homogeneity), Laplace uniqueness via half-line pullback, parity sectors of involutive isometries | `ThetaCriticalBoundaryMellinCharge`, `ThetaCriticalBoundaryFluxPotential`, `ThetaIntegerCutoffMovingPacket`, `ThetaContinuousRateOrbitDensity` | done |
| L6 complex analysis | Rouché/Hurwitz (max modulus on `1/G`), Jensen+RvM capacity, sector Phragmén–Lindelöf | HTGeometry `HurwitzMaxModulusZeros`, `JensenIntegratedCountBound`, `SectorPhragmenLindelof`; `ThetaTailDivisorCapacity`, `ThetaTailSectorialGammaBound` | done |

## Cards (status: todo / partial / done)

| Card | Needs | Status |
|-|-|-|
| prime-deletion-spectral-escape | L1 | done → 3-formalized |
| euler-two-port-jet-pole-renormalization | L1 | done → 3-formalized |
| sieve-bidirectional-cusp-variation | L1 | done → 3-formalized |
| prime-square-two-level-normal-jet-rigidity | L1 (algebra in corpus) | done → 3-formalized |
| prime-deletion-graded-terminal-admission | first-atom asymptotic | todo |
| euler-critical-boundary-mass-escape | L1, flux potential | DONE → 3-formalized (`ThetaCriticalBoundaryMellinCharge`, `ThetaCriticalBoundaryFluxPotential`, `ThetaIntegerCutoffMovingPacket`, `ThetaContinuousRateOrbitDensity`) |
| one-sided-bernstein-two-anchor-offline-zero | L1, L2 | done → 3-formalized |
| prime-power-bernstein-gauge-rigidity | L2, gauge layer `ThetaTranslationGaugeFlux` | done → 3-formalized |
| divisor-bernstein-gauge-rigidity | L2b, Möbius/totient | done → 3-formalized |
| prime-deletion-bernstein-pure-ray | L2 | done → 3-formalized |
| all-sieve-seed-projector-translation-cone | L1, L2, measure gauges `ThetaTranslationMeasureGauge` | done → 3-formalized |
| all-sieve-mobius-rate-reconstruction | L2 | DONE → 3-formalized (HTGeometry `RateMobiusInversion`; `ThetaRateLaplaceBernstein`, `ThetaRateMobiusSourceTransfer`, `ThetaRateMobiusBoundaryExamples`) |
| sieve-zero-division-rate-tomography | L2, L3, Landau | DONE → 3-formalized (HTGeometry `QuasiPolynomialLaplaceCalculus`; `ThetaZeroDivisionCausalKernel`, `ThetaZeroDivisionRateTomography`, `ThetaZeroDivisionRateDerivativeWitness`) |
| positive-real-zero-division | L3 | done → 3-formalized (`ThetaZeroDivisionSource`) |
| euler-zero-division-seed-transfer | L3 | DONE → 3-formalized (`ThetaSeedHalfLineDivision`, `ThetaSeedTransferQuartet`, `ThetaTailScalingAsymptotics`, `ThetaGaussianBaseCommutator`, `ThetaTwoEndedTailLaw`, `ThetaTailIntegralCalculus`, `ThetaTailGermExpansion`) |
| endpoint-harmonic-completeness | L3, tail-capacity | DONE → 3-formalized (`ThetaZeroDivisionRealization`, `ThetaEndpointDivisorClassification`, `ThetaEndpointHarmonicCompleteness`, `ThetaEndpointDefectIndex`, `ThetaEndpointMomentFiltration`, `ThetaEndpointPositiveDeformation`, `ThetaEndpointLpDefect`, `GaussianControlEndpointIncompleteness`; HTGeometry `FiniteMeasureL1Duality`, `PolynomialImagRaysLiouville`) |
| tail-divisor-capacity-threshold | L6 | DONE → 3-formalized (`ThetaRelativeSourceRigidity`, `ThetaTailDivisorCapacity`, `ThetaTailSimpleCriticalThreshold`, `ThetaTailCapacitySharpness`, `ThetaTailSectorialGammaBound`; HTGeometry `GammaHorizontalRatio`, `SectorPhragmenLindelof`, `JensenIntegratedCountBound`, `GaussianPairControlQuotient`) |
| derivative-dark-divisor-packets | L6 | DONE → 3-formalized (`ThetaDerivativePacketDivisor`, `ThetaSourceTailRatioCalculus`, `ThetaDerivativePacketLogConcavity`, `ThetaDerivativePacketSpectralBoundary`, `ThetaSourceTailDerivativeModeration`, `ThetaCompactTailInterpolation`, `ThetaCompactTailSchwartzConvergence`, `ThetaCompactTailImplant`; HTGeometry `HurwitzMaxModulusZeros`) |
| compact-critical-strip-zero-engineering | bumps, Riemann–Lebesgue | done → 3-formalized (`ThetaCompactStripZeroEngineering`, `ThetaAnalyticStripZeroEngineering`, `ThetaSourceSurgeryToolkit`; HTGeometry `OscillatoryPacketFourier`, `EvenAnchorProjection`) |
| global-riccati-order-one-offline-countermodel | Riccati Gaussian family `ThetaRiccatiGaussianCountermodel` | done → 3-formalized |
| riccati-three-charge-offline-countermodel | L6 | done → 3-formalized (`ThetaRiccatiThreeChargeCountermodel`) |
| euler-logcell-residue-highpass | ℓ² operators, Hardy separation | DONE → 3-formalized (HTGeometry `PositiveIntegerBlockOperators`; `ThetaEulerLogCellResidueChannels`, `QuasiPolynomialBlaschkeIsometry`, `ThetaEulerLogCellSeedVacuum`) |
| cdf-crossfrequency-rvm-capacity | L5, compact operators | DONE 2026-10-05 → 3-formalized |
| cdf-no-finite-range-symmetrizer | L5 | DONE → 3-formalized (`ThetaCdfFixedShiftAction`, `ThetaCdfFiniteRangeSymmetrizerNoGo`) |
| quantile-critical-one-port-rigging | L5 | DONE 2026-10-05 → 3-formalized (`ThetaQuantileOnePortPencil`, `ThetaQuantileFlatNormalForm`, `ThetaQuantileHalfPowerThreshold`, `ThetaQuantileChargedPort`, `ThetaQuantileTwoEndedSelector`) |
| quantile-resistance-network | L5, Fourier series | todo |
| compact-inverse-zero-jordan-history | L5 | DONE → 3-formalized (46 modules; last: `TwoGaussianDerivativeCenteredHistory`) |
| deletion-cutoff-commutator-collapse | L1, PNT | DONE → 3-formalized (`ThetaCutoffCommutatorShell`, `ThetaCutoffCommutatorCofinalLimit`, `ThetaCutoffCommutatorMellin`, `ThetaCofinalCurrentSignChanges`, `ThetaPrimeScheduleSpectralObservation`, `ThetaNaturalScheduleEulerOscillation`) |
| chronological-boundary-positive-transfer | L1, Laplace | DONE → 3-formalized (`ThetaChronologicalCutoffCurrent`, `ThetaChronologicalPositiveTransfer`, `ThetaChronologicalCausalJumps`, `ThetaChronologicalSingularDeconvolution`, `ThetaChronologicalPacketResolution`) |
| prime-deletion-moving-cusp-dual-source | L1, Landau | DONE → 3-formalized (`ThetaMovingCuspDualSource`, `ThetaMovingCuspTotientReconstruction`, `ThetaMovingCuspSpectralShear`, `ThetaMovingCuspWeightedEscape`) |
| rational-cusp-boundary-law | Poisson/Gauss sums | done → 3-formalized (`ThetaRationalCuspBoundary`, `ThetaCuspOneSidedConnection`, `ThetaCuspAbelBoundaryPairing`, `QuadraticGaussSumFourthPower`) |
| prime-modular-commutator-crossing | Jacobi, Hardy sign, PNT | done → 3-formalized (`ThetaDeletionInversionCommutator`, `ThetaQuadratureDefectSpectralKernel`, `ThetaCommutatorKernelInertia`) |
| renewal-phase-cosh-factorization | L4 | done → 3-formalized |
| renewal-complex-resonance-stieltjes-obstruction | L4, Hadamard | done → 3-formalized (`ThetaRenewalDenominatorOrder`, `ThetaRenewalResonanceDivisor`, `ThetaRenewalPhaseKernelNotMonotone`, `ThetaRenewalFeedbackLoop`, `ThetaRenewalResonancePhase`, `ThetaRenewalNuclearBoundary`; HTGeometry `LogDerivativeResidue`, `DiagonallyDominantPosDef`) |
| renewal-reflection-preserving-zero-surgery | L4, Riemann–Lebesgue | done → 3-formalized (`ThetaReflectionPreservingZeroSurgery`, `ThetaSurgeryControllability`, `ThetaProfileSurgeryVariation`, `ThetaSurgeryEnvelope`, `ProfileRenewalLogKernel`, `ProfileRenewalAnalyticContinuation`) |
| renewal-seam-critical-coupling | L4, Rouché | done → 3-formalized (`ThetaSeamCouplingFamily`, `ThetaSeamCouplingZeros`, `ThetaSeamCouplingContacts`, `XiStripInverseDecay`, `EntireConstantShiftZeroCount`; HTGeometry `RealNonnegativeZeroEvenOrder`) |
| half-line-port-alternating-orientation | two-thirds theorem | done → 3-formalized (`ThetaHalfLinePortOrientation`, `ThetaHalfLinePortCrossings`, `ThetaHalfLinePortGauge`) |
| half-port-stieltjes-spectral-bridge | L4, one-port Stieltjes layer | done → 3-formalized (`ThetaHalfPortStieltjesSpectral`; HTGeometry `OnePortStieltjesTransform`, `OnePortSpectralModel`, `MaximalMultiplicationSelfAdjoint`, `StieltjesPrincipalValueBoundary`, `LorentzianCosineIntegral`) |
| levy-spherical-dispersion-duality | L4, radial integration | done → 3-formalized (`ThetaReflectedJumpExponents`, `ThetaJumpRenewalMeeting`, `ThetaJumpCompoundPoisson`, `ThetaSphericalRadialLift`) |
| causal-germ-translation-ideal-phase-selection | zero-radius theorem | done → 3-formalized (`HalfLineTransformCalculus`, `ThetaCausalGermPort`, `ThetaPrimeMomentPorts`, `ThetaTranslationIdealSources`, `XiWallLogDerivativeCones`, `ThetaPrimePacketPorts`, `ThetaPacketHarmonicObstructions`, `FiniteRankPhaseMoments`) |
| causal-mobius-theta-boundary-criterion | Möbius–theta tail ⇔ RH criterion | DONE → 3-formalized (`CausalMobiusThetaStability`, `CausalMobiusThetaRamareForm`, `CausalMobiusThetaPhysicalSource`, `CausalMobiusThetaPhysicalWavelet`, `CausalMobiusThetaHistoryLocalization`, `PoissonArithmeticProgressionBound`, `EulerDeletionPeriodicProjection`, `CausalMobiusThetaSmoothGaugeProfile`, `CausalMobiusThetaSmoothGauge`, `CausalMobiusThetaTransitionClock`, `CausalMobiusThetaAbelBoundary`) |
| causal-mobius-theta-primorial-transition | primorial innovation bounds | DONE → 3-formalized (`CausalMobiusThetaPrimorialInnovation`, `CausalMobiusThetaUniformCycle`, `CausalMobiusThetaLargestPrime`) |

## Remaining three cards: build order

| Step | Content | Planned module | Status |
|-|-|-|-|
| Q1 | Fourier Hilbert basis `e_n(t)=e^{2πint}` of `L²(unitIntervalMeasure)` | `ThetaQuantileFourierModes` | done |
| Q2 | `Be=0`, `B e_n = q(e_n−1)/(2πn)`, matrix `⟨e_m,Be_n⟩=(Φ_m−Φ_{n−m})/(2πn)`, `D=PBP`, `H_n` blocks, `D₀`, `R`; nonzero spectra and algebraic multiplicities of `B`, `D` agree | `ThetaQuantileFourierQuotient`, `ThetaQuotientOppositeFrequencyBlocks` | done |
| Q3 | `h=1/q` concave, `Φ_{2n}<2Φ_n`; `q` convex, `Φ_{2n}−Φ_n=∫q''W_n>0`; `r_n∈(0,1)` | `ThetaQuantileProfileCalculus`, `ThetaCdfActionDyadic` | done |
| Q4 | sharp clock `Φ_n = log log n − log π + O(log log n/log n)`; `r_n→0`; `cI ≤ G₀ ≤ 2I` | `ThetaCdfActionClock`, `ThetaQuotientPairedBlockMetric` | done |
| Q5 | Ky Fan principle via greedy SVD, `K_N` subadditive, Weyl `Σ m_i|μ_i| ≤ K_N` (Schur flag on generalized eigenspaces) | HTGeometry `KyFanWeylSingularValues` | done |
| Q6 | `Σ_{|γ|≤T} 1/|z| = (1/2π+o(1))(log T)²` (Abel summation on `N(T)`), eigenvalue partial sums of `D` | `XiReciprocalOrdinateLogSquare`, `ThetaQuotientEigenvalueSums` | done |
| Q7 | items 1–3 and 5 of the RvM card | `ThetaQuotientOppositeFrequencyBlocks`, `ThetaQuotientCrossFrequencyCapacity`, `ThetaCdfFrequencyAdmission` | done |
| Q8 | item 4: `K_Φ` clock comparison (`MertensClockDefectTraceClass` generalized to every `HalfLineClock`, `e^{−y/2}` displacement) | `ThetaActionPrimeGramOperator` | done |
| Q9 | one-port rigging card; Q10 resistance-network card | later | todo |

## One-port rigging card: build order (2026-10-05)

`H₀ = meanZeroSpace`, `P = meanZeroProj`, `h = 1/q` (`metricSymbol thetaSource`), `M_h = thetaMetricOperator`, `B = thetaKernelOperator`, `V = pinnedVolterraCLM` (`V + V* = |1⟩⟨1| − |1⟩⟨t| − |t⟩⟨1|`, so `PVP` is skew on `H₀`), `β(f) = ⟨1, Bf⟩`, `b = P h`; corpus eigenvector `thetaDivisorEigenvector z` (`B v = −z⁻¹ v`, `v = U(sourceModeF)`, `∫ sourceModeF = M`), `xiC_thetaSource` (`xiC = XiC` on `|Im z| < 1`), `sourceModeI/U/F`, `quantileUnitary`, `integral_comp_quantile`.

| Step | Content | Planned module | Status |
|-|-|-|-|
| R1 | `M_h B = iV` on `H₀`; pencil `TD = A − bβ`; `A` self-adjoint, `T` positive injective on `H₀`; `ker β` eigenvalues real | `ThetaQuantileOnePortPencil` | done |
| R2 | flat normal form (2a), port moment (2b), weak form (2c); image dense in `L²(ℝ)`; `ρ ∈ L²`, `x ∉ L²`; exact output norm `‖ρ‖₂`; `f_L` sequence, `β` unbounded in `T`-energy | `ThetaQuantileFlatNormalForm` | done |
| R3 | Douglas range criterion; `T^α` (CFC rpow on `H₀`) acts as `h^α` on the odd sector; `Q ∈ range T^α ⟺ α < 1/2`; `b ∈ range T^{1/2}`, `b ∉ range T` | `ThetaQuantileHalfPowerThreshold` | done |
| R4 | `f_z = v_z/√M − 1 ∈ H₀`, `Df_z = −z⁻¹f_z`, `β(f_z) = −z⁻¹` for every Xi zero; charge sum (6) | `ThetaQuantileChargedPort` | done |
| R5 | `G_z`, `u_z` for `0 < Im z < 1`: `u_z ∈ L²`, `∫u_z = 0`, `−i∫xu_z = −1/z`, (7), (9), (8) `∫|u_z|²/ρ < ∞ ⟺ XiC z = 0`; `u_z∘Q/h = f_z` at zeros | `ThetaQuantileTwoEndedSelector` | done |
