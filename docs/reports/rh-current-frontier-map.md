# RH proof-route ledger

**State:** RH open. 27 live routes; 17 candidates. No route has a source-derived RH-closing sign or bound.

**Lean checkpoint:** fba965f88699dddc135c2cd74351c529b6390223. [L] = tracked, root-imported Lean declaration (not recompiled for this ledger); [S] = source-only or umbrella-unwired declaration, not counted as proved; [P] = paper claim. R:X = formal/GaloisForLFunctions/RHTower/X.lean; H:X = formal/GaloisForLFunctions/HTGeometry/X.lean. E = source modules, not extra premises. Paths are proposed; [L] denotes root-imported proof evidence, not a fresh build.

**Classification:** Live = fixed source-defined observable with RH-sufficient receiver and explicit arithmetic estimate still open; an iff is not required. Candidate = missing source-to-receiver landing, only zero-indexed/abstract realization, or finite/nonselective diagnostic. Killed = scoped mechanism refuted/circular/nonselective; see [killed routes](rh-killed-routes.md). One route may have alternate receivers for one source architecture.

## Find a route

| Family | Live | Candidates | [Dead mechanisms](rh-killed-routes.md) |
|---|---|---|---|
| Prime explicit formula / signed energy | WL, RW, FU, RP, PA, LI, JAS, CTF, EWU, OWU, PBM, RB | APF, EGC, EWJ, FEL | KR-GEN, KR-CRT, KR-CCP, KR-BD, KR-FPR, KR-REF, KR-CPF, KR-TMD, KR-TK, KR-SRP; EGC inner contour |
| Möbius cancellation | MC | MSC | KR-DEF |
| Theta sign / heat / moments | TT, LA, TH, HCF | HJ | KR-TEQ, KR-CAL, KR-ISG, KR-JPR, KR-HFR; TT averaging |
| Causal hyperbolic–modular duality | CHMD | — | CHMD scoped compactness/order/cone/pole |
| Geometry / index / arithmetic rigidity | TG, HF, GTA | DR, IRK | KR-DSA, KR-INT, KR-TWN, KR-APW, KR-RAW, KR-R1; HF zero-algebra, IRK completion |
| Newton dynamics | XN | — | — |
| Renewal / singular comparison | RN | — | KR-TRC, KR-R2; native extension |
| Ward / collision | WD | — | KR-UCF, KR-R3, KR-HUS |
| Suzuki / boundary limits | SZ | SEC | KR-NEV, KR-BD |
| Physical realization | PM (FZZ-P) | PTR, W1C, PM (PW-B) | KR-AUT, KR-SEL, KR-PTR, KR-GAP, KR-COS, KR-POI, KR-ISG; nuclear Ruelle ζ, HB, W1C pencil |
| Singular source completion | — | BSH, CDC, PCS, RFHM, SC, WBF | R, AF, F |
| Deterministic zeta recurrence | BAG | — | KR-BAG, KR-TOR, KR-LLM |

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Exact prime data → one-sided bound on Φ(log n), prime lags, or integrated Chebyshev deficit → RH.
- **Established [L]:** Either one-sided bounded lag criterion is RH-equivalent; power-gap, prime-mesh, progression, and thin-exception sampling transfer source bounds. By Landau's theorem, a one-sided square-root bound `±∫₀ᵀ(eᵗ−ψ(eᵗ))dt ≤ B e^(T/2)` on the logarithmic Chebyshev-deficit primitive already forces RH. Explicit prime-lag/zero-free-strip exponent laws, curvature and Cayley reconstructions retain affine charge. Sampling and operator encodings do not produce a bound.
- **Open:** Source-derived exponent-zero one-sided prime-lag or integrated Chebyshev-deficit bound (or equivalent dips/exponentially thin failures); alternate no-off-line-chain plus bounded progression/density-zero exception.
- **E:** R:PrimeLagLowerBoundRH; R:ChebyshevDeficitPrimitiveOneSidedRH; R:WeilLagDenseSampling; R:WeilLagPowerGapExceptionalSampling; R:WeilLagPrimeWindowMeanReceiver; R:PaperLagCayleyDeterminantReconstruction.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → nonnegative constrained ground energy at every aperture → RH.
- **Established [L]:** RH iff all-aperture negative index vanishes. Compact self-adjoint threshold pencil computes exact finite index and minimal positive repair. Odd/primitive positivity, full mixed Φ explicit formula, and exact Doob identity retain every prime cross-term; small apertures are positive. Literal Fejér box energy gives another one-sided receiver. Any finite family of distinct nonreal Xi orbits yields an equally dimensional compact polar-zero negative subspace with an L²-relative gap at sufficiently large support; threshold existential. Compact-polar Xi evaluation is injective and dense in its folded divisor Hilbert target; induced Weil pairing has zero radical. Exact Weil form splits into Markov creation/jump energy plus `½⟨cosh,g⟩²−½⟨sinh,g⟩²`; for real compact `C²` tests the archimedean functional is exactly `Ω(0)h(0)+∫₀∞[(h(0)−h(x))e^(x/2)/sinh x+4h(x)cosh(x/2)]dx`, with nonnegative jump integrand and factorized cosh moment. RH iff the sinh-capacity bound holds for every compact test/level. Absolute-value contraction lowers Markov energy but raises the pole part; finite-dimensional capacity is a `Q⁻¹` bound only when `Q` is positive definite. A zero-annihilating, prime-blind twisted-arc null family has dilation energy `a(1)=0`, `a′(1)=−2S` for its explicit prime slope `S`; if `S≠0`, the dilated blind cone has negative energy on one side of `1`.
- **Open:** Source-derived sinh-capacity bound at every level, equivalently all-aperture lower bound for the actual signed Gamma/prime-edge/polar form; no established positivity of the full `Q` or uniform capacity ceiling.
- **E:** R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane; R:WeilMarkovOneBoundState; R:WeilFejerBoxEnergyRH; R:PaperRestrictedWeilGroundThreshold; R:WeilCompactOrbitInertia; R:XiCompactPolarWeilRealization; R:ArchimedeanAnomalyConstantLaws; R:WeilMarkovPoleCapacity; R:WeilArchimedeanExactForm; R:NullRayDilationCriticality.

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed Möbius/prime scheduling → completed Abel moment A(M)/M bounded above → RH.
- **Established [L]:** One-sided Abel receiver retains polar/lattice terms. Prescribed finite prime blocks admit a helper core with positive Boolean energy differences. A prime-exhaustive history can decrease complete clock energy at each block's cutoff. Compact-cutoff critical Abel clocks are continuous in the full BV prime-jump graph; their closed positive clock cone contains every cutoff-fixed continuous BV target. After a target-dependent cutoff fixed before scale, distinct actual primes approximate every complete graph vector at all sufficiently large common scales with arbitrarily small diagonal cost. Landau continuation of a literal positive tail retains its compact head, and any real-analytic meromorphic Laplace continuation with a nonreal pole excludes an eventually one-signed source tail. Cone membership and realization do not orient the signed energy.
- **Open:** Pay fixed seed and signed drift between successive cutoffs, including earlier action, covariance, and endpoints; obtain uniform completed-Abel bound. MC's fixed-window actual-prime synthesis does not pay this history.
- **E:** R:CCMFUSuzukiMobiusDivisorOneSided; R:MobiusDivisorPreparedPrimeCube; R:MobiusDivisorPaidPrimeExhaustion; R:MobiusRieszSquareSourceQuadrature; R:MobiusDivisorClockGraphCone; R:PrimePositiveClockRealization; R:MobiusDivisorPrimeGraphClockRealization; R:MobiusDivisorCompactClockSource; R:MobiusDivisorCompactClockCone; R:MobiusDivisorCompactClockSeparation; R:MobiusDivisorCompactClockTailSeparation.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Literal matched−quantile prime history → eventual linear defect floor → RH.
- **Established [L]:** Linear-floor equivalence, signed hyperbola/centroid/square-debt identities, low-LCM payment, and exact Abel/RP tail representations. Full signed Cayley tails have noncompact positive and negative parts; compact repairs cannot force their sign.
- **Established [L]:** The literal native first clock jet `λ_{p,e} f_{p,e}` has zero-depth Gram dominated by `¼` of the prime Poisson kernel: bounded synthesis on full `ℓ²` prime-depth source, positive-depth Hilbert–Schmidt columns, strong right derivative for every original coefficient vector, noncompact critical first-jet synthesis, and no operator-norm derivative. Bounded ordinate-clock changes retain a bounded noncompact first jet; their differences are Hilbert–Schmidt; native orbits are strongly but not operator-norm differentiable.
- **Open:** Source-derived complete-history floor with joint centroid/square, high-LCM, moving-core, and singular-domain transport paid.
- **E:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePHyperbolicPairDeletion; R:RoutePLcmPairPayment; R:PaperAbelRoutePOrder; R:BurnolBaseCoefficientCoordinates; R:BurnolBaseFirstJetAdmission; R:BurnolBaseFirstJetNoncompact; R:BurnolBaseNativeGenerator; R:BurnolRelativeOrdinateFirstJet; R:BurnolOrdinateNativeGenerator; H:GramDominatedSynthesis.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Continued exact prime−archimedean trace → high-frequency passivity or subexponential Bernstein mismatch → RH.
- **Established [L]:** Finite-frequency trace and source recovery are exact. Signed current multiplier positivity on all upper half-strip slices is RH-equivalent; frequency cutoffs converge in norm. Arbitrarily thin exponential envelopes for the Bernstein packet mismatch between one nondegenerate coupled-Sonin aperture and the endpoint prime–Gamma source imply RH, with all Hausdorff positivity premises discharged unconditionally. For each fixed Hausdorff order `k`, calibrated moment differences are nonnegative at every sufficiently large shift `r`; RH reduces to the finitely many shifts below an order-dependent threshold for each `k` (no order-uniform threshold established). Absolute-current observations retain magnitude but erase orientation. Sharp prime-weight logarithmic-energy floor and rigidity do not give the sign. For the critical Stokes carrier, passive deletion and signed correction coincide at all degrees and survive unconditionally at the two-jet level via a canonical one-atom countercarrier; at all degrees, each distinct prime/depth node has raw singleton mass `<2x`, while every completed Xi moment witness has mass `≥2x` at its thermal nodes, so any exact completion must increase infinitely many singleton masses and, under the supercarrier constraint, also remove mass. Passive deletion and finite atom repair fail.
- **Open:** Arithmetic sign of the high-frequency current numerator, unit-collar exponential envelope for the coupled-Sonin/endpoint Bernstein mismatch, or source sign at all remaining low shifts across unbounded Hausdorff orders; nonpassive source-faithful completion with both added and removed mass.
- **E:** R:PrimeArchEndpointFrequencyAccretivity; R:PrimeArchBernsteinLoschmidtPurity; R:SoninCoupledBernsteinMismatchRH; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity; R:PaperPrimeArchCurrentOperator; R:PaperPrimeArchSignErasure; R:PrimeWeightLogEnergyFloor; R:GammaSewnMobiusApertureStokesPassiveDeletionSignedCorrection; R:GammaSewnMobiusApertureStokesCriticalPoleCapacity.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Signed Möbius source → half-power cancellation/subpower energy or square-sampled Chebyshev bound → RH.
- **Established [L]:** RH-equivalent Möbius Hilbert, Liouville, Riesz, and square-source receivers; exact signed bilinear and divisor decompositions pay small-modulus, low-product, and terminal regions. Locally on `ℤ/p²ℤ`, the three valuation strata `1_U, 1_V, δ₀` are orthogonal with producer–reporter compression spectrum `{1, −1/p}` and hyperbolic Möbius record parameters `σ_p = sech(½ log p)`, `τ_p = tanh(½ log p)`. At every sufficiently large common scale, distinct actual primes realize any fixed compact Abel-clock target with arbitrarily small normalized diagonal cost and literal terminal singleton fibres.
- **Open:** Global signed bilinear bound: principal counterterm and high-product remainder jointly. Fixed-window realization and local `ℤ/p²ℤ` strata identities do not bound scale-dependent targets, inherited histories, or cutoff drift.
- **E:** R:MobiusHilbertFormEquivalence; R:MobiusSquareResidueShortBilinear; R:PrimeSquareMobiusComplementaryRecord; R:MobiusDivisorPrimeClockRealization; R:MobiusDivisorPrimeClockTerminalControl.

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed signed covariance/Wold decay or odd Weil-form sign → RH.
- **Established [L]:** Exact seam/tail and odd-four identities; sharp Wold boundedness threshold t<1/2 and natural-cutoff RH energy criterion. Odd/primitive Weil positivity has an exact half-line reflected-prime inequality and Φ-Doob form. Translation-averaged entire strip-decaying densities are independent of a zero's transverse depth; this observation cannot orient off-line zeros. A nonzero continuous periodic Kelvin-chirp profile cannot give a positive-definite separator when support ratio `e^L>4+2√2`; unbounded combs remain outside this bound. Finite-prefix, sign-blind, and masked convergence do not control global sign.
- **Open:** Signed nonlocal covariance or full odd/primitive form positivity across all rapidities and test scales.
- **E:** R:XiHeatCassiniWoldNaturalSquareEnergySubhalf; R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane; R:TranslationAveragedDensityDepthBlindness; R:KelvinChirpSeparatorBound.

<a id="la"></a>
### LA — Line anchor

- **Path:** Literal theta source → all-height Laguerre/Hadamard or Jensen sign → real-rooted Ξ → RH.
- **Established [L]:** Exact sign/zero-count receivers (`RH ⇔ Re(ξ'/ξ) ≥ 0` on `Re s > 1/2`), fixed-time heat-slice Taylor positivity equivalence to the de Bruijn–Newman threshold (`newmanConstant ≤ λ`), exact negative index of the slice coefficient operator, and finite-height/slice controls. Near-double off-line pairs and exceptional heights evade presently controlled finite data.
- **Open:** All-height arithmetic sign, including remaining low-order slices and an arithmetic separator for near-double off-line pairs.
- **E:** R:XiLogDerivReCriterion; R:XiSliceFiniteOrderReduction; R:PaperHeatSliceCriterion; R:PaperSliceCoefficientInertia; R:PaperSliceCoefficientRepair.

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Pre-divisor Euler/Gaussian source → positive-residual cubic transgression and integer trace<1 → RH.
- **Established [L]:** Boundary winding/index and source-sensitive transgression identities; finite-scale and ideal/compactness gates do not orient the full reflection-odd prime−Gamma source.
- **Open:** Matrix-complete E_base=E_residual+Tr T_D with E_residual≥0 and all-disc sub-unit trace; alternate source-derived central-gap bound at exponent zero.
- **E:** R:FormationAnchoredCubicSpecialization; R:RestrictedProjectionIndexOperatorNormCriterion; R:GaussianCentralGapExplicitCriterion.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Original arithmetic cohomology → positive Hodge-compatible form, or full-positive arithmetic weight → RH.
- **Established [L]:** Full Weil positivity/PBAP are RH receivers; full-positive weights are rigidly Λ. Original Meyer quotient has global Xi-jet synthesis, faithful Hasse Hilbert admission, nondegenerate Paugam pairing, full-Jordan compact inverse with determinant Ξ, trace-class arithmetic flow/convolution and complete prime−Gamma−polar trace. Fixed Gaussian realizes every original class in the BV graph; native generator intertwines on the whole source image. A fixed bounded top-Hasse insertion recovers the full Paugam pairing from trace-class source convolution; ordinary trace of the alternating product vanishes. Finite Weil nodal mixtures have unique optimal adjacent transport. A positive-definite rational-dilation-invariant form on the Xi zero algebra exists iff RH and all zeros are simple; this zero-built form is not an arithmetic source producer. First causal Xi classes and every polynomial spectral multiple vanish in the original source topology along vertical escape, while native endpoint jets have norm ≥1; no continuous whole-quotient extension retains finite native normalization. For dilated prime-blind nodes, RH iff positivity holds at parameters accumulating at `t=1`; RH implies it at `t=1/k`, and `t=1/2` has an exact theta-scaled archimedean datum. Inside the odd sector (and primitive hyperplane `coshHalfMoment f = 0`), narrow even-bump `oddShift` and odd-bump `evenShift` realize both coordinate signs `±e_j` (`j≥2`), yielding pole-free two-sided Farkas equivalences (`(∃ λ, MarkovPositiveOdd λ) ⇔ OddPrimeBlindPositive`, and analogously on the primitive hyperplane), one-sided M. Riesz minorant/majorant extensions, `cosh`-free uniform window bounds, plastic Lévy–cosh crossover lower bounds with a `+2 sinhHalfMoment(f)²` bonus, a degree-16 first-cell cosine-log Taylor secular counterterm hierarchy proving coercivity and spectral-gap laws up to ratio `S/L ≤ 27`, and a general `M`-stage secular counterterm potential `secantStagePotential M n` (`M ≥ 1`, with zero-loss adaptive telescoping at `M ≥ N`, stage monotonicity in `M`, and all-ratio `S/L` conservation, prime-blind vanishing, and `markovEnergy ≥ 0` laws whenever `2 sinhHalfMoment(f)²` covers the high-frequency secant excess, including exponential `2 sinh(h/4)² coshHalfMoment(g)²` closure on `oddShift g h`). These are receivers/transport and partial-cone bounds, not global sign producers.
- **Constraint [L]:** At a real Ξ zero, strictly positive linear densities annihilate repaired principal classes yet attain either pairing sign on primitive tests whose transform is nonzero there; compact core-nullity alone fixes no pole sign. The normalized blind `(pole, arch)` moment region is convex and has `arch≥Ω(0)`; RH iff it lies above `arch=−pole`. Under RH its null edge is approached from both pole signs with arbitrarily small relative margin, excluding a uniform strict relative-gap proof. Compact mean-zero all-integer-blind cores obey an exact Nyman–Beurling orthogonality identity; existence of a strict positive-definite separator in the closure of pole/Kelvin-chirp functionals would force every such core at that width to vanish. Neither fact supplies the separator.
- **Open:** PBAP: source-derived nonnegative complete Weil form on unrestricted prime-blind tests (or odd/primitive prime-blind tests without high-frequency `sinhHalfMoment` dominance, or dilated parameters tending to `1`), hence positive Hodge compatibility. Geometric arithmetic cup/trace identification remains separate; native realization beyond finite packets requires changed topology, regularization, or normalization. Inserted trace, nodal transport and conditional separation give no positivity.
- **E:** R:WeilPositivityPrimeBlindDuality; R:WeilNodeDilationFamily; R:BlindMomentRegion; R:BlindCoreWanderingNymanBeurling; R:BlindCoreFarkasSeparation; R:MarkovOddSectorFarkasAndOneSidedPBAP; R:MarkovOddShiftWindowAndPlasticCrossoverPBAP; R:MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP; R:MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP; R:MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP; R:DeningerMeyerGlobalXiSynthesis; R:DeningerMeyerGlobalHassePaugamPairing; R:DeningerMeyerFredholmXi; R:DeningerMeyerFlowLefschetz; R:PaperThetaWholeMeyerGenerator; R:PaperThetaUnregularizedExtensionObstruction; R:DeningerMeyerPaugamInsertedTrace; R:FiniteWeilNodalMixtureTransport; R:ZeroAlgebraJetInvariantForms; R:WeilLinearEffectivityObstruction; R:CoreNullTestPoleSign.

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Exact Weil source → causal prime-wave, Chebyshev-discrepancy derivative pairing, or Möbius-rest one-sided bound, or theta-Doob odd-sector half-bound → RH.
- **Established [L]:** Toeplitz/sech positivity, Λ-prime-wave and Λ-free Möbius-rest one-sided bounds, and absence of odd resolvent eigenstates above 1/2 are RH-equivalent. Stieltjes integration by parts expresses the Klein–Gordon prime wave via the classical discrepancy `Δ(s)=Σ_{log n<s} Λ(n)/√n−2e^(s/2)` and the exponentially localized odd derivative kernel `∂_s K_y(s)`; RH holds iff `∫₀∞ ∂_s K_y(s) Δ(s) ds` is bounded above (or bounded below) for `y≥0`. Integrated deficit has a bounded transient head. Exact folded Möbius-wave/tail/remainder and signed `(Λ(n)−1)` lattice-replacement waves give RH-equivalent one-sided bounds. Half-time secant single-square even Weil sign for every rapidity is RH-equivalent; polar anti-nodes remove pole terms but their nonnegativity is only RH-conditional. On one-signed odd tests the prime cross term is a nonnegative opposite-side bonus minus a nonnegative same-side term. For a profile supported through `a` and antitone only on `[c,a]`, prime terms with `log n ≥ max(2a/3,(a+c)/2)` are nonnegative; the low-prime window and Lévy form remain. The arithmetic resolvent has simple eigenvalue `1`; every nonzero primitive eigenvalue is `<1`, not necessarily `≤1/2`. RH iff the odd bound-state space is zero iff the even bound-state space is `span{1}`. If off-line zeros are finite, odd/even/total bound-state dimensions equal `(q, q+1, 2q+1)`, where `q` counts quarter-plane off-line zeros. One-signed odd eigenstates with eigenvalue `>1/2` vanish; sign-changing ones are not excluded. Even-Θ Doob on odd tests has a negative local pole term and an origin-crossing sum-of-values collar. The secondary odd profile `m_a=(Θ(·−a)−Θ(·+a))/(2sinh(a/2))` is positive on `x>0` and has positive sinh pole source. Its normalized shift differences span an infinite-dimensional signed radical of zero energy and resolvent eigenvalue `1/2`. For `f=m_a w`, `w` even, the pole-square pairing is nonnegative, folded edge terms are Dirichlet squares, and the absorbed archimedean kernel is pointwise nonnegative. Harmonic θ ground potential is `<1`; exact full source energy equals stationary energy minus archimedean diagonal and prime-shift quadratic terms. Stationary absolute-value contraction is strict off one-sign states; prime-shift is nonnegative on nonnegative pairs. Total edge energy `‖p.snd‖²` splits into a `2×2` archimedean/prime × envelope/nodal table giving a quantitative nodal lower bound on `(1−μ)/μ` for any nonzero primitive eigenvector; primitive ground subtraction `primGraph` satisfies `sourceEnergy(primGraph q)=weilForm q` on the even sector; eigenvector mass-space Fourier/cosine readouts and translated-cardinal pairing laws force polar moments and Ξ-zero Fourier readouts of threshold eigenvectors (`μ=1/2`) to vanish, and give an exact finite-family eigenvector projection decomposition of `sourcePair` and `sourceEnergy`. Orthonormal eigenvector families satisfy exact Pythagorean decompositions and unconditional edge/graph Bessel inequalities, a shift-uniform odd-polar Bessel bound on `⟨w_i, tanhL⟩²`, an exact cardinal spectral deficit at nonreal Ξ-zeros, a universal Rayleigh-to-energy lower bound and primitive-contraction nodal inequality, and a shift-independent odd cardinal Fourier-Re mode. A universal Riesz–resolvent and stationary-generator dictionary on `SourceGraph` (`(∀ p, sourcePair p q = ⟨p.fst, v⟩) ⇔ q = rieszLift(v + 2q.fst) ⇔ (I − 2·resolvent)q.fst = resolvent v`) identifies `signedRadical` with `ker(resolvent − ½I)` and gives `k×k` spectral readout Gram matrix identities, individual nodal-lobe three-term nonnegative decompositions, Courant nodal-lobe negativity for bound states (`μ ≥ 1/2`), exact odd half-mass lobe laws, universal primitive-contraction resolvent polarization, and bilateral stationary + prime-shift reinforcement in `-4 sourcePair(p⁺, p⁻)` forcing `ν ≤ μ_max` (and strict `ν < μ_max` when the primitive `oneL`-defect is dominated by `4 ⟨primeShiftOperator p⁺.fst, p⁻.fst⟩`). None is a full prime+Gamma sign.
- **Established [L]:** The stationary resolvent is a strict contraction on nonzero vectors; exact second-resolvent and ground-perturbation identities separate stationary energy, prime jump energy, and local diagonal potential. Prime generator satisfies Beurling–Deny nodal contraction; for eigenvectors, the absolute-value edge norm gives `−4 sourcePair(p⁺,p⁻) ≤ ((1−μ)/μ)‖q.fst‖²`, and each lobe obeys an exact five-term jump-versus-diagonal balance. A balanced nonnegative nodal graph is mass- and edge-orthogonal to a primitive eigenvector. Native finite Xi-Jordan packets have signed arithmetic radical exactly at lower Jordan layers after polar subtraction; this identifies a kernel, not a sign.
- **Open:** Source-derived uniform one-sided bound on complete signed Möbius/`(Λ−1)` wave or derivative pairing `∫₀∞ ∂_s K_y(s) Δ(s) ds`, positivity of all half-time squares or all odd Doob energies, or a quantitative jump/ground-potential inequality excluding sign-changing odd eigenstates with `μ>1/2`. Strict stationary contraction and the five-term identities do not bound the local diagonal potential or pay the primitive `oneL`-defect.
- **E:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDPoleDensityLawAndChebyshevDiscrepancyTransport; R:CHMDChebyshevDiscrepancyDerivativeTransportLaw; R:CHMDPrimeKernelDerivativeUniformBound; R:CHMDDoobSourceGraph; R:CHMDSpectralRiemannCriterion; R:CHMDOddSectorCriterion; R:CHMDEvenSectorPointSpectrum; R:CHMDOddBoundStateSignObstructionAndParityQuarterBound; R:CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces; R:CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality; R:CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm; R:CHMDStationaryNodalDecompositionAndPrimeShiftPositivity; R:CHMDEigenvectorCardinalReadoutAndFourTermNodalDecomposition; R:CHMDSpectralBesselAndPrimitiveContractionNodalBounds; R:CHMDUniversalRieszResolventAndCardinalKernelEquations; R:CHMDOddCardinalKernelEquationsAndReadoutGramMatrices; R:CHMDStationaryResolventDictionaryAndNodalPolarization; R:CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds; R:CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure; R:CHMDStationaryStrictContractionAndSecondResolventIdentity; R:CHMDPrimeGeneratorBeurlingDenyAndDiagonalPotentialBalance; R:CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance; R:CHMDBalancedNodalGraphAndGroundPerturbationResolvent; R:CHMDNativeJordanRadical; R:CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection; R:CHMDMobiusFoldedTransportOfKleinGordonPrimeWave; R:CHMDLatticePoleReplacementAndSignedPrimeWave; R:CHMDOddPrimeCrossSignBonusAndWindowPositivity; R:CHMDOddMonotoneProfilePrimeSignLaw; R:CHMDHalfTimeSecantAutocorrelationAndPolarAntiNodeTests; R:CHMDOddHarmonicIdentityAndPolarDoobAbsorption; R:WeilCompactOrbitInertia; R:MobiusDivisorPrimeGraphClockRealization.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity → RH.
- **Established [L]:** Moment and heat-current receivers, finite-rank sign regions, and exact theta-source identities. Fixed-rank or bounded-window positivity does not select the all-rank branch.
- **Open:** All-degree positivity at one positive heat time or equivalent same-time phase/current sign with full discrete-prime remainder.
- **E:** R:XiHeatHankelFormOrthantPositivity; R:ThetaCuspC5OuterClockCurrent; R:XiGaussianHeatTraceCompleteMonotonicity.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Literal theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Established [L]:** Global native Green/whole-BV solver, full-multiplicity Meyer packets, fixed-Gaussian realization and generator intertwining retain the source. Intrinsic one-channel projection has kernel equal to the Xi-multiplicity pencil range; exact confluent moments, all-power defects/solvers, BV repeated-resonance profiles, and complete signed arithmetic value are constructed. Literal causal theta renewal kernel is Hilbert–Schmidt and cone-positive; its positive rank-one feedback yields a compact cone-positive operator with global `det₂(zK)=exp(−dz)D(z)/D(0)` for the actual renewal denominator `D`. Every renewal resonance is an eigenvalue with matching algebraic multiplicity; cone positivity alone does not confine complex resonances. Theta-ratio reduced slope has positive physical value but negative conjugate value, norm and trace on a boundary strip; a strict coarse-cone interior path retains negative norm/trace with positive source error. First causal Xi classes vanish in the original source topology along vertical escape while native endpoint jets stay norm-bounded below; no continuous unregularized extension of finite native synthesis exists. Fixed Cauchy-pole quartet defect vanishes iff RH, with Krylov cyclicity and source-entropy Cauchy tomography proved on the reciprocal-square source; this is a zero-side/Cauchy-moment criterion, not a boundary source-current sign. No global source orientation follows.
- **Open:** Mixed prime+Gamma≥pole inequality with all cusp terms, global seam/cusp gluing, and arithmetic boundary-current orientation; a cone-positive compact Fredholm realization does not yield a real spectrum or the missing sign. Source-faithful native completion requires changed topology, regularization, or normalization, beyond fixed-Gaussian realization.
- **E:** R:PaperThetaNativeResolvent; R:PaperThetaNativeMeyerCompleteness; R:PaperThetaOriginalArithmeticRealization; R:PaperThetaWholeMeyerGenerator; R:PaperThetaUnregularizedExtensionObstruction; R:PaperThetaConfluentNativeSolvability; R:PaperThetaConfluentNativeRegularity; R:PaperThetaConfluentNativeArithmetic; R:PaperThetaCutTransform; R:ThetaRenewalCausalKernel; R:ThetaRenewalCausalResponse; R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum; R:ThetaCuspRatioBoundaryNormOrientation; R:ThetaCuspRatioSourceSlopeReal; R:ThetaCuspRatioBoundaryNormInterior; R:XiReciprocalSquareFixedCauchySource; R:UniversalCauchyQuartetVarianceLaw; R:XiSourceEntropyCauchyTomography.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Directed source current → global negative-cross control or collision charge<2 → RH.
- **Established [L]:** Exact Ward/collision receivers, source formation, global cap integrability, and strict-right multiplicity readout. The actual nonnegative cap vanishes iff RH; forming it is not a sign/cancellation proof.
- **Open:** Source-derived vanishing of global cap or full signed prime−Gamma contraction; uniform owner/absorber bounds for every zero block.
- **E:** R:XiWardCapGlobalIntegrability; R:XiWardGlobalCapRightZeroSum; R:XiWardCubicParabolicDirectionalMultiplicity.

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Literal prime−Gamma history → signed lower floor → Li positivity → RH.
- **Established [L]:** Exact paired Li/source histories and finite primitive receivers; closed-ideal operators classify RH-equivalent compactness but do not supply arithmetic lower bounds.
- **Open:** Eventual Re H_N≥K_N−C on 0<t≤c log(2N+1), or equivalent finite lower bound for the literal primitive; retain first-crossing/outside correlations.
- **E:** R:LiEvenCrossActualClockGrowthLaw; R:LiSignAlongSquares; R:PaperLiNegativeOperator.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed boundary pairing → screw nonnegativity or shifted-Ξ confinement → RH.
- **Established [L]:** Screw/shifted-Ξ receivers, supported phase recovery, boundary/quantile identities, and positive Green inverse. Literal arithmetic Hankel operator exists as a compact self-adjoint integral operator for every positive shift and aperture; at shifts `ω>1/2` it equals the former compressed operator. The continuous cancelled row equations of the actual two-leg Suzuki Gamma source characterize the exact graph closure of finite source packets (no extra maximal extension), and Cesàro averages of radial source regularizations converge in every actual Gamma graph norm. Symmetric Cayley moment partial sums reconstruct the literal Suzuki arithmetic carrier density almost everywhere. Admission and graph/a.e. reconstruction use integrable cusp mass, not a sign; finite heads do not give complete moving-source sign.
- **Open:** Source Wronskian law paying moving infinite head and shell leakage; uniform cusp-preserving passage to unshifted Ξ. Compact/self-adjoint admission at `ω>0` and Gamma graph closure do not yield positivity or a controlled `ω→0` limit.
- **E:** R:SuzukiScrewPointwiseNonnegativityCriterion; R:SuzukiCanonicalShiftedXi; R:SuzukiCanonicalPositiveShiftHankel; H:IntegrableMultiplicativeHankel; R:CCMUnitRieszSuzukiGreenPositiveInverse; R:SuzukiCausalDepthGammaMaximalSource; R:SuzukiCausalDepthGammaCesaroSource; R:PaperSuzukiCayleyReconstruction.

<a id="pm"></a>
### PM — Physical-model routes (Live: FZZ-P Haar approximation; Candidate sub-branch: PW-B cusp forcing)

- **Path:** FZZ alternating Nyman–Beurling source → dyadic Haar approximation → RH; or PW-B physical cusp source → admitted Ward/energy identity → growth receiver → RH.
- **Established [L]:** **(FZZ-P, Live):** For `φ_a(t)={1/(at)}−2{1/(2at)}` on `(0,1]`, approximation of the dyadic Haar target `h=−1_{(0,1/2]}+1_{(1/2,1]}` in `L²(0,1]` is exactly RH-equivalent, with measurable `L²`-witness self-similarity discharged via unconditional dilation averaging; exact Fourier `L log L` reconstruction retains all cross-terms. A witness whose Mellin transform analytically continues to the known zero-free-region mirror is dyadically self-similar; the continuation is a premise, not established for every witness. **(PW-B / Hawking–BM, Candidate — zero-indexed by `q : XiZeroCopy` and missing receiver landing):** Weak retarded realization, compact-cutoff two-response contact identity, complementary-rate wedge-exhaustion limit, and absolutely admitted native-corrected action for each zero copy `q`. Original reflected principal kernel is uniformly bounded for physical exponents; all three principal response channels have polynomial growth. Full original cusp forcing and unchanged forced response have absolutely admitted Laplace integrals and weighted time-`L²` admission for every positive damping `c>0`, matching the literal causal frequency response. Eisenstein value at `i` factors as `2Γℝ(2s)ζ(s)L(s,χ₋₄)` with Hecke Hermitian resonance identity proved at every strip zero of `Λ`; because zeros can come from either L-factor, this value alone does not isolate ζ.
- **Open:** **(FZZ-P):** Unconditional `L²` approximation of the dyadic Haar target by `span{φ_a}`. **(PW-B):** Pre-divisor source formulation (eliminating `XiZeroCopy` indexing) and small-damping `c→0⁺` complete-energy ceiling; PW-B source-contact action must still imply optical magnitude, ordered cap, and all-divisor extinction.
- **E:** R:FermiNymanBeurlingHaarTarget; R:FermiNymanHaarApproximationEquivalence; R:FermiNymanWitnessContinuationRigidity; R:PaperFermiFourierCriterion; R:EisensteinHeckeFactorizationAtI; R:EisensteinHeckeResonanceAllZeros; R:ThetaCuspHawkingBMPWRetardedWeakNative; R:ThetaCuspHawkingBMPWTwoResponseAction; R:ThetaCuspHawkingBMPWTwoResponseActionLimit; R:ThetaCuspHawkingBMPWNativeTwoResponseAction; R:ThetaCuspHawkingBMPrincipalReflectionAdmission; R:ThetaCuspHawkingBMPrincipalSmallDamping; R:ThetaCuspHawkingBMForcedSmallDamping.

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Arithmetic prime-product Weil form → level-one positivity on sufficiently large-prime tests → RH.
- **Established [L]:** Level-one full-product/dyadic constant-vector positivity, cosine-kernel positivity on large primes, harmonic Euler Weil positivity on large primes, PSD at infinity at every level `σ>1`, and torus-density nonnegativity are all RH-equivalent without quasi-RH or no-chain side conditions. Full signed L² torus density and finite-coordinate conditional expectations exist; typical phases and small prime budgets are positive unconditionally.
- **Open:** Source sign for exceptional constant vectors on sufficiently many shells, or all-amplitude damped shell positivity.
- **E:** R:JointAncestryLevelOneCapstones; R:JointAncestryLevelOneDensityCriterion; R:JointAncestryDampedShellCriterion.

<a id="ctf"></a>
### CTF — Chronological tail and Báez–Duarte approximation

- **Path:** Bounded chronological Bose/Möbius rows (or finite Báez–Duarte dilates) → vanishing L² error → RH.
- **Established [L]:** Exact two-sided Báez–Duarte equivalence (`d_N → 0 ⇔ RH`), bounded-row chronological equivalence (`‖r_a‖_{L²(0,∞)} → 0` with `|a_k|≤1` ⇔ RH), and dual sampling equivalence; unbounded rows are dense. Sharp coefficient-budget dichotomy: if RH fails, every coefficient budget `exp(ε^(−θ))` with `θ≤2` fails at some accuracy. Bounded vanishing-error rows force Möbius coefficients; off-line zeros force sharp-row escape.
- **Open:** Construct bounded rows with vanishing chronological error (or prove `d_N → 0` for the discrete Báez–Duarte distance), or prove the dual sampling bound from arithmetic data.
- **E:** R:ChronologicalRiemannEquivalence; R:BaezDuarteCriterionHardDirection; R:BaezDuarteDistance; R:ChronologicalDualSamplingCriterion; R:ChronologicalMobiusEscape.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → one-sided vertical growth or rank-uniform Hankel positivity → RH.
- **Established [L]:** Seven-way heat-trace capstone at any fixed heat time `a>0` (vertical boundedness, vanishing vertical Cesàro mean, right half-plane zero-freeness, vertical heat Gram PSD, heat Hankel PSD, arch−prime Hankel PSD on the pole hyperplane `P(−1/4)=0`, and positivity of all Hankel determinants `det(M_{i+j}(a))`); fixed-rank positivity is unconditional and vertical growth is bounded at Vinogradov–Korobov strength. Singular Hankel blocks have exact negative-index law (counting off-line zero quadruples), Toda contact orders, escaping root branches, regular-head transfer, and signed kernel projections at every positive heat time, without genericity assumptions. On the critical-feature side, compact-source boundary alias and phase variance obey an unconditional phase-uniform budget controlled by the Ξ phase-histogram entropy deficit.
- **Open:** Source-derived one-sided prime-chirp/vertical bound, cofinal Ξ histogram entropy-deficit bound, or rank-uniform Hankel positivity selecting the no-transition branch.
- **E:** R:XiGaussianHeatRouteCapstone; R:XiGaussianHeatBlockInertia; R:XiGaussianHeatTodaMultiplicity; R:XiGaussianHeatRegularKernelProjections; R:PaperCriticalFeatureEntropyVariance; R:PaperCriticalFeatureXiHistogram.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first-jet source → line-centered Newton self-map discs covering every zero → RH.
- **Established [L]:** Disc coverage/self-map and nonnegative interior margin are RH-equivalent. Actual-Xi margin satisfies ΔQ=4(r²−|z−c|²)|ξ″(z)|²≥0 inside each disc; boundary positivity alone does not force interior positivity. Entire scalar damping `A(Ξ)` makes the Newton map globally holomorphic iff `A=0`; each fixed disc has a polynomial pole repair preserving reflection and first root jets, but not self-mapping.
- **Open:** Arithmetic construction of line-centered discs covering every zero with Q≥0 throughout; pay interior curvature Green potential.
- **E:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscSourceMargin; R:XiNewtonDiscCurvature; R:XiNewtonScalarDamping.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Reflected approximate functional equation → unbounded physical self-returns on each right-strip disc → RH.
- **Established [L]:** Disc recurrence of the actual ζ function implies RH; the corpus proves this sufficient direction, not the converse. Weak-recurrence ladder, physical cubic reduction and Fourier reconstruction do not give cofinal returns. Random phase-cell returns and finite-window positive mass are insufficient.
- **Open:** Complete signed axes/tail payment yielding common-height physical recurrence on every right-strip disc.
- **E:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse; R:PaperZetaReturnSpectralCriterion.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Actual even blind minimum nonnegative at every aperture → even positivity → λ=Λ → RH.
- **Established [L]:** Even positivity at any finite pole weight forces λ=Λ and RH; even-polar and full-positive weight cones coincide. Single-source purification, exact fibres and blind minimizer attainment hold at every aperture. Blind minimum is antitone in aperture, at least `1/20` for `a≤(log 2+1/50)/2`, and nonnegative at every aperture iff RH. No real prime-weight sequence repairs the even cone at pole weight `β<1` without the polar constraint. Constant archimedean shifts preserve blind minimizers and subtracted ground residuals while changing the minimum's sign.
- **Open:** Source-derived nonnegative even blind minimum at every larger aperture; attainment and ground geometry do not supply its absolute sign.
- **E:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorFullPositivity; R:EvenSectorExactMomentRealization; R:EvenSectorBlindVariationalAttainment; R:EvenSectorBlindMinimumSmallAperturePositivity; R:EvenSectorMultiPrimePeriodizationNoGo; R:EvenSectorBlindGroundShiftInvariance.

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH.
- **Established [L]:** Uniform decay across all late actual theta-stage Schur packets is RH-equivalent; finite truncations converge strongly even off RH. Symmetrizing/positive-kernel substitutes do not force decay.
- **Open:** Source-derived uniform transverse-energy decay, independent of the zero divisor.
- **E:** R:HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurSolidObservation; R:PaperThetaSchurModeCharge; R:PaperThetaSchurCompactGap.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual Λ odd Weil positivity, or odd-positive arithmetic weight plus all-scale dilation-ray sign → RH.
- **Established [L]:** RH iff the actual von Mangoldt weight is odd Weil-positive (or Weil-positive modulo constants); an arbitrary odd-positive minorant `λ≤Λ` or odd-positive weight with full dilation-ray positivity must equal Λ and implies RH. Odd positivity yields a Nevanlinna measure/slit continuation; even mean-zero sign removes real-cut mass. Odd blind fibres, exact dual attainment, and the bounded self-adjoint arithmetic-corrected ground operator exist at every aperture: every odd blind minimizer is an actual eigenvector in the represented operator domain with polynomial-times-ground transform and exact finite spectral interpolation. Constant archimedean shifts preserve subtracted ground geometry while changing the blind minimum's sign.
- **Open:** Source proof of odd positivity for actual Λ, or construction of an odd-positive arithmetic weight with all-scale ray sign. Odd blind minimizer and ground-operator geometry alone give neither sign.
- **E:** R:WeilOddConeMinorantRigidity; R:OddWeilSpectralMeasure; R:WeilDilationRayCriterion; R:OddSectorBlindVariationalAttainment; R:OddSectorExactDualAttainment; R:OddSectorArithmeticGroundOperator; R:OddSectorGroundPolynomialStructure; R:OddSectorGroundZeroInterpolation; R:OddSectorExactSpectralInterpolation; R:EvenSectorBlindGroundShiftInvariance.

<a id="pbm"></a>
### PBM — Prime boundary monodromy / regularized log-ζ abscissa

- **Path:** Fixed pole-regularized prime or log-ζ coefficients → Dirichlet series convergence at every real `σ>1/2` → RH.
- **Established [L]:** RH iff the pole-regularized prime series `Σ_{n≥2}(1_ℙ(n)−1/log n)n^(−σ)` or log-ζ series `Σ_{n≥2}((Λ(n)−1)/log n)n^(−σ)` converges at every real `σ>1/2` (proved via Abel summation from the `Λ(n)−1` partial-sum exponent law; despite the legacy route name, no monodromy is involved here — punctured monodromy lives in `DR`). Raw prime Dirichlet sum diverges for `Re s<1`; regularized prime and log-ζ diagonal shift operators retain a nonzero compact-quotient (Calkin) gap `1/2`. The gap-weighted prime Dirichlet series `Σ_k (p_{k+1}−p_k)p_k^(−s)` continues meromorphically to `Re s > θ` as `1/(s−1)+G(s)` for any admissible prime-gap second-moment exponent `θ` (unconditionally `θ=71/100` by Hoheisel). Regularization is not cancellation.
- **Open:** Source-derived critical-abscissa (`σ>1/2`) cancellation of the fixed regularized prime or log-ζ coefficients (or admissible prime-gap second-moment exponent `θ≤1/2` plus zero-freeness); compact-ideal comparison supplies no bound.
- **E:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal; R:PrimeGapDirichletContinuation.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Extremal divisor sums/primorial Mertens product → eventual Robin/Nicolas inequality → RH.
- **Established [L]:** Eventual Robin and Nicolas inequalities are exact RH criteria; fixed k-free and positive exponent-defect classes satisfy partial margins.
- **Open:** Source sign on increasingly prime-saturated extremal integers/primorials at square-root remainder scale.
- **E:** R:RobinCriterionRiemann; R:NicolasInequalityRiemannConverse; R:RobinInequalityKFree.

## Route candidates

<a id="apf"></a>
### APF — Arithmetic paired Fredholm

- **Path:** Prime source → divisor exhaustion → Fourier-trace vanishing → RH.
- **Established [L]:** Fredholm index and actual cycle-trace Fourier reconstruction.
- **Open:** Zero-independent exhaustion/vanishing of all trace coefficients; the reconstructed coefficients already encode the off-line zero terms.
- **E:** R:PaperZetaCycleFourierReconstruction; R:PaperPrimeFredholmReconstruction.

<a id="bsh"></a>
### BSH — Arithmetic mate curvature

- **Path:** Literal prime−Gamma section → mate identity → orientation.
- **Established [L]:** Framed curvature/compact-ideal diagnostics distinguish on/off-line fibres (`n^(2 Re s − 1)` radial character); finite cutoffs are trace-blind.
- **Open:** Construct a pre-divisor arithmetic section and mate identity coupling the fibre parameter `s` to `Ξ(s)=0` without assuming the radial character is zero.
- **E:** R:DeningerOneSidedFramedMateCurvatureTransgression; R:PaperDeningerFramedCurvature.

<a id="cdc"></a>
### CDC — Constitutive dagger

- **Path:** Arithmetic presentation → neutral grade → source law.
- **Established [L]:** Calibrated dagger confluence holds at a complex parameter `s` iff `Re s = 1/2` (via the radial factor `n^(2 Re s − 1)`). Logistic relative entropy bounds the native proof-exchange defect and satisfies an exact identity with Gamma-six curvature; along quadratically deep diffusive grades, individual defects vanish while total exchange work tends to `1/8`.
- **Open:** One source-defined pre-divisor potential descending on all closed error fibres and coupling `s` to `Ξ(s)=0` without assuming RH.
- **E:** R:ConstitutiveDaggerConfluence; R:PaperCompletionInformationCost.

<a id="dr"></a>
### DR — Dyadic Xi roots

- **Path:** Global compatible dyadic roots on strict-right domain → zero-free Ξ → RH.
- **Established [L]:** Common zero-free cusp roots, finite monodromy/Kummer data and capped atlas; pole-regularized log-ζ convergence to every real σ>1/2 is RH-equivalent. Smooth prime-germ and naive positive-root producers fail in their stated classes.
- **Open:** Global continuation/monodromy and source convergence of the regularized series; finite covers do not supply a common root.
- **E:** R:XiSymmetricLittlewoodZeroFreeCuspDyadicRoots; R:XiTiltPuncturedMonodromy; R:RegularizedLogZetaAbscissa.

<a id="egc"></a>
### EGC — Pole-safe contour

- **Path:** Shifted contour source → enclosed-pole cancellation plus outer source covariance/sign → RH.
- **Established [L]:** Full copy correction converges on fixed shifts; Fourier reconstruction and source-ray decay retain all copies. Admissible cofinal rectangles enclose both prescribed poles and any finite zero packet; after mass subtraction the inner source contour equals the exterior-copy tail, uniformly small on centered shifts. This inner cancellation is unconditional and retains all zeros.
- **Open:** Outer expanding-contour covariance/sign or source-ray decay strong enough to exclude off-line copies; inner mass cancellation alone is nonselective.
- **E:** R:PaperEGCCompleteCorrection; R:PaperEGCFourierReconstruction; R:PaperEGCEnclosedPoleCancellation.

<a id="ewj"></a>
### EWJ — Euler/Wold jets

- **Path:** Faithful third jets → exhaustive source budget → RH receiver.
- **Established [L]:** Exact finite-depth jets and compact-quotient character; fixed-history recovery misses transverse operator gaps.
- **Open:** Zero-independent admission and norm exhaustion, not finite-jet feasibility.
- **E:** R:PaperEulerWoldDepthHistory; R:PaperEulerWoldCompactCharacter.

<a id="fel"></a>
### FEL — Theta likelihood

- **Path:** Predeclared likelihood history → zero/prime contrast balance → RH.
- **Established [L]:** Exact probability, conditional KL, finite reflection-gap accounting, and certified adaptive circle-observation histories whose full reveal expenditure equals the posterior entropy deficit plus spot debt.
- **Open:** Source-derived cofinal zero-to-contrast balance; coarsening and adaptive posterior accounting alone cannot select the line.
- **E:** R:PaperThetaObservationHistory; R:PaperCircleAdaptiveHistory; R:PaperCircleAdaptiveBoundary.

<a id="hj"></a>
### HJ — Hurwitz reflection

- **Path:** Rational source fibres → reflection residual zero → RH.
- **Established [L]:** Hurwitz fibre/reflection and norm-observation receivers preserve the exact two-seed residual `primeTailSeedTwoReflectionResidual ρ = 2^(ρ−2) − 2^(−ρ̄−1)`, which depends only on the prime `2`, equals `SEC`'s first-prime seam charge, and vanishes at a parameter `ρ` iff `Re ρ = 1/2` (hence vanishes on `XiDivisorSupport` iff RH).
- **Open:** Pre-divisor arithmetic source functional coupling `ρ` to `Ξ(ρ)=0` and forcing the residual to vanish; parameter-wise evaluation at `ρ` contains no higher-prime or Ξ input.
- **E:** R:PrimeTailSeedHurwitzReflection; R:PaperHurwitzWallApproach.

<a id="irk"></a>
### IRK — Rotation-algebra trace

- **Path:** Arithmetic boundary defect → K₀/Chern landing → integral orientation.
- **Established [L]:** Finite-word traces, local winding and quotient-ideal diagnostics. The full Xi-jet relation has an explicit inverse in the closed rotation algebra off-line, including nilpotent jets; on-line it has no left inverse. Its logarithmic trace equals literal boundary winding. The pre-completion relation has nonzero cokernel at every Xi zero; this cokernel is not the original Poisson source. Rank+θ·Chern alone does not select the divisor.
- **Open:** Global arithmetic Poisson/projective lift with integral analytic count and correct source defect; completed relation invertibility is zero-side classification, not source orientation.
- **E:** R:PrimeRotationXiRelativeKTwo; R:PrimeRotationCanonicalTraceIntegrality; R:PrimeRotationXiCompletedResolution.

<a id="msc"></a>
### MSC — Möbius−Sonin transport

- **Path:** Fixed squarefree arithmetic Hilbert source preserving strict-right divisor/conormal → Sonin energy sign → RH.
- **Established [L]:** Real-power rigging moves the divisor; polynomial and broad LP multiplier transports cannot preserve the required Ξ preimage. A fixed density+squarefree-discrepancy Hilbert source recovers μ² coefficients, the squarefree partition and derivative on Re s>1/2 away from s=1; strict-right zeros retain Xi multiplicities, and fixed clock/source tangent reproduce the overlap/Fisher conormal. Literal Dirichlet columns can remain non-ℓ²; no positive Sonin energy follows.
- **Open:** Source-faithful bridge from this squarefree Hilbert observation to a nonnegative Sonin/Weil energy or other RH-closing sign, retaining the complete signed arithmetic source; divisor/conormal preservation alone is not a sign producer.
- **E:** R:HedenmalmGammaSewnSquarefreeFisherThresholdTrackedRigging; R:XiRealRootedPolynomialPreimage; R:SquarefreeDiscrepancyHilbertTransport; R:HedenmalmSquarefreeSummatoryConormalTransport.

<a id="pcs"></a>
### PCS — Singular co-shift

- **Path:** Singular ground → wall-class annihilation preserving forward mode → RH.
- **Established [L]:** Complex/wall ground is explicit. Finite-prime co-shift projections converge strongly but retain norm and compact-ideal wall gaps; fixed-history observations miss the gap. Reflection-odd wall class vanishes exactly on the line.
- **Open:** Source-natural annihilation of wall class without deleting the forward mode.
- **E:** R:PaperPrimeCoShiftCalkin; R:PaperPrimeCoShiftCofinalGap; R:PaperPrimeCoShiftSolidObservation.

<a id="ptr"></a>
### PTR — Photonic source

- **Path:** Prime-faithful lossless port/stack → real-rooted transfer limit Ξ → RH.
- **Established [L]:** Finite lossless stacks are real-rooted, and RH holds iff `XiC` is a locally uniform limit of finite products of lossless Maxwell stack entries; however, the proved converse constructs stack factors `ptrPairSlab γ τ` by inserting the unknown zeros `γ` of `Ξ` into the impedance `cot²(γτ)` (zero-indexed). Field-density, thin-slab, cosine-defect and zero-count laws constrain any Xi limit. The actual cosine-producer source lives in the continuum Poisson port `L²(ℝ)`, but at every positive depth gap `d>0` the continuum Poisson port stays at operator norm and Calkin distance `1` from the identity. Finite Euler/local ports and fixed-depth resonance-free handoffs fail.
- **Open:** Zero-free (pre-divisor) nonlocal prime-faithful continuum port preserving the exact Ξ divisor, or independent zero-loss theorem overcoming the unit Calkin gap of the continuum Poisson port.
- **E:** R:PhotonicLosslessProductPortRH; R:PhotonicLosslessProductPortThinSlab; R:XiCosineShiftDefectZeroDensity; R:PaperPoissonNativeSource; R:PaperPoissonCompletionGap.

<a id="rfhm"></a>
### RFHM — Support grade

- **Path:** Phase/depth/compound-faithful source → broken inverse covariance → wall law.
- **Established [L]:** Exact survival/KL/entropy accounting; reversible sewing remains inverse-covariant and cannot orient Reρ.
- **Open:** New source covariance/creation law retaining phase, depth and compounds.
- **E:** R:PaperRFHMSurvivalInformation.

<a id="sc"></a>
### SC — Stokes/Witt−Krein

- **Path:** Cross-fibre indefinite invariant → source orientation.
- **Established [L]:** Rigged fibres are chamber-constant; Fourier reconstruction has a common null set, but canonical polarization is wall-singular.
- **Open:** Source-fixed cross-fibre indefinite restriction/index selecting the critical wall.
- **E:** R:PaperKreinWallFourierCompletion.

<a id="sec"></a>
### SEC — Adjacent prime seam

- **Path:** Exact eventual compactness or time-one factorial-Fock jet boundedness → zero seam jump → RH.
- **Established [L]:** Essential norm equals seam jump; compact-ideal cost is zero at a parameter `ρ` iff endpoint charges agree (`Re ρ = 1/2`), while asymptotic smallness across large primes is automatic and nonselective. At Meixner time `θ = 1`, the reflected prime-seam transform along the inward real ray cancels on `Re ρ = 1/2` and has boundary pole residue `±√2` off the line, making finite-jet factorial-Fock boundedness at every `ρ ∈ XiDivisorSupport` equivalent to RH.
- **Open:** Pre-divisor source proof of exact eventual compactness or factorial-Fock jet boundedness at actual Ξ zeros without post-divisor `XiDivisorSupport` indexing.
- **E:** R:XiPrimeSeamAdjacentEssentialNormNoGo; R:PaperPrimeSeamIdealTrace; R:TimeOneGammaJetFockRHCriterion.

<a id="w1c"></a>
### W1C — Clifford–Dirac / centred Lee–Yang

- **Path:** Arithmetic operator/domain or centred ferromagnetic producer → real-rooted Ξ → RH.
- **Established [L]:** Bare operator lacks point spectrum/compact resolvent. Lee–Yang holds for finite ferromagnetic graphs; an Ising magnetization limit Ξ/Ξ(0) would imply RH. Field-density/centering constraints and LP-maximality exclude finite-order, fixed-depth and simple prime-log ports. At a prime Γ-site pivot, nonnegative-fugacity dual-spectrum containment forces active walls into a divisibility chain with sharp logarithmic size bound; nondividing pairs create nondual frequencies. Finite Hermitian-positive pencils have only real determinant roots, but no such resolvent trace equals a local Euler factor on all nonreal regular points.
- **Open:** Source-defined couplings with centred slow-field law converging to Riemann's measure, or a faithful arithmetic scattering denominator; interaction-driven critical edge density required.
- **E:** R:WeightOneCliffordSpectralNoGo; R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:RiemannKernelLaguerrePolyaSymbol; R:LeeYangPrimePivotSpinPartitionSpectrum; R:HermitianPencilEulerFactorObstruction.

<a id="wbf"></a>
### WBF — Source certificates

- **Path:** Arithmetic certificate stream → uniform-depth positive completion → Ξ landing.
- **Established [L]:** Purely abstract operator-genealogy theorems in `HTGeometry` on bounded scalar streams `0 < c_n ≤ B` (no primes, ζ, or Ξ appear in these modules): finite genealogy Gram determinants recover coefficient magnitudes; critical relative determinants classify square-summable perturbations; strong finite-prefix convergence and zero finite-prefix ideal cost coexist with infinite Calkin cost for nonzero completed genealogy.
- **Open:** Define an arithmetic certificate stream and a source-faithful depth-uniform completion landing on Ξ/Weil positivity; abstract scalar Gram completion supplies no arithmetic coupling or sign.
- **E:** H:PaperGenealogyFredholmRecovery; H:PaperGenealogyDeterminantGauge; H:PaperCriticalGenealogyCompletion.

## Shared constraints

- Finite jets, packets, and prefixes do not establish a cofinal sign; scoped failures and surviving routes: [killed routes](rh-killed-routes.md).
- Reflection-even or magnitude-only observations cannot supply reflection-odd arithmetic orientation. Full-positive perturbations of Λ under subcritical deviation are rigidly Λ. E: R:WeilLittleOVonMangoldtRigidity; R:EstermannDeformationObstruction.
- RH ⇔ zeros approach the line (ZAL) plus asymptotic abscissa law (AAL). Either condition alone misses residual off-line configurations. E: R:ZerosApproachLineAttainment; R:AsymptoticAbscissaLawProducers.
- No nonzero continuous compactly supported test has Fourier–Laplace transform vanishing at every real zero of `Ξ` (since `f̂` has exponential type `O(R)` zeros in `|z|≤R` against `≍ R log R` real zeros of `Ξ`), so no nonzero compactly supported test is divisible by `Ξ` or `Ξ²`. E: R:CompactTestXiDivisibilityObstruction.
- The closed critical prime-log Laplace synthesis graph has exactly the literal positive-time L² profile domain; positive prime damping gives Hilbert–Schmidt outputs and tends strongly to identity. Domain admission supplies no Weil sign or Xi landing. E: R:PrimeLogLaplaceClosedGraphLiteral; R:PrimeLogLaplaceDamping; R:PrimeLogLaplaceMaximalDomain; H:BurnolWeightedShiftStrongContinuity.
- Actual prime-log Burnol features are total in the half-line L² space. A bounded operator preserving each prime feature line is uniquely a bounded holomorphic half-plane symbol; its norm is the symbol supremum, and first/cubic prime Pick positivity is equivalent to bounded holomorphic interpolation. Physical nonnegativity is equivalent to positive packet tests and a unique finite positive shift measure, whose total mass is the operator norm. Every bounded positive contractive prime-preserving generator is uniquely finite jump measure plus nonnegative killing; unit-jump dynamics exist. Unbounded accretive prime-symbol graphs and contraction evolutions are closed/m-accretive with dense Cayley resolvent range (`[L]`); the reciprocal-symbol example shows bounded prime eigenvalues alone do not give a bounded operator. Analytic/operator classification, not an RH receiver or source sign. E: R:PrimeBurnolFeatureTotality; R:PrimeLogHolomorphicUniqueness; R:PrimeBurnolPickCone; R:PrimeBurnolSymbolClassification; R:PrimeBurnolPositiveMeasureClassification; R:PrimeBurnolFiniteJumpClassification; R:PrimeBurnolAccretiveSymbol; R:PrimeBurnolAccretiveGraph; R:PrimeBurnolAccretiveEvolution; R:PrimeBurnolAccretiveIntegral; R:PrimeBurnolAccretiveGenerator; R:PrimeBurnolReciprocalGenerator; H:CayleyDenseResolvent.
- [L] The Cayley transform `C=(Z−1)(Z+1)⁻¹` of the identity accretive symbol on `BurnolHalfLineL2` has rank-one third hereditary defect `1−3C*C+3(C*)²C²−(C*)³C³ = 4|ψ₁⟩⟨ψ₁|`, dense adjoint orbit, and generates the compact operator ideal in its elemental `C*`-algebra; no Xi/Weil landing. E: R:PrimeBurnolCayleyDefect; R:PrimeBurnolCayleyOrbit; R:PrimeBurnolCompactCalculus; H:DenseRankOneCompactClosure.
- [L] Positive Burnol Lévy data allow infinite jump activity; their literal prime-feature evolution has a dense-range closed backward relation. Drift times time determines injectivity and backward prime-span closability; a closed dense-domain minimum-norm inverse exists, but unbounded exponent precludes a bounded inverse. Infinite jump activity gives injective pure-jump evolution and strong cutoff recovery. A prime Lévy example realizes the unbounded inverse; no Xi/Weil sign follows. E: R:PrimeBurnolLevySymbol; R:PrimeBurnolLevyInverseGraph; R:PrimeBurnolLevyPrimeAction; R:PrimeBurnolLevyMinimumInverse; R:PrimeBurnolLevyAsymptotics; R:PrimeBurnolPureJumpInjectivity; R:PrimeBurnolPrimeLevyExample.
- Compact-polar Xi sampling is faithful but zero-side; finite Xi jets have an exact least trace-energy metric defect under a condition-number budget, not a source-positive arithmetic form. E: R:XiCompactPolarWeilRealization; R:XiJordanSharpMetricBudget.
- Pole-free Dirichlet cones (odd conductor `≥10`, even `≥216`) and level-one modular cones (weight `≥14`) contain zero weights. A boosted ζ archimedean density `+C(1+|t|)^θ`, any `θ>1/4` with suitable `C>0`, admits trivial weights. Cone positivity after changing archimedean datum does not select the original Λ. E: R:WeilConePoleDualityAnatomy; R:TrivialWeightBoostedWeilCone.
- The negative archimedean anomaly window has edge `t₀` with `2π<t₀≤2π+1/50`; locating it supplies no full Weil sign. E: R:AnomalyWindowTwoPi.
- [L] Compact-test Weil line integral and Herglotz-to-full-positivity bridge hold on any absolute-convergence abscissa; a positive-real-part source remains a premise. For real-coefficient degree-`d>0` conductor-one twins `T` with `a(1)=1`, entire finite-order reflection-even completion `(s(s−1))^κ Γℝ(s)^d T(s)`, and all zeros on `Re s=1/2`, necessarily `κ=d`, RH holds, and `T=ζ^d` on its convergence half-plane. Nonzero real functional-equation-compatible entire finite-order perturbations of `ζ^d` therefore have an off-line completed zero. E: R:WeilLineIntegralAnyAbscissa; R:HerglotzWeilBridgeAnyLine; R:CompletionOrderOneEnvelopeAnyLine; R:TwinRigidityZetaPower; R:TwinRigidityPoleOrder; R:TwinRigidityOffLineZero.
- Translated completed Dirichlet germs `completedLFunction χ_i (2s+b_i)` are differentially independent over the field of all convergent Dirichlet series (`dirZetaBase`) iff their archimedean pole labels `(b_i+parity(χ_i))/2` lie in distinct `ℤ`-orbits; explicit translated palettes and `(ζ, L(·,χ₋₄))` realize arbitrary finite ranks and both parities. Algebraic independence of completions does not orient zeros. E: R:CompletedDirichletArithmeticSource; R:CompletedDirichletUpperEnd; R:CompletedDirichletOrbitIndependence; R:CompletedDirichletExplicitPalette.
- For integers `n≥1`, archimedean phase resonance `Ω(τ)=−log n` exists exactly when `n≤8πexp(γ+π/2)`; for `n≥2` every such `|τ|<2π`. Frequency restriction supplies no Weil-form sign. E: R:ArchimedeanResonanceRange.
- Other RH receivers and falsifiers: [endpoints](endpoints.md); no independent source producer follows from a receiver.

## Alias lookup

C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P,PW-B→PM; G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. Retired labels: [killed routes](rh-killed-routes.md#retired-labels).
