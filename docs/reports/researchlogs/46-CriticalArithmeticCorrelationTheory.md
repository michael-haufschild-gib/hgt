# CriticalArithmeticCorrelationTheory: mathematical facts

Namespace `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`. 105 modules. Main object: the complete Weil form of an atomic test family at overlap/width c/N on the horizon {1..N} (completeWeilEnergy φ c N), profile φ ∈ C², supported in [0,1], ∫φ² > 0.

## TheCompleteWeilReserveHasAnExplicitTouchingHorizon
- The non-ratio (boundary) correction matrix fullWeilNonRatioMatrix has form and operator action ≤ (D log(N+1)/N)‖x‖² for c ∈ (0,1], N ≥ 2 (Hermitian: form bound ⇒ action bound via eigenbasis).
- Explicit reserve through touching: ∃a, ∀N ≥ 2, c ∈ (0,1]: a‖x‖² + ((1 − q)/2)·poleDefect_N(x) ≤ completeWeilEnergy, q = completeWeilPoleShift φ 1 < 1. Decomposition: atomic Weil form + pole defect, center matrix, cross error ≤ 4C c², pole error, self finite part monotone in c, non-ratio ≤ D.
- Exponential conductor cutoff with explicit horizon: every unit x with nonpositive complete Weil energy is η-close to the span of the first R Ramanujan pole profiles, R ≤ e^{D(C+1)}, for all N ≥ 2, c ∈ (0,1].

## TheCompletedSourceWorkHasALogarithmicCeiling (uses ArithmeticElectrostatics TheSelbergWorkExhaustsTheTransverseEnergy, RHTower LorentzianZeroMass)
- sourceLogEnvelope R = c_ξ + log(R + 4). Transverse angular ≤ 1/(1 + d²) for x² ≤ 1; reflected energy ≤ 2/(1 + d²).
- log(|t| + 4) ≤ log(R + 4) + |t|/R; damping × log row cost ≤ R²(L + 1)/(R² + t²).
- Damped Lorentzian row summed: Σ_{p,q} ≤ 64R·L(L + 1) (unit-width row sum then width-R Lorentz mass ≤ (8/R)L).
- Full reflected pair work ≤ two damped rows; xiDampedSourceWork R ≤ 64R L(L + 1) = O(R log²R) for R ≥ 4, multiplicities and exterior rows retained. Tapered finite readings: |xiTaperedSourceWork R N| ≤ 128R L(L + 1) uniformly in N.

## SmoothPlateausRecoverTheCompletedRobinMargin (uses SSHA TheMarkovFormFailsInsideTheSeparatedRegime, RHTower SharpWeilNearRadicalCount)
- Robin density (∫(g(u) − g(u+y))²)/(2y) integrable on (0,1] (dominated by the Lévy density).
- Plateau autocorrelation ∫ plateau(u)plateau(u+y) ≤ 1 − y; Robin integral bumpRobin(plateau η) ≥ (1 − δ)(1 − 2η/δ); charge ∫ plateau ≥ 1 − 2η.
- Completed shape (Robin/mass + charge²/mass) ≥ (1 − δ)(1 − 2η/δ) + (1 − 2η)²; can exceed any a < 2. Since log(2π) < 2, some smooth plateau has completed Robin margin > log(2π).

## ThePlateauShapeAndChargeHaveTheirIndicatorLimits
- As η → 0⁺: ∫ plateau² → 1, ∫ plateau → 1, Robin → 1 (upper bound 1 + 2Cη − 4η log η via Lipschitz transition); normalized Robin → 1; charge ratio → 1; completed shape → 2; completed margin → 2 − log 2π. Margin attained while filling the unit support.

## SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive (uses RAPT TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum)
- Below unit width, completed shape + pole shift − log 2π ≤ completeWeilAdjunctionEnergy(φ, c, 1) (conductor-one energy).
- If T < conductor-one energy at fixed c < 1, eventually every complete Weil eigenvalue ≥ T (adjunction energies increase in conductor; spectral count exhaustion).
- For every b < 2 − log 2π and ε: some plateau (mass > 1 − ε) has, at every fixed c ∈ (0,1), eventually all eigenvalues ≥ b; complete Weil matrix eventually positive definite at every fixed strictly separated width (horizon depends on c).

## HarmonicMassFollowsDelayedCounting (uses HTGeometry ShiftPartialSummation)
- Nonnegative f with Σ_{i<N} f ≥ (N − K)C: Σ f(i)/(i+1) ≥ (H_N − H_K)C (summation by parts, exact loss H_K); also ≥ (log(N+1) − log(K+1))C.

## GrowingRamanujanFamiliesHaveASquareRootHorizon (uses BVI LargeSieveWithTheMontgomeryVaughanConstant, UniformLagWindowCovarianceAtQuadraticOrder; RAPT TheRamanujanPoleProfilesArePrimeQuasimodes)
- Normalized Ramanujan packet Σ_{m≤Q} c_m normalizedRamanujanMode m n: on any window of K consecutive n, |Σ (packet)² − K Σc²| ≤ Q(Q−1)Σc² (primitive roots of distinct orders disjoint; coefficient mass equals conductor mass; two-sided large sieve with Montgomery–Vaughan constant).
- Harmonic lower frame: Σ_{n≤N} (Σ c_m ramanujanPoleProfile m n)² ≥ (H_N − H_{Q(Q−1)})Σc², ≥ (log(N+1) − log(Q(Q−1)+1))Σc², ≥ (log(N+1) − 2 log Q)Σc²: uniform over coefficient vectors and horizons.

## RamanujanFamiliesHaveExplicitCoordinateMass (uses RAPT BoundedPrimeEnergyHasFiniteRamanujanCoordinates)
- Normalized horizon vectors (divided by √log N): lower frame constant ½ once Q⁴ ≤ N.
- A unit vector within squared distance ¼ of a span of conductors ≤ Q has Σ_{m≤Q} ⟨x, normalized vector_m⟩² ≥ 1/18 at N ≥ Q⁴; same from raw profile approximation with R ≤ Q.

## BoundaryVanishingControlsTheTouchingAutocorrelation (uses ACT ShiftedGroundStateKernelBounds, SSHA TheArchimedeanPairingOfTwoAtoms)
- Continuous g supported in [0, w] vanishes at both endpoints; L-Lipschitz ⇒ |autocorr g z| ≤ (L²w/4)(w − |z|)² (quadratic endpoint decay at last overlap).

## EndpointDecayRemovesTheCrossKernelGapLoss (uses SSHA TheArchimedeanDensityHasQuadraticIncrementControl, RAPT TheAtomCrossMatrixIsCloseToItsCenterKernel)
- |Lévy density(s + z) − density(s)| ≤ 38w/(s − |z|)² for |z| ≤ w < s.
- Cross-term replacement |atomCrossTerm g s − density(s)(∫g)²| ≤ 19L²w³, independent of the gap s − w.
- Every smooth compact profile: normalized cross error ≤ C w²/s² uniformly over widths w and gaps s > w (far case 2w ≤ s via window bound, near case via endpoint Lipschitz).

## TheTouchingCrossMatrixHasAUniformErrorBudget (uses RAPT TheCompleteWeilEnergyControlsThePrimeDefect)
- Distinct n, j ≤ N have |log j − log n| > 1/N, so atoms of width c/N ≤ 1/N are separated up to touching c = 1.
- Entry bound: |atomCrossErrorKernel(n, j)| ≤ C(c/N)² max(n,j)²/|n − j|²; quadratic form ≤ 4Cc²Σx²; bounded pole profiles have residual ≤ (36CAc²)²; the full cross-error matrix form ≤ 4Cc²‖x‖², uniform in N and c ∈ (0,1].

## TheChargeDeficitKeepsAUniformPrimeReserve
- Nonzero continuous profile on [0,1]: (∫φ)² < ∫φ² (positive variance against constants; φ(0) = 0 forces non-constancy). Hence completeWeilPoleShift φ c = c(∫φ)²/∫φ² < c.
- Uniform charge-defect reserve: ∃a, ∀ fixed c ∈ (0,1), eventually in N: a‖x‖² + ((1 − q)/4)·poleDefect ≤ completeWeilEnergy (horizon depends on c).

## OverlapLengthControlsTheTouchingCrossError (uses AIP CubicGaugeSurplusPotential, SSHA TheMarkovFormFailsInsideTheSeparatedRegime)
- |autocorr g z| ≤ B²(w − |z|) for |g| ≤ B on [0, w] (overlap length).
- Height-only cross error: |atomCrossTerm g s − density(s)(∫g)²| ≤ B²w(1 + w/2) (Lévy density ≤ 1/(2t) + 1/4), no derivative cost.
- For w ≤ 1: normalized cross error ≤ ((152(∫|φ|)² + 6B²)/∫φ²)w²/s²; for plateaus (η ≤ ¼) ≤ 316w²/s² uniformly as plateaus approach the indicator.

## OnlyTheBoundaryStarEntersAtTouching (uses SSHA TheRowsAtBoundedOverlap)
- For a ∈ [1, N], b ≥ 1, a ≠ b, |log b − log a| ≤ 1/N forces a = N, b = N + 1 (log(N+2) − log N > 2/(N+2) ≥ 1/N).
- At width ≤ 1/N the non-ratio lag terms vanish except the boundary pair (N, N+1): nonRatioLag = 2·bumpCorr(log(N+1) − log N)·x_N·Σ_{km=N+1} x_m; nonRatioForm = 2 bumpCorr(·) Σ_{k∈[2,N+1]} Σ_{km = N+1} Λ_atom(k) x_N x_m (a single weighted boundary star).

## TheBoundaryPrimeStarVanishesAfterNormalization
- Boundary weights Σ_{km=N+1} Λ_atom(k) ≤ log(N+1) (divisor identity). |nonRatioForm| ≤ 2|bumpCorr|·log(N+1)·Σx².
- 1/(N+1) < log(N+1) − log N < 1/N, defect ≤ 1/N².
- At touching width 1/N: normalized |nonRatioForm|/∫g² ≤ (2B²/∫φ²)(log(N+1)/N)Σx²; for every c ∈ (0,1] ≤ (4B²/∫φ²)(log(N+1)/N)Σx² (c ≤ ½: the boundary star vanishes exactly; c > ½: overlap length ≤ 1/N²).
- Every smooth nonzero profile: uniform non-ratio budget D log(N+1)/N → 0, uniformly in c ∈ (0,1].

## TheActualArchimedeanMatrixReachesTouching
- At width w ≤ 1/N: atom mass Gram is diagonal; mixed Lévy integrand keeps the translated cross formula; markovPair + primePair = 2·gammaHardyPhaseRate(0)∫g² + levyEnergy g on the diagonal and −atomCrossTerm g |log j − log n| off it.
- Literal complete Weil horizon matrix entries at touching: (archimedean entry) − primePair(atom n, atom j) + (∫g e^{−u/2})(∫g e^{u/2})·arithmeticPoleKernel(n, j); normalized version divides by ∫g². No non-ratio term is discarded.

## TheNonRatioMatrixIsTheActualPrimeCorrection (uses SSHA TheRowsAtBoundedOverlap)
- Prime pairing is linear in compactly supported smooth families; primeSum(Σ x_i e_i) = Σ_{i,j} x_i x_j primePair(e_i, e_j); the horizon prime-pair matrix form = primeSum of the synthesized atomic test.
- fullWeilNonRatioMatrix = (∫g²)⁻¹·[primePair(atom n, atom j)] − weilPrimeKernel (Hermitian); its form equals nonRatioForm/∫g² exactly at every width.
- Eventually (uniformly in c ∈ (0,1]) its form and operator action are ≤ ε‖x‖².

## TheCompleteWeilMatrixKeepsItsBoundaryCorrection
- Pole product (∫g e^{−u/2})(∫g e^{u/2})/∫g² = atomPoleErrorCoefficient + completeWeilPoleShift(c)/N; charge²/mass = pole shift/N.
- Exact decomposition through touching (c ∈ (0,1]): completeWeilMatrix = (log N + selfFinitePart(c) − γ + selfError)·1 − fullPrimeMatrix + centerMatrix(pole shift) − crossErrorMatrix + poleErrorMatrix − nonRatioMatrix. completeWeilEnergy = renormalizedPrimeEnergy + (selfFinitePart − γ + selfError)‖x‖² + center − cross + pole − nonRatio.

## TheSelfAndPoleErrorsStayUniformAtTouching
- completeWeilSelfFinitePart(c) = −log 2π − log c + Robin/∫φ²; 2 gammaHardyPhaseRate(0) + log(N/c) + profileRobin − log N = selfFinitePart − γ.
- |selfError| ≤ (e^{1/2}/2)(c/N); |atomPoleErrorCoefficient| ≤ K_pole (c/N)²; pole error form ≤ 2K_pole c²‖x‖²; pole-profile residual ≤ 4K²A²c⁴, all for c ∈ (0,1].

## OnePrimeDefectReserveCoversEveryRatioThroughTouching
- Uniform reserve: ∃a, eventually in N, ∀c ∈ (0,1]: a‖x‖² + ((1 − q)/4)·poleDefect ≤ completeWeilEnergy (one horizon and one mass floor for all ratios up to touching).

## OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching (uses RAPT BoundedCompleteWeilEnergyHasFiniteRamanujanCoordinates)
- The uniform reserve bounds the pole defect on every energy sublevel {‖x‖ = 1, energy ≤ T}, uniformly in c ∈ (0,1].
- Arithmetic compactness: one finite Ramanujan conductor set S approximates every such unit vector to squared error η; and gives coordinate mass Σ_{m∈S}⟨x, normalized vector_m⟩² ≥ 1/18, one horizon for all ratios.

## TheReplacementErrorsVanishUniformlyThroughTouching (uses RAPT TheWeilReplacementErrorsVanishOnRamanujanModes)
- A residual with uniform square bound C becomes ≤ ε after √log N normalization (C/log N → 0).
- On each fixed normalized Ramanujan mode, uniformly in c ∈ (0,1]: cross error action, pole error action, self error, and center residual (center matrix minus pole-shift ground charge at m = 1, linear in c) all → 0.

## RamanujanQuasimodesAreUniformThroughTouching
- Residual of the complete matrix on normalized Ramanujan mode m relative to completeWeilAdjunctionEnergy(φ, c, m) decomposes into six terms (prime residual vs log N − E_m, self, center, cross, pole, non-ratio); each small with one horizon for all c ∈ (0,1]: normalized Ramanujan modes are uniform quasimodes.

## OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching
- Strict charge keeps conductor one below every excitation: completeWeilAdjunctionEnergy(c, 1) < (c, m) for m ≥ 2 (pole shift < 1 ≤ 2 log 2 ≤ adjunction gap).
- Spectral exclusion: for b < completed shape + pole shift(1) − log 2π, eventually every eigenvalue ≥ b for all c ∈ (0,1] (low eigenvector has coordinate mass ≥ 1/18 on S, but each quasimode with energy gap δ forces coordinate ≤ ε/δ).
- Near-unit plateau: for b < 2 − log 2π and ε > 0 some plateau with mass > 1 − ε has a single horizon N₀ with all eigenvalues ≥ b, energy ≥ b‖x‖², complete Weil matrix positive definite for every c ∈ (0,1] (up to and including touching).

## MacroscopicOverlapSpectralAssembly
- Fixed-overlap spectral assembly (any fixed c, no size condition on c): defect reserve a‖x‖² + βD_N(x) ≤ W_N(x) (β > 0) + norm quasimodes ‖W_N r̂_m − E_m r̂_m‖ → 0 for normalized Ramanujan vectors + common floor e ≤ E_m ⇒ eventually every eigenvalue ≥ b for every b < e; e > 0 ⇒ eventually positive definite.
- Mechanism: reserve bounds the defect on sublevels ⇒ finite Ramanujan span S carries mass ≥ 1/18; quasimode with gap δ forces coordinate² ≤ ε²/δ² on the low spectral subspace; choose ε = δ/(6(|S|+1)).

## FiniteRamanujanCoordinatesTransferSpectralFloors
- Same transfer for any Hermitian matrix family A_N with Ramanujan norm quasimodes and finite-coordinate capture of low-energy unit vectors: b‖x‖² ≤ ⟨A_N x, x⟩ eventually. Applies to linear combinations of prime and complete Weil operators without commuting spectral projections.

## ShiftingThePrimeEnergyGivesALogarithmicDefectReserve (uses RAPT PrimeDefectConfinementMustRetainLowEnergyConductors, TheConductorEnergyKeepsALogarithmicReserve)
- shiftedCompleteWeilMatrix = completeWeil − δ(log N·1 − fullPrime); form = energy − δ·renormalizedPrimeEnergy. Prime energy ≤ poleDefect + (log 8 + 4)‖x‖² (row bound).
- Shifted matrix has quasimodes with energies completedConductorEnergy(c, m) − δ·E_m (no commutation needed).
- If β/2·(E_m − L) ≤ completedConductorEnergy for all m: eventually β/2·(primeEnergy − (L+1)‖x‖²) ≤ completeWeilEnergy for all x.
- Tilted unit spline, c ≥ 1: complete energy ≥ (growingDefectFraction c/8)(poleDefect − (conductorLogarithmicLoss + log 4 + 5)‖x‖²). Absolute constants: ≥ (a/c⁷)(poleDefect − C log(2c)‖x‖²) for c ≥ 1, horizon depends on c.

## MacroscopicOverlapConductorFloor (uses RAPT TheShellsRepayEveryConductor, SSHA TheTiltedSplineKeepsAGammaReserveAtEveryOverlap)
- shellSpectrum |φ̂(2πt)|² integrable on half-lines. First coprime term of the repayment series: completedConductorEnergy(c, m) ≥ (2/∫φ²)∫_{t>c} shellSpectrum (weight m/φ(m) ≥ 1, starts at c/m ≤ c).
- Tilted unit spline has no real Fourier zeros ⇒ tail > 0 ⇒ uniform positive conductor floor at every c > 0.

## MacroscopicOverlapTiltedSplineReserve (uses TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap)
- Tilted spline defect reserve transported to matrix coordinates at every fixed c > 0; positivity of its complete Weil matrix at fixed c reduces to the norm quasimode law with completed conductor energies.

## WeightedAffinePrimeWindowsAreUniform (uses ActualAffinePrimeWindowsAreUniformInTheirParameters, RHTower MertensFirst)
- Mertens window: Σ_{U<k≤V} Λ(k)/k ≤ log V − log U + 2(log 4 + 4).
- Riemann sum of ∫_a^1 F(t)dt/t on grid i/D for Lipschitz F vanishing on [0, a]: error ≤ ℓ log D/D.
- Weighted affine prime windows: for q > 0 and F Lipschitz on [0,1] vanishing on [0, a], a > 0: Σ_{k≤X} Λ(k)/k·c_q(kn + h)·F(k/X) → (c_q(n)c_q(h)/φ(q))∫_a^1 F(t)dt/t uniformly in n, h and real X (grid of D windows; Mertens pays window oscillation, leftover and Riemann error; c_q bounded by φ(q)).

## MacroscopicOverlapPositivityAtEveryOverlap (uses RAPT TheUpwardPrimeWindowsCarryTheShellCorrection, TheCompleteWeilResidualIsTheUpwardDefect)
- Norm quasimodes at every fixed overlap c > 0: complete Weil residual on normalized Ramanujan vector = −upward defect + o(1); upward non-ratio prime rows carry shell correction κ_m(c) in ℓ² ⇒ ‖W_N r̂_m − completedConductorEnergy(c, m) r̂_m‖ → 0.
- Positivity at every fixed overlap: for the tilted unit spline and every fixed c > 0 the complete Weil matrix is eventually positive definite; in particular at the macroscopic overlap c = 3/2 (overlapping atoms). Horizon depends on c.

## CyclotomicNormGivesAConductorUniformCurvatureFloor (uses AIT TheArchimedeanIntersectionIsALogOrder, HTGeometry AlgebraicIntegerSeparation)
- A nonvanishing geometric prefix Σ_{j<k} ζ^j (m ∤ k) is a nonzero cyclotomic integer; its norm gives Π_{ζ primitive} |Σ_{j<k} ζ^j| ≥ 1.
- AM–GM: primitiveRootPrefixEnergy(m, k) = Σ_ζ |prefix|² ≥ φ(m) when m ∤ k (uniform in conductor and length).
- Interpolated arithmetic overlap curvature: φ(m)·u(1 − u) ≤ curvature(m, k + u); normalized curvature/φ(m) ≥ frac(t)(1 − frac(t)) for t ≥ 0.

## TheArithmeticCurvatureHasAnExactGramCompletion (uses HTGeometry FiniteHilbertDispersion)
- Prefix differences are unit rotations of shorter prefixes: |P_ζ(i) − P_ζ(j)| = |P_ζ(dist(i, j))|. primitiveRootPrefixEnergy(m, dist(i,j)) = Σ_ζ |P_ζ(i) − P_ζ(j)|² (squared Hilbert distance).
- Centered kernel primitivePrefixGram(m, i, j) = Σ_ζ ⟨P_ζ(i), P_ζ(j)⟩: quadratic form = Σ_ζ |Σ a_i P_ζ(k_i)|² ≥ 0. Uncentered curvature is conditionally negative: on Σa = 0 the form = −2Σ_ζ|Σ a_i P_ζ(k_i)|².
- Integer samples of the real curvature are the prefix energies; distinct prefix classes (m ∤ dist) are separated by ≥ φ(m) (distance bound, not a Gram floor).

## CyclotomicDivisibilityClassifiesTheOverlapGramRadical (uses BVI SelbergSupportExactRecurrenceComplexity)
- Packet polynomial Σ a_i C(·)(1 + X + … + X^{k_i−1}). Gram form = 0 ⇔ vanishes at all primitive m-th roots ⇔ cyclotomic Φ_m divides the packet polynomial. For a conductor set: radical = intersection of Φ_m-divisibility conditions. Positivity of individual prefixes does not imply coercivity on packets.

## AllDivisorConductorsRecoverTheDiscreteBridge
- Σ_{m|Q} primitiveRootPrefixEnergy(m, k) = k² + (k mod Q)(Q − (k mod Q)); conductor 1 gives k²; Σ_{m|Q, m≠1} = k(Q − k) for k ≤ Q.
- Σ_{m|Q, m≠1} primitivePrefixGram(m, i, j) = Q·min(i, j) − ij (discrete Brownian bridge covariance); bridge quadratic form ≥ 0 on [0, Q].

## CyclotomicCompletionIsThePrimeBlockJumpEnergy (uses BVI BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo)
- Conductor-completed Gram on primes p < Q equals Q·Σ_{n<Q} primePacketJumpSum(n)²/(n(n+1)) (pronic energy of cumulative prime jumps): full mixed form identity.

## RationalRefinementCompletesTheCyclotomicGram (uses AET TheIntersectionOfTorsionOrbits, THIM BuchstabSlopeLawAndPrimeHorizonDissipation)
- refinedCyclotomicConductors(m, L) = {e | mL : e/gcd(e, L) = m}. Möbius inversion after dilation is an exact positive projection onto lifted primitive orders.
- On the grid 1/L: L²·arithmeticOverlapCurvature(m, k/L) = Σ_{e refined} primitiveRootPrefixEnergy(e, k); centered arithmeticOverlapGram on the grid = Σ primitivePrefixGram ⇒ nonnegative quadratic form for arbitrary real coefficients. Finer resolution changes the conductor family, never introduces signed spectral weights.

## TheRealOverlapCurvatureIsConditionallyNegative
- arithmeticOverlapCurvature m t = Σ_{d|m} μ(m/d) d² frac(t/d)(1 − frac(t/d)) is continuous (endpoint values agree). Centered Gram ≥ 0 on all finite families of nonnegative real points (rational grid approximation); raw curvature kernel |x_i − x_j| is conditionally negative on all real points (translation).
- On the first unit cell curvature = φ(m)t; centered Gram = φ(m)·min(x, y) (Brownian kernel) for every conductor.

## PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder (uses AET TheFourierCoefficientsOfTheTorsionMeasure)
- primitiveRootPrefixEnergy(m, k) = Σ_{ζ primitive} |Σ_{j<k} ζ^j|². Over all d-th roots: Σ = k² + (k mod d)(d − k mod d). Möbius inversion: for m > 1, energy = Σ_{d|m} μ(m/d)(k mod d)(d − k mod d) (constant mode cancels) — a signed quadratic residue sum that is nonnegative.
- Energy > 0 iff m ∤ k; integer-valued ⇒ ≥ 1 when m ∤ k; = 0 ⇔ m | k.
- primitiveQuadraticCell(m, k, u) is the convex interpolation (1 − u)E(k) + uE(k+1) (Möbius cancels curvature in the cell); ≥ 0, > 0 when m ∤ k.
- arithmeticOverlapCurvature on cell k + u equals the cell interpolation exactly; ≥ u(1 − u) for every m > 1; ≥ frac(t)(1 − frac(t)) on t ≥ 0; nonnegative with no zero hypothesis.

## TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet (uses RAPT TheRamanujanPrimeRowsHaveAdjunctionEnergy)
- ramanujanLogDivisorJet(m, n) = Σ_{d|m, d|n} μ(m/d) d log d. Downward prime convolution Σ_{a|n} Λ(a)c_m(n/a) = log n·c_m(n) − jet(m, n); RAPT's downward correction = −jet.
- At a conductor multiple (upward corrections vanish): Σ_{d|m} μ(m/d) d log d = φ(m)(log m + tameDifferent(m)) (logarithmic totient identity = completed prime-row energy).

## AnnularRamanujanFamiliesHaveTwoSidedFrames (uses BVI OscillatoryPronicTailSummationByParts…)
- Annular discrepancy: |Σ_{n∈(A, A+N]}(Σ a_m ramanujanPoleProfile m n)² − (Σ 1/n)Σa²| ≤ (Q(Q−1)/(A+1))Σa² (summation by parts; cost only the first harmonic weight).
- Dyadic annulus (A, 2A] beyond 4Q(Q−1): frame constants ¼ and 5/4, simultaneously, for every coefficient vector.
- A dyadic annulus has no proper divisibility edge: weilPrimeKernel vanishes on it; prime compression to one annulus is zero; any prime energy transfer must cross annulus boundaries.

## ActualPrimeWindowsDiagonalizeAffineRamanujanModes (uses PrimeResidueWindowsConvergeToTheirUnitMean, UnitAveragesDiagonalizeSuccessorCorrections)
- Affine residue pattern r ↦ c_q(r n + h); its unit-class mean primeClassKappa = c_q(n)c_q(h)/φ(q).
- affineRamanujanPrimeWindow(q, n, h, A, B, N) = Σ_{AN<k≤BN} Λ(k)/k·c_q(kn + h) → (log B − log A)c_q(n)c_q(h)/φ(q) (source theorem, all prime powers, no correlation model). Normalized modes: window reading → (log B − log A)(c_q(h)/φ(q))·mode(n).

## ActualAffinePrimeWindowsAreUniformInTheirParameters (uses PrimeResidueWindowsControlEveryGramPacket)
- Fixed q, A ≤ B: one horizon makes the affine window within ε of its limit for all n, h (finitely many residue coordinates; Σ_r |pattern| ≤ qφ(q)).

## UnitAveragesDiagonalizeSuccessorCorrections (uses AET TheFourierCoefficientsOfTheTorsionMeasure)
- Primitive roots = coprime powers of one primitive root. Σ_{r coprime} c_q(rn + h) = c_q(n)c_q(h) (affine reduced-residue product law; same for Ramanujan sums).
- Normalized Ramanujan modes are eigenfunctions of every affine unit average with eigenvalue c_q(h)/φ(q) ∈ [−1, 1].

## PrimeResidueWindowsConvergeToTheirUnitMean (uses RAPT ResiduePatternGaugesAreMatchedByTheirMean)
- residuePrimeReading(q, F, Y) = Σ_{k≤Y} F(k mod q)Λ(k)/k − kappa(F) log Y → finite part (unit-class Mertens constants + convergent non-unit classes) for every real pattern F.
- On multiplicative windows (AN, BN]: reading → kappa(F)(log B − log A), finite part cancels.

## PrimeResidueWindowsControlEveryGramPacket
- residuePrimeWindow F = Σ_r F(r)·window(indicator_r); error vs unit mean = Σ_r F(r)·error_r; |error| ≤ errorMass·Σ|F(r)|; errorMass → 0 at fixed q, A, B.
- One horizon controls every signed residue pattern (chosen after the horizon), every real and complex Gram packet in full residue norm (feature family and coefficients may depend on N).
- Residue masses are positive (non-unit prime powers have favorable sign): eventually (log B − log A − ε)·kappa(F) ≤ window(F) for all F ≥ 0; lower operator bound in the unit Gram for every complex packet, no full-residue penalty.

## ActualPrimePrefixesDominateTheirCyclotomicGram
- Unit residues enumerate primitive roots exactly (u ↦ ζ^{val u}). actualPrimePrefixGram (von Mangoldt window of |Σ a_i·prefix(ζ^n, k_i)|²) = residue window of the prefix energy; unit mean = (Σ a_i a_j primitivePrefixGram(q, k_i, k_j))/φ(q) (full cyclotomic Gram, all cross terms).
- Eventually actualPrimePrefixGram ≥ ((log B − log A − ε)/φ(q))·cyclotomic Gram form, for all coefficients and prefix lengths (fixed q and window).

## TheFirstOverlapPrimeCostHasASmallDefectCoefficient (uses ALG TheArchimedeanCrossEnergyIsOneSided)
- For 1 ≤ c ≤ 2: Σ x_m² nonRatioRow(c/N, N, m) ≤ C₀(poleDefect + Σx²) (row bound + top-row logarithm paid by the divisor identity).
- Normalized overlap length max(0, c/N − 1/(N+1))/(c/N) ≤ c − 1 + 1/N.
- |normalized nonRatioForm| ≤ (B²/∫φ²)C₀(c − 1 + 1/N)(poleDefect + Σx²): first genuine overlap costs a small defect coefficient; for any ε there is δ such that c ∈ [1, 1 + δ] costs ≤ ε(poleDefect + Σx²) with one horizon. No prime-pair cancellation assumed.

## IntegerSeparationShrinksTheNonRatioPrimeRows (uses SSHA TheRowsAtBoundedOverlap)
- n ≤ N, j ≥ 1, n ≠ j ⇒ |log j − log n| > 1/(N + 1).
- Each non-ratio term ≤ B²·max(0, w − 1/(N+1))·upInd; |nonRatioForm g N x| ≤ B² max(0, w − 1/(N+1))·Σ x_m² nonRatioRow(w, N, m) (Schur test; finite k range; every prime power, every signed vector).

## SmoothDilationHasASmallLipschitzDifference (uses SSHA TheCriticalExponent)
- Compact C² profile φ on [0,1], 1 ≤ c ≤ 2: φ(·/c) − φ is C(c − 1)-Lipschitz (derivative bound: Lipschitz of φ' on |z| ≤ 2 plus |1/c − 1| ≤ c − 1); its L¹ mass ≤ 6C(c − 1).
- Mixed Robin finite part changes by ≤ K·W·(c − 1) under dilation, uniformly in shift a and finite-part window W; same after atom-mass normalization (divide by c).

## TheMixedRobinExpansionSurvivesActualOverlap
- mixedBumpRobin f g w = (bumpRobin(f + g) − bumpRobin(−f + g))/4 (polarization).
- Scalar: |levyEnergy f − ((log(1/w) + archRobinConstant)∫f² + bumpRobin f w)| ≤ (e^{1/2}/2)w∫f² for supp ⊂ [0, w], w ≤ 1.
- Mixed: |∫_{y>0} levyMixed f g − ((log(1/w) + κ)∫fg + mixedBumpRobin)| ≤ (e^{1/2}/4)w(∫f² + ∫g²), no separation assumption (coincident supports allowed; singular cross integral never split from diagonal cancellation).

## TheRobinFinitePartIsStableUnderLipschitzPerturbations
- Factor (f(u) − f(u+y))² − (g(u) − g(u+y))² = (increment of f − g)·(sum of increments): removes the 1/y singularity before integration.
- |bumpRobin f W − bumpRobin g W| ≤ W·L·(∫|f| + ∫|g|) where L = Lipschitz constant of f − g; mixed shifted version ≤ 2WL(∫|f| + ∫|g|), independent of displacement.

## TheSeparatedCrossTermIsContinuousInAbsoluteMass
- ∫|autocorr f − autocorr g| ≤ ∫|f − g|·(∫|f| + ∫|g|) (Fubini).
- Separated pair (w < s): atomCrossTerm g s = ∫ archLevyDensity(s + z)·autocorr g(z) dz; |cross f − cross g| ≤ archLevyDensity(s − w)·∫|f − g|·(∫|f| + ∫|g|) (density antitone), all signs retained.

## ExactHigherShellThresholds
- exteriorShellOverlap(N, k) = N(log(N + k) − log N). Horizon-N log window c/N contains a pair a ≤ N, b ≥ a + k iff exteriorShellOverlap(N, k) ≤ c (minimal log gap at a = N).
- k − k²/N ≤ exteriorShellOverlap(N, k) < k; → k. For c < k, eventually no successor gap ≥ k is eligible.

## ExactSuccessorShellWindows (uses OnlyTheBoundaryStarEntersAtTouching)
- Log windows are asymmetric additively: |log(a + r) − log a| < w ⇔ r < a(e^w − 1); |log(a − r) − log a| < w ⇔ r < a(1 − e^{−w}).
- firstExteriorOverlap N = N log((N+1)/N) ∈ (1 − 1/N, 1), → 1. An unequal integer pair with one endpoint ≤ N lies in window c/N iff firstExteriorOverlap N ≤ c (for N ≥ 2); for fixed c < 1 eventually none.
- Geometric eligibility only; the prime interaction also reads autocorrelation and Λ.

## DirectedPrimeRowsPreserveTheDefect (uses ALG TheArchimedeanCrossEnergyIsOneSided, SSHA TheRowsAtBoundedOverlap, RAPT BoundedPrimeDefectHasFiniteRamanujanApproximation)
- Directed Schur/Young: Σ|x_m||x_n|(V_mn + V_nm) ≤ Σ x_m²(outgoing row/t + t·incoming row) — independent costs per direction.
- |nonRatioForm| ≤ ∫g²·Σ x_m²(2(log 4 + 4)e^{3w/2}(e^w − 1)N/t + t·2e^{w/2}m(e^w − 1)(log m + w)): outgoing (upward) rows have bounded mass (Chebyshev), incoming (downward) rows carry log m weight.
- For w ≤ min(1, K/N): nonRatioUpConstant = 2(log 4 + 4)e^{5/2}, nonRatioDownConstant = 2e^{3/2}; |nonRatioForm| ≤ ∫g²(2tC_dK·poleDefect + (C_uK/t + tC_dK(2ψ + 1))Σx²). Downward log weight paid by sum_top_le_poleDefect_param (top-row log ≤ 2·poleDefect + 2ψΣx²).
- Infinitesimal relative bound: |nonRatioForm| ≤ ∫g²(ε·poleDefect + nonRatioRelativeCost(K, ε)Σx²), cost = 2C_uC_dK²/ε + (ε/2)(2ψ + 1) = 8(log 4 + 4)e⁴K²/ε + ….
- overlapPrimeEnergy g N x = log N·Σx² − primeSum(atomicTest)/∫g². Eventually (uniform in w ≤ min(1, K/N), compact g, x): ≥ poleDefect/2 + (γ − ¼ − cost(K, ¼))Σx². Bounded overlapPrimeEnergy on the unit sphere ⇒ uniform finite Ramanujan approximation (finite S independent of N, w, g).

## TheSignedArithmeticSourceKeepsAlmostAllTheDefect (uses ALG ThePoleIsInfinitesimalRelativeToThePrimeDefect)
- overlapArithmeticEnergy = overlapPrimeEnergy + 2(∫f e^{−u/2})(∫f e^{u/2})/∫g² (pole moments).
- arithmeticRelativeCost(K, ε) = ε/3 + nonRatioRelativeCost(K, ε/3) + poleRelativeCost(K, ε/3) − γ.
- Eventually, uniformly over 0 < w ≤ min(1, K/N), compact g, signed x: overlapArithmeticEnergy ≥ (1 − ε)·poleDefect − cost(K, ε)Σx². Sharp ratio counterterm, directed non-ratio rows, exact pole moments each spend ε/3 of the defect.

## TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap (uses SSHA TheGammaFormLocalizesAtAnOrderedCutoff, TheTiltedSplineKeepsAGammaReserveAtEveryOverlap, TheMarkovFormFailsInsideTheSeparatedRegime, RAPT TheArithmeticTailPaysForItsLogarithmicMass)
- Gamma payment (tilted unit spline, every fixed c > 0): ∃ a > 0, C: eventually log N·Σx² − (1 − a)poleDefect − CΣx² ≤ archForm/((c/N)∫spline²).
  Proof: macroscopic cutoff M = N/L (L > max(4c, 128e²c/δ)); prefix atoms separated (w ≤ spacing/2) keep unit self-energy log N·S₀ with defect cost δ/4; tail gets Fourier-band reserve δ log N·S₁ − bS; ordered prefix/tail Gamma interaction costs only 2πB·S (archForm_add_ge_of_ordered); tail logarithm paid by log_mul_tail_mass_le_defect at defect cost 1 + δ/4. Net defect coefficient 1 − δ/2.
- weilQuad(atomicTest)/∫g² = overlapArithmeticEnergy + archForm/∫g² − log N·Σx² (exact assembly).
- exists_tiltedUnitSpline_complete_defect_reserve: complete signed Weil form ≥ a·poleDefect − CΣx² at every fixed overlap c > 0, horizon-independent mass loss.
- exists_finite_ramanujan_complement_with_complete_margin: for every T, a finite conductor set S; unit packets orthogonal to all ramanujanPoleProfile m (m ∈ S) eventually have complete Weil energy > T. Every energy sublevel is confined to finitely many arithmetic conductors.

## TheNearGammaAndDownwardPrimeRowsCancel (uses RAPT TheNearAtomsHaveALogarithmicPairing, BSU SieveCoordinateSupNorm, RHTower CriticalGibbsPerronPolarization)
- nearRowRadius c = 2c·e^{2c}; nearRowIndices = j ≠ n with |log j − log n| ≤ 2c/N. Geometry: |j − n| ≤ radius, N ≤ radius·n and N ≤ radius·j (near pairs live in a fixed top fraction of the horizon); row cardinality ≤ 2·radius.
- Bounded numerators ⇒ Σ_n (Σ_{j near} F/√j)² ≤ 4 radius³K² (horizon independent).
- nearGammaDownwardCoefficient = normalized Gamma pair atomArchPair·c_m(j) − normalized autocorr·Σ_{d|j}Λ(d)c_m(j/d). Gamma near entry ≈ log(N/c)·autocorr (+K); downward convolution = log j·c_m(j) − jet. Shared logarithm cancels (|log(N/c) − log j| ≤ radius + |log c|) ⇒ coefficient ≤ (K + B + |log c|)φ(m) + jetBound(m).
- interiorDownwardPrimeRow (literal k·j ≤ N products, exact ratio lags removed) = Σ_j normalized autocorr·(Λ ∗ c_m)(j)/√j (grouping products).
- Normalized autocorr of atomDilate depends only on |s|/w.
- nearGammaDownwardRow = near Gamma row − literal interior downward prime row; squared norm bounded; / log N → 0; holds for tilted unit spline at every fixed c. Exterior products and upward rows are separate terms.

## TheWeightedAffinePrimeShellsHaveTheirSignedMean (uses RAPT TheNonRatioPrimeRowsSplitIntoDownwardAndUpward)
- Real-endpoint residue error: reading(⌊X⌋) − kappa log X − finitePart → 0.
- Abel summation on [0,1]: weighted reading Σ W(k/X)F(k)Λ(k)/k = W(1)·reading(⌊X⌋) − ∫₀¹ W'(u)reading(⌊Xu⌋). Flat W near 0: ∫₀¹ W/u = −∫ W' log u; weighted reading − kappa·∫₀¹W/u = W(1)E(X) − ∫W'(u)E(Xu) (log and finite part cancel exactly) → 0. Uniform over residue patterns, and over affine parameters n, b for c_q(kn + b) with mean c_q(n)c_q(b)/φ(q).
- reciprocalShellWeight φ a t = autocorr(a/t) (0 at t = 0): C², vanishes on |t| < a; ∫₀¹ W/t = ∫_a^1 autocorr(u)/u.
- affineRamanujanPrimeShell(q, n, b, φ, c, h, X) = Σ_{k≤X} Λ(k)/k·c_q(kn + b)·autocorr(hX/(ck)) → (c_q(n)c_q(b)/φ(q))·∫_{h/c}^1 autocorr/u uniformly in n, b (tilted spline included).
- affinePrimeShellCorrection(q, n, φ, c, X) = (2/∫φ²)Σ_{1≤h<⌈c⌉} affineRamanujanPrimeShell(q, n, h, φ, c, h, X) → c_q(n)·shellCorrection(φ, c, q) = c_q(n)(completeWeilAdjunctionEnergy − completedConductorEnergy), uniformly in n. The literal weighted prime source realizes the whole signed decrement from reference to completed conductor energy (finite shell family fixed by the overlap).

## TheFullDownwardPrimeRowCancelsTheNearGammaRow (uses RHTower ZetaNotchRampMainTerm)
- exteriorPrimeCutoff = ⌈N e^{c/N}⌉ ≤ N + exteriorPrimeStrip(c) (= ⌈c e^c⌉). Exterior products ℓ > N within c/N of a row n force n ≥ N − strip.
- horizonRamanujanMangoldt(m, N, ℓ) = Σ_{d|ℓ, ℓ/d ≤ N} Λ(d)c_m(ℓ/d); |·| ≤ φ(m) log ℓ (horizon divisor Mangoldt ≤ log ℓ); log ℓ/√ℓ ≤ 2.
- Literal infinite downward row (on c_m(j)/√j) = finite sum over ℓ ≤ cutoff of normalized kernel·horizonRamanujanMangoldt/√ℓ (product regrouping; vonMangoldtAtom·1/√j = Λ(k)/√(kj)).
- Full downward − interior = regrouped exterior row; |row| ≤ 2φ(m)·strip; supported on ≤ strip + 1 boundary rows; squared mass ≤ (strip + 1)(2φ(m)strip)², horizon independent; / log N → 0.
- Near Gamma minus the full infinite downward prime action on the conductor profile → 0 in log-normalized Euclidean norm, every fixed c > 0, every prime power and exterior product included; tilted spline instance.

## TheWeightedAffineShellErrorsVanishInHarmonicNorm (uses HTGeometry HarmonicQuotientSquareError)
- reflectedAffineShift(q, h) = qh − h represents −h mod q; c_q(qh − h) = c_q(h); c_q(T − h) = c_q(T + reflected shift).
- |affineRamanujanPrimeShell| ≤ φ(q)∫φ²·mertensSum⌊X⌋.
- Arbitrary fixed shell shifts (shift : ℕ → ℕ): affinePrimeShellCorrectionOfShift → c_q(n)·shellCorrectionOfShift uniformly in n; globally bounded error (Mertens sum below the horizon).
- Uniform real tail majorant (sup over X ≥ Y) + harmonic-quotient square error lemma: row error at X = N/n, divided by √n, has Σ_n err²/log N → 0. Uniform affine convergence upgrades to log-normalized Euclidean norm on the moving horizon N/n.
- Reflected shifts recover shellCorrection exactly (negative offsets mod conductor).

## TheUpwardPrimeRowsHaveUniformKernelBounds (uses RHTower CHMDCompactSourceClass, HTGeometry ArctanSinTaylor)
- Σ_{d|ℓ} Λ(d)²/d ≤ (log ℓ)². Divisor sparsity: Σ_n (Σ_{ℓ∈S, n|ℓ} Λ(ℓ/n)/√(ℓ/n)·F)² ≤ |S|K²Σ_{ℓ∈S}(log ℓ)².
- shellAutocorr is Lipschitz (compact C² source). |√x/√y − 1| ≤ |x − y|/y. Lipschitz G: |G(A log(1+x)) − G(Ax)| ≤ K|A|·2x² for |x| ≤ ½.
- Macroscopic strip (N ≤ Ax, Ay; |y − x| ≤ B; 2AB ≤ N): |√(x/y)·G((N/c)(log y − log x)) − G((N/c)(y − x)/x)| ≤ (4KA²B²/c + ABM)/N — log linearization + square-root Jacobian cost O(1/N).
- primeIndexBoundaryMass(B, Y) = Σ_{|k−Y|≤B} Λ(k)/k → 0 (Λ(k)/k → 0); products k·n within B of N have k within B + 1 of ⌊N/n⌋.
- |√n·upward row on c_m(j)/√j| ≤ φ(m)·2(log 4 + 4)e^{3w/2}(e^w − 1)N (bounded at fixed overlap).
- Off-diagonal row in a strip = positive offsets T + h plus negative offsets T − h (h ≤ B), horizon cutoffs kept. Nonzero integer log gap ≤ c/N forces N ≤ c e^c·T and N ≤ c e^c·j.
- exists_logPrimeKernel_linearization_bound: for |j − T| ≤ B, T ≠ j: |√(T/j)·autocorr((N/c)(log j − log T)) − autocorr((N/c)(j − T)/T)| ≤ C/N for N ≥ N₀ (both kernels vanish outside the macroscopic range; inside, O(1/N)).
- Upward products touching a horizon atom lie within exteriorPrimeStrip of it. upwardRamanujanRow_eq_offsets: literal infinite upward row = Σ_{k ≤ N + B} vonMangoldtAtom k Σ_{h ≤ B}(positive offset kn + h ≤ N, negative offset h < kn, kn − h ≤ N).

## TheUpwardPrimeRowsRealizeTheCompletedShellCorrection
- √n·(upward row on c_m(j)/√j)/∫g² = logarithmicUpwardCoefficient (1/∫φ²)Σ_k Λ(k)/k Σ_h [c_m(kn ± h)·√(kn)/√(kn ± h)·autocorr((N/c)log((kn ± h)/kn))] exactly.
- Log kernel → reciprocal-offset kernel autocorr((N/c)h/(kn)): error ≤ D·mertensSum(N + B)/N → 0.
- Cutoffs moved from kn ± h ≤ N to kn ≤ N with reflected shift (c_m(kn − h) = c_m(kn + mh − h)): differences only on the prime-index window |k − N/n| ≤ B + 1; cost ≤ 4Bφ(m)·primeIndexBoundaryMass(B, N/n) (→ 0). Small products kn ≤ h have zero kernel once N ≥ c.
- {k ≤ N + B : kn ≤ N} = [1, ⌊N/n⌋]: remaining source is positive + reflected affine shell readings at X = N/n.
- Shells h ≥ c contribute exactly zero (autocorr support); with B ≥ ⌈c⌉: reciprocal coefficient = ½(correctionOfShift id + correctionOfShift reflected) at X = N/n.
- Three errors (log-kernel linearization ~ (mertensSum(N+B)/N)²·harmonic N; cutoff boundary via harmonic-quotient lemma; shell mean via shifted residual) each vanish in Σ_n(·/√n)²/log N.
- actualUpwardRowError = literal infinite upward row on c_m(j)/√j minus shellCorrection(φ, c, m)·c_m(n)/√n: Σ err²/log N → 0 for every m ≥ 1, every fixed c > 0. The literal upward prime-power action realizes the completed shell correction on each conductor profile (tilted spline instance).

## TheCompleteWeilFormIsPositiveAtEveryFixedOverlap (uses RAPT TheCompleteWeilResidualIsTheUpwardDefect, MacroscopicOverlapTiltedSplineReserve)
- upwardPrimeVector(normalized conductor vector) − shellCorrection·vector = φ(m)^{−1/2}·normalized upward residual → 0.
- Complete Weil matrix residual: ‖A_N v_m − completedConductorEnergy(m)·v_m‖ → 0 — completed conductor energies are actual norm quasimode energies at every fixed c > 0.
- exists_tiltedUnitSpline_completeWeil_eigenvalue_floor: every fixed c > 0 has e > 0 with all complete Weil eigenvalues ≥ e eventually (reserve + quasimodes + positive conductor floor).
- eventually_tiltedUnitSpline_completeWeilMatrix_posDef; eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg: literal weilQuad of every atomic test ≥ 0 at every fixed overlap (horizon depends on c).

## TheCompleteWeilGroundStateIsThePole (uses RAPT ThePoleConductorMinimizesTheCompletedEnergy, TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum)
- completedEnergyFloor = completedConductorEnergy(1) (pole conductor minimizes).
- tiltedUnitSplineGroundGap(c) = (2/∫spline²)∫_{t>c} shellSpectrum > 0 separates every m > 1 from m = 1.
- Bounded spectral counts of the actual matrix = completed conductor counts (for T not an energy). Exactly one eigenvalue below E(1) + gap/2; bottom eigenvalue → E(1); the spectral projection onto that window captures the normalized pole vector (error² ≤ residual²/(gap/2)² → 0). Ground state of the complete Weil matrix is the pole.

## TheWeightedPrimeShellsAreUniformOnBoundedOverlap
- One horizon for all C¹ weights with common flatness a, |W(1)| ≤ B, |W'| ≤ D on [0,1], in full residue norm (Abel identity with per-class real errors).
- Reciprocal shell weights with a ∈ [a₀, A] (a₀ > 0) have uniform height (L·A + |autocorr 0|) and derivative (L·A/(a₀/2)²) bounds; W'(t) = autocorr'(a/t)(−a/t²).
- Uniform over c ∈ [1, K], h ≤ H, all n, b: affine shells → signed mean; full signed shell correction uniform over c ∈ [1, K], all shift families, all n (tilted spline instance).

## TheBoundedOverlapShellErrorsVanishUniformlyInNorm
- |affinePrimeShellCorrectionOfShift| ≤ 2φ(q)⌈K⌉·mertensSum⌊X⌋; error globally bounded over c ∈ [1, K], shifts, n.
- Indexed tail majorant ⇒ Σ_n shiftedReciprocalUpwardRowError²/log N ≤ ε eventually uniformly in c ∈ [1, K] and shift; normalized residual ≤ ε uniformly.

## TheActualUpwardSourceIsUniformOnBoundedOverlap
- exists_logPrimeKernel_uniform_overlap_bound: kernel linearization constant C uniform in c ∈ [1, K] (A = Ke^K + 2K + 1).
- Geometric error, cutoff boundary (primeIndexBoundaryMass monotone in B), and shell-mean errors each have one horizon over c ∈ [1, K] and strips B ≤ exteriorPrimeStrip K. eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap: literal infinite upward residual ≤ ε for all c ∈ [1, K] at one horizon (tilted spline instance).

## TheNearGammaDownwardCancellationIsUniformOnBoundedOverlap (uses RAPT TheCompleteWeilResidualIsTheUpwardDefect)
- nearRowRadius, exteriorPrimeStrip monotone in c. Near Gamma/downward coefficient bound E = (C + radius(K) + log K)φ(m) + jet(m) uniform for c ∈ [1, K].
- One horizon for c ∈ [1, K]: interior near residual, exterior downward vector (c ∈ (0, K]), full near-Gamma-minus-downward vector, and nearCenterVector (pole shift ≤ completeWeilPoleShift φ K) all ≤ ε in log-normalized norm.

## TheReplacementErrorsVanishUniformlyOnBoundedOverlap (uses RAPT TheReplacementErrorsVanishAtEveryOverlap)
- Generic: uniform squared bound C on r(c, N) ⇒ (log N)^{−1/2}·r ≤ ε uniformly for c ∈ (0, K].
- Two-pole error: ‖fullWeilPoleError·profile‖² ≤ 4(atomPoleMomentErrorConstant)²A²K⁴ (coefficient ≤ const·(c/N)², kernel sum ≤ N⁴).
- Separated cross error: ‖·profile‖² ≤ (36K₀AK²)² with K₀ = 152(∫|φ|)²/∫φ². Self error ≤ (e^{1/2}/2)K/N·‖v‖. Center matrix is exactly linear in c (completeWeilPoleShift φ c = c·shift(1)), so its residual scales from c = 1. All replacement errors vanish uniformly on c ∈ (0, K].

## BoundedOverlapKeepsACompleteWeilReserve (uses TMWP BoundedOverlap.dirichletPoly_highBand_mass, ACS, ArithmeticPositivityTheory factorialSpanGammaOffset)
- Tilted spline Fourier transform nonzero on reals ⇒ common floor m on [1, 101K]. High band: ∫_N^{101N}|FT(atomic test)|² ≥ 48(c/N)²mN·Σx² (Dirichlet polynomial high-band mass ∫_N^{101N}|D|² ≥ 48N Σx²).
- Uniform Gamma reserve: (a log N − b)Σx² ≤ archForm/((c/N)∫spline²) for all c ∈ [1, K], N ≥ 1 (a = 48m/(2π∫spline²), b = (factorialSpanGammaOffset + log 2)(1 + 2Ke^K)).
- Uniform Gamma payment, complete reserve (a·poleDefect − CΣx² ≤ normalized weilQuad), and matrix-coordinate reserve a‖x‖² + β·poleDefect ≤ completeWeilEnergy, all with one horizon for c ∈ [1, K].

## CompletedConductorQuasimodesAreUniformOnBoundedOverlap
- Complete Weil residual identity has eight source terms (prime matrix residual, self error, center, separated cross, pole error, full near-Gamma/downward, near center, upward). One horizon: ‖A v_m − E_c(m)v_m‖ ≤ ε for all c ∈ [1, K] (fixed m).

## OneHorizonMakesEveryBoundedOverlapPositive
- Uniform coordinate certificate: finite S; unit x with completeWeilEnergy ≤ T (c ∈ [1, K]) has Σ_{m∈S}⟨x, v_m⟩² ≥ 1/18.
- completedConductorEnergy(c, m) ≥ (2/∫spline²)∫_{t>K} shellSpectrum for all c ≤ K, all m (monotone Fourier tail).
- Spectral exclusion: any b below that tail floor bounds every eigenvalue for c ∈ [1, K] at one horizon.
- Endpoint: completedConductorEnergy(φ, 1, 1) = bumpRobin φ 1/∫φ² + completeWeilPoleShift φ 1 − log 2π; joined with touching uniformity (c ≤ 1).
- exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor K: one e > 0 and one horizon with all eigenvalues ≥ e for all 0 < c ≤ K (including arbitrarily small c and passage through touching). Hence PosDef, energy ≥ e‖x‖², and weilQuad(atomic test) ≥ 0 for every signed packet, uniformly in c ∈ (0, K]. K fixed; no unbounded overlap schedule.

## TheTiltedSplineHasAPolynomialConductorFloor (uses MacroscopicOverlapConductorFloor, BSU EffectiveTranslatedPairingAndMultiplicityDefect)
- tiltedSplineTailConstant = sinh(1)⁸/(64(1 + (3π/4)²)⁴). |FT tilted spline(r)| = (1/8)|FT splineProbe(r/8)|.
- shellSpectrum ≥ const/c⁸ on [c + 1, 2c + 1] ⇒ ∫_{t>c} shellSpectrum ≥ const/c⁷ (c ≥ 1); every completed conductor energy ≥ (2·const/∫spline²)/c⁷.

## EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap (uses SSHA EveryProfileWithoutRealFourierZerosKeepsAGammaReserve, RAPT TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy)
- Profile hypotheses only: C², support [0,1], FT(φ)(r) ≠ 0 for all real r. Gamma defect payment repeats the tilted-spline cutoff argument with exists_noRealZero_archForm_reserve.
- Complete defect reserve, positive Fourier tail at every c (FT has no real zeros ⇒ shellSpectrum > 0), conductor floor (2/∫φ²)∫_{t>c} shellSpectrum > 0, matrix-coordinate reserve.
- eventually_noRealZero_completeWeilMatrix_posDef: every C² profile on [0,1] whose Fourier transform has no real zeros has eventually positive definite complete Weil matrix at every fixed c > 0. Also exact low spectral counts (= completed conductor counts) and spectrum bottom → completedShellEnergy.

## FixedOverlapPositivityIsSelectiveAgainstTheLiouvilleTwin (uses TMWP LiouvilleTwinSelectivity, HTGeometry ExponentialDividedDifference)
- bumpRobin_le_of_nearPlateau: 0 ≤ g ≤ B on [0,1], g ≥ m₀ on [η, 1 − η], K-Lipschitz ⇒ bumpRobin g 1 ≤ KBa + (B² − m₀² + 2ηm₀²)log(1/a) + m₀²(1 − a) for 0 < a ≤ 1 (Lipschitz below a; plateau self-overlap above).
- boxPlateau w = ∫_{x−L}^{x+L} (four-fold box of half-width w), L = ½ − 4w; = 2L·(unif_L ⋆ box⁴); C², 0 ≤ · ≤ 1, = 1 on |x| < ½ − 8w, = 0 on |x| > ½, 1/w-Lipschitz. FT = 2L·Û_L·Û_w⁴ has no zeros off the real axis.
- tiltedBoxPlateau w τ u = e^{τu}·boxPlateau(u − ½): a nonzero tilt shifts FT argument to ξ − iτ ⇒ no real Fourier zeros. Lipschitz e^τ(1/w + τ); ∫(·)² ≥ 1 − 18w.
- liouvilleSelector: w = 1/1000, e^τ = 1001/1000. ∫φ² ≥ 491/500; bumpRobin/∫φ² ≤ 3/2 (a = 10⁻⁴); robinEulerThreshold = e^{β/‖φ‖²}/(2π) < 1 since e^{3/2} < 2π.
- liouvilleSelector_selective: for every fixed c > robinEulerThreshold (in particular every c ≥ 1), eventually: ζ's complete Weil form is strictly positive on every nonzero atomic family of width c/N, while the Liouville twin λΛ has a strictly negative complete form on some family of the same width.

## FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip (uses TMWP EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio)
- Same profile and overlap: ζ positive while every pole-free sign gauge ε (completely multiplicative ±1, bounded harmonic sums) has negative complete form on some atomic family. Every cofinite flip (all primes outside a finite set flipped; Liouville = empty set) is such a gauge. One profile at one bounded overlap separates ζ from infinitely many twins, none a finite flip.

## TheGammaReserveSurvivesGrowingOverlap (uses RAPT TheFlipThresholdGrowsLikeAPowerOfThePrime)
- splineBandFloor c = sinh⁸1/(64(1 + (101c/8)²)⁴) ≤ |FT spline|² on [c, 101c]; ≥ (sinh⁸1/(64·161⁴))/c⁸ for c ≥ 1.
- Band mass ∫_N^{101N}|FT f_x|² ≥ 48c²·floor/N·Σx²; Plancherel ≤ 2π∫f².
- Synthesized mass floor at growing overlap: ∫f_x² ≥ κc⁻⁷(c/N)‖φ‖²Σx² (κ = growingMassConstant) for all c ≥ 1, N ≥ 1 — adjacent atoms may cancel but the norm keeps a c⁻⁷ floor.
- Gamma reserve: archForm f_x ≥ (κc⁻⁷ log N − b·c)(c/N)‖φ‖²Σx² for 1 ≤ c ≤ N (b = growingReserveCost); per unit atom mass → ∞ along every schedule c_N⁸ = o(log N).

## PrimeResidueSourcesHaveQuantitativeLogDecay (uses RHTower PrimeProgressionPowerLog)
- residueMangoldtReading(q, F, X) = Σ_{n≤X} F(n mod q)Λ(n). Indicator kappa = 1/φ(q) on units, 0 otherwise. |reading(indicator a) − θ(X; q, a)| ≤ ψ(X) − θ(X); non-unit classes have θ ≤ θ(q).
- Fixed-modulus PNT (power-log): |reading(indicator r) − kappa·X| ≤ C·X·exp(−a(log X)^{1/10}) for all r incl. non-units/prime powers. Hence for every k: eventually |reading(F) − kappa(F)X| ≤ (X/(log Y)^k)Σ|F| for X ≥ Y, all signed F.

## ResidueMertensFinitePartsHaveLogarithmicRates (uses HTGeometry ReciprocalLogPowerTailGeneral)
- Exact Abel transport: E(Y) − E(X) = (R(Y) − κY)/Y − (R(X) − κX)/X + ∫_X^Y (R(t) − κt)/t² dt for residue Mertens remainders E.
- ∫_X^Y dt/(t log^{p+1} t) ≤ 1/(p log^p X). For every k: eventually |residue Mertens remainder E(X)| ≤ (2/log^k Y)Σ|F| for X ≥ Y, all signed patterns (limit Z → ∞ in the Abel transport).

## AffinePrimeShellsHavePolynomialGrowth
- Active prime indices in a shell satisfy k ≥ X/c (autocorr support) ⇒ |affine shell| ≤ (log 4 + 4)φ(q)∫φ²·c (Chebyshev ψ(X) ≤ (log 4 + 4)X).
- |affinePrimeShellCorrectionOfShift| ≤ 4(log 4 + 4)φ(q)c²; mean ≤ same; error ≤ 8(log 4 + 4)φ(q)c² globally (X ≥ 1, c ≥ 1).

## GrowingShellSourcesHaveLogarithmicRates
- Weighted Abel bound with movable flat neighbourhood: |weighted − mean| ≤ (2(B + D)/log^k Y)Σ|F| when Y ≤ X and Y ≤ X·a.
- Reciprocal shell weights for a ∈ [1/c, 1]: |W(1)| ≤ ∫φ², |W'| ≤ 4Lc² (flat on |u| < 1/(2c)).
- exists_affineShellCorrection_polynomial_log_rate: ∃ C, ∀ k, eventually: for all c ≥ 1, X ≥ 2cY, all shifts and n: |affine shell correction − mean| ≤ C·c³/log^k Y. Every inverse-log rate with cubic overlap cost.

## SmallWidthKeepsPrimeGeometryPolynomial
- For c/N ≤ 1: linearNearRowRadius c = 2c e² (linear in c), linearPrimeStrip c = ⌈c e⌉; near rows: |j − n| ≤ radius, N ≤ radius·n, radius·j; card ≤ 2·radius; squared near rows ≤ 4 radius³K²; exterior cutoff ≤ N + strip; exterior near products force n ≥ N − strip.
- Small width: nonzero integer log gap ≤ c/N forces N ≤ c·e·T and N ≤ c·e·j.

## NearGammaDownwardCancellationHasPolynomialGrowth
- c ≥ 1, c/N ≤ 1/3: near-Gamma/downward coefficient ≤ E·c (|log c| ≤ c; radius linear); interior squared row mass ≤ C·c⁵; exterior row ≤ 2φ(m)·linearStrip, strip ≤ (e + 1)c; exterior squared mass ≤ C·c³; full normalized near-Gamma-minus-downward ‖·‖² ≤ C·c⁵/log N; near center ‖·‖² ≤ C·c⁵/log N (2c ≤ N).

## UpwardKernelLinearizationHasPolynomialCost
- Kernel linearization at small width: |√(T/j)·autocorr((N/c)log(j/T)) − autocorr((N/c)(j − T)/T)| ≤ C·c²(B + 1)²/N for strip B with 2(e + 3)cB ≤ N.
- Summed logarithmic-vs-linearized upward coefficient error ≤ D·c²(B + 1)³·mertensSum(N + B)/N; mertensSum(N + B) ≤ (J + 2)log N for B ≤ N.
- (log N/N)² ≤ 4/√(log N). Normalized harmonic bound of the kernel-linearization error ≤ K·c⁴(B + 1)⁶/√(log N) (log N ≥ 1, c/N ≤ 1, B ≤ N, 2(e + 3)cB ≤ N).

## PrimeBoundaryErrorsHavePolynomialHarmonicBounds (uses HTGeometry HarmonicQuotientTailBound)
- primeIndexBoundaryMass(B, Y) ≤ 2B + 2 (Λ(k)/k ≤ 1); ≤ 8(B + 1)/√Y for Y ≥ 2B + 2. N/n < 2⌊N/n⌋.
- Split harmonic rows at N/n = 4(B + 1)(log N)²: cutoff-change error has normalized squared norm ≤ K(B + 1)⁶/√(log N), uniform in c ∈ (0, N].

## AffineShellErrorsHavePolynomialHarmonicBounds
- Source rate above quotient cutoff T = 2c·exp(√log N) (k = 2) + global polynomial bound below it ⇒ shifted reciprocal residual: Σ err²/log N ≤ K·c⁶/√(log N) eventually, for all c ≥ 1 and shifts (tilted spline instance).

## SmallWidthRealizesTheUpwardPrimeOffsets
- c/N ≤ 1: upward products within linearPrimeStrip c = ⌈ce⌉ of the row; exact offset reindexing and logarithmicUpwardCoefficient identity with strip linearPrimeStrip c.

## WeilReplacementErrorsHavePolynomialCost
- ‖A·normalized v‖² = ‖A·v‖²/log N. Pole and separated-cross replacements: fourth-power overlap cost after normalization; center scales linearly with charge; self remainder ~ width c/N.
- Explicit: pole error ‖·‖² ≤ C c⁴/log N (c ≤ N); separated cross ≤ C c⁴/log N; center residual ≤ C c²/log N (exact scaling); self ≤ C c²/N².

## CompletedConductorEnergiesHavePolynomialBounds (uses RAPT OverlapForcesNewRamanujanTerms)
- Zero multiplier (n = 0, c_m(0) = φ(m)) removes amplitude: |shellCorrection(φ, c, m)| ≤ 4(log 4 + 4)c².
- completeWeilAdjunctionEnergy = (selfFinitePart(1) + ramanujanAdjunctionEnergy(m) − γ) − log c + [m = 1]·poleShift(c), pole shift ≤ c. |completedConductorEnergy| ≤ C·c² (c ≥ 1).

## TheActualUpwardSourceHasPolynomialHarmonicBounds
- For c ≥ 1, 4(e + 3)²c² ≤ N: Σ actualUpwardRowError²/log N ≤ K·c¹⁰/√(log N) (kernel linearization c⁴(B+1)⁶, boundary (B+1)⁶, affine shells c⁶; B ≤ (e + 1)c).

## CompletedConductorQuasimodesHavePolynomialError (uses SAHT TheArithmeticResidualBudgetIsUniformInTheHorizon)
- Prime residual from the horizon-uniform arithmetic Hodge budget: ≤ C/log N.
- Eight-term residual: ‖A v_m − E_c(m)v_m‖² ≤ K·c¹⁰/√(log N) for c ≥ 1, 4(e + 3)²c² ≤ N (all poles, prime powers, cutoffs kept; tilted spline instance).

## FixedConductorPacketsStayPositiveAtGrowingOverlap (uses HTGeometry FiniteGramApproximationCertificate, SAHT GrowingRamanujanFamiliesHaveAUniformGramBudget, RAPT BoundedPrimeEnergyHasFiniteRamanujanCoordinates)
- Finite energy error: entry errors ≤ ε ⇒ |⟨A Σa_i v_i, Σa_i v_i⟩ − Σ E_i a_i²| ≤ |I|·ε·Σa².
- Normalized Ramanujan Gram error |⟨v_m, v_l⟩ − δ_ml| ≤ (1 + 2ml)/log N (harmonic − log ∈ [0, 1]).
- For 0 ≤ A < 1/48 and 1 ≤ c ≤ (log N)^A: c⁷·‖residual‖ ≤ ε (residual² ≤ Kc¹⁰/√log N, c²⁴ ≪ √log N); c⁷·(entry error) ≤ ε (energy ≤ Cc², Gram error ≤ G/log N).
- eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap: fixed finite conductor set S; one horizon; for all c ∈ [1, (log N)^A], A < 1/48: completeWeilEnergy(Σ a_m v_m) ≥ (tailConst/∫spline²)c⁻⁷Σa² > 0. Also for every power of the iterated log, c ≤ (log log N)^A (any A).

## ConductorScaleControlsTheCompletedEnergy
- First coprime tail term: completedConductorEnergy(c, m) ≥ (2/∫spline²)(m/φ(m))∫_{t>c/m} shellSpectrum.
- Floor (2·tailConst/∫spline²)(m/φ(m))·min(1, (m/c)⁷): seventh-power floor below the overlap scale (m ≤ c), constant floor for every m ≥ c (energy ≥ 2·tailConst/∫spline², using m/φ(m) ≥ 1).

## TheCompleteWeilReserveHasPolynomialOverlapCost
- atomicWeilForm + poleDefect ≤ (log N + log 4 + 4)Σx² (full defect at fixed counterterm, row bound).
- gammaPaymentCost(c, δ, L) explicit; Gamma payment with δ ≤ growingMassConstant/c⁷, L ≥ 4c, L ≥ 128e²c/δ.
- growingDefectFraction c = min(κ, ½)/c⁷; growingDefectCutoff c ≥ max(3, 4c, 128e²c/δ) ≤ H·c⁸.
- tiltedUnitSpline_complete_defect_reserve_explicit: for c ≥ 1, N ≥ cutoff(c): (δ(c)/4)·poleDefect − growingCompleteReserveCost(c)Σx² ≤ normalized weilQuad. Source: full defect counterterm, non-ratio and pole costs at ε = δ/8; Gamma payment from growing-overlap reserve.
- Costs polynomial: Gamma payment ≤ C c⁸, complete reserve cost ≤ C c⁹.
- exists_tiltedUnitSpline_complete_defect_reserve_polynomial: (a/c⁷)poleDefect − C c⁹ Σx² ≤ normalized weilQuad for all c ≥ 1, N ≥ H c⁸.
- Any unit vector with completeWeilEnergy ≤ 0 has poleDefect ≤ C c¹⁶ (N ≥ H c⁸).

## AffineShellErrorsHaveAUniformHarmonicBudget (uses HTGeometry HarmonicQuotientSquareBudget)
- Cutoff T = 2cY₀e^c; above it error ≤ C c²/(1 + log((N/T)/n)) (inverse-log² rate integrated); below it global D c². Σ shiftedReciprocalUpwardRowError² ≤ K c⁵ for all N ≥ 1, c ≥ 1, shifts — horizon-independent budget.

## UpwardPrimeErrorsRetainTheirHorizonDecay
- Kernel error keeps its 1/N factor; prime-index boundary rows: Σ(·/√n)² ≤ K(B + 1)⁵ at every horizon (global D b²/√n; for N/n ≥ 4b: ≤ D b²/√(N/n)).
- Boundary budget Σ ≤ 10D²(B + 1)⁵ (global rows only where N/n < 4b; harmonic quotient tail ≤ 1 + log(8b)).
- mertensSum(N + B) ≤ (log 4 + 6)log N (B ≤ N). Kernel linearization keeps decay: Σ/log N ≤ K c⁴(B+1)⁶(log N/N)².
- Two-rate upward residual: ‖normalized upward residual‖² ≤ K(c⁵/log N + c¹⁰(log N/N)²) for every N with log N ≥ 1, c ≥ 1, 4(e+3)²c² ≤ N (no eventual qualifier).

## CompleteConductorResidualsRetainTheirHorizonDecay (uses OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching, TheCompleteWeilReserveHasAnExplicitTouchingHorizon, RamanujanFamiliesHaveExplicitCoordinateMass, NegativeWeilPacketsHaveExponentialConductorCutoffs, RHTower Sieve.HarmonicLogBound)
- ‖v_m‖² ≤ 2(Σ_{j<m}|mode_m(j)|)² for log N ≥ 1 (periodic coefficient bound). Self error has explicit horizon (no conductor waiting time).
- Explicit-horizon complete residual: ‖A v_m − E_c(m)v_m‖² ≤ K(c⁵/log N + c¹⁰(log N/N)²) for all N ≥ 1, log N ≥ 1, c ≥ 1, 4(e+3)²c² ≤ N. (log t/t)² ≤ 1/log t.
- tiltedSplineConductorTailFloor c = (2/∫spline²)∫_{t>c} shellSpectrum > 0. Eigenvector coordinate: eigenvalue ≤ 0 and E ≥ e > 0 ⇒ ⟨x_i, v⟩² ≤ ‖Av − Ev‖²/e².
- exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_horizon: ∃ C, D, H; for every c ≥ 1 there are Q ≤ exp(D(Cc¹⁶ + 1)) + 2 and B > 0 such that every N with Q⁴ ≤ N, Hc⁸ ≤ N, 4(e+3)²c² ≤ N and log N ≥ max(1, 36B(c⁵ + c¹⁰)/floor(c)²) has PosDef complete Weil matrix. Mechanism: negative unit packet ⇒ defect ≤ Cc¹⁶ ⇒ exponential conductor cutoff R; coordinate mass ≥ 1/36 on conductors ≤ Q; each coordinate² ≤ residual²/floor² ⇒ contradiction.
- Touching residual identity (c ≤ 1): A v_m − completeWeilAdjunctionEnergy·v_m = −prime residual + self + center − cross + pole − nonRatio.
- Touching (0 < c ≤ 1): cross error ‖·‖² ≤ C/log N; non-ratio action ≤ D log(N+1)/N·‖v‖; every term ≤ C/log N ⇒ ‖A v_m − adjunctionEnergy·v_m‖² ≤ K/log N for N ≥ 2, log N ≥ 1, all c ∈ (0, 1].
- Touching conductor floor: tailFloor(1) ≤ completeWeilAdjunctionEnergy(c, m) for c ∈ (0,1], all m (pole minimal; others larger).
- exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_through_touching: explicit Q ≥ 2, B > 0: every N with Q⁴ ≤ N and log N ≥ max(1, 36B/tailFloor(1)²) has PosDef complete Weil matrix simultaneously for all c ∈ (0, 1]. Stated horizon, not eventual.

## CountingActiveShellsMakesTheAffineSourceLinear
- Σ_{1≤h<H}|autocorr(h/r)| ≤ r·∫φ² (only h < r active).
- Interchanging sums (fixed k: only h < ck/X active) cancels the 1/k weight: |affinePrimeShellCorrectionOfShift| ≤ 2(log 4 + 4)φ(q)c — linear in overlap (improves quadratic); mean ≤ same; error ≤ 4(log 4 + 4)φ(q)c, every X ≥ 1, c > 0.

## ReciprocalShellVariationControlsTheActualSource
- Abel transfer charges ∫₀¹|W'| (total variation) instead of sup|W'|.
- Reciprocal shell weights (0 < a ≤ 1): |W(1)| ≤ ∫φ², ∫₀¹|W'| ≤ 2L (∫_{a/2}^1 La/u² = L(2 − a)).
- exists_affineShellCorrection_linear_log_rate: error ≤ C·c/log^k Y for c ≥ 1, X ≥ 2cY (linear overlap cost, every inverse-log rate).
- Quadratic-log harmonic budget: Σ_n shiftedReciprocalUpwardRowError² ≤ K c²(1 + log c) for all N ≥ 1, c ≥ 1, shifts.

## GrowingConductorPrimeSourcesHaveUniformLogarithmicDecay (uses RHTower ConductorUniform.DirichletCharacterUniformSums)
- Conductor-uniform PNT: for q ≤ (log X)^A, every residue indicator (non-units/prime powers included): |reading − kappa·X| ≤ C X exp(−a(log X)^{1/10}); non-unit θ bounded via conductor theta bound.
- For every k: one horizon Y for all q ≤ (log Y)^A, all X ≥ Y, all signed patterns: error ≤ (X/log^k Y)Σ|F|.

## GrowingConductorMertensErrorsHaveUniformLogarithmicDecay
- Residue Mertens remainder ≤ (2/log^k Y)Σ|F| uniformly over q ≤ (log Y)^A, X ≥ Y.

## GrowingConductorsHaveUniformReciprocalShellRates
- Variation Abel bound uniform over growing conductor families. Raw shell error ≤ C·qφ(q)·c/log^k Y; extra log decay absorbs qφ(q) ≤ (log Y)^{2⌈A⌉}: error ≤ C·c/log^k Y uniformly over q ≤ (log Y)^A, c ≥ 1, X ≥ 2cY, shifts, n (tilted spline instance).

## NegativeWeilPacketsHaveExponentialConductorCutoffs (uses RAPT BoundedPrimeDefectHasAnExponentialConductorCutoff)
- For η > 0: ∃ C, D, H; every c ≥ 1 has R ≤ exp(D(Cc¹⁶ + 1)) such that every unit packet with completeWeilEnergy ≤ 0 at N ≥ Hc⁸ is η-approximated by Ramanujan profiles of conductors ≤ R (defect ≤ Cc¹⁶ ⇒ exponential conductor cutoff).
