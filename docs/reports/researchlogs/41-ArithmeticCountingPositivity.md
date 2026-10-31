# ArithmeticCountingPositivity — facts log

## HarmonicCorrelationPaysThePrimeGap (uses SMAP FullCorrelationKeepsTheMargin)
- harmonicCorrelation c_N(ω) = S_N(ω)/H_N. Harmonic variance of poleGauge y = |poleResidual y|².
- On the hyperplane x ⟂ b, ω² = 1: c_N²·|x|² ≤ harmonicVar(poleGauge(ωx)) (Cauchy–Schwarz with gaugeWitness); c_N² ≤ 1; the witness attains equality (sharpness of the projection inequality only).
- eventually_prime_gap_ge_squared_correlation: ∀ε ∃N₀ ∀N ≥ N₀, ∀ sign gauges ω (may depend on N), ∀ hyperplane x: P_N(ωx) ≤ (log N − γ − 2 log 2·c_N² + ε)|x|². Uniform over gauges; no limiting density needed (Robin–Euler ceiling + sharp Poincaré (2 log 2 − δ)Var ≤ D_N).

## SparsePrimeFlipsRetainPositiveGaps (uses RAPT PolarMatchingReadsTheDensityOfTheGauge)
- Harmonic mass of multiples of p in [1,N] = H_{⌊N/p⌋}/p.
- finiteFlip {p} (n) = (−1)^{v_p(n)}; squares to 1. c_N ≥ 1 − 2/p for all N ≥ 1.
- p ≥ 3: gap (2 log 2)(1 − 2/p)².
- finiteFlip {3} is a completely multiplicative sign gauge with ω(3) = −1, gap 2 log 2/9, and polar matching |gaugeMertensSum ω y − log y| ≤ log 4 + 4 + log 3 (same polar matching as untwisted source).
- Every a < 2 log 2: some prime flip p ≥ 3 has gap a with polar matching bound log 4 + 4 + 2 log p/(p−1). Gap thresholds below 2 log 2 plus multiplicativity plus polar matching do not select Λ.

## PrimeParityPairing
- parityMass ± = Σ(1 ± ω(n))/n (nonneg, monotone); + = H + S, − = H − S.
- Prime parity pairing (multiplication by p bijects positive to negative fibres): (H − S)_N = (H + S)_{⌊N/p⌋}/p.
- Boundary identity: (p+1)S_N − (p−1)H_N = parity⁺(N) − parity⁺(⌊N/p⌋) ∈ [0, 2(1 + log p)].
- c_N ≥ (p−1)/(p+1); |c_N − (p−1)/(p+1)| ≤ 2(1 + log p)/((p+1)H_N); c_N → (p−1)/(p+1).
- Every prime flip (incl. p = 2) has gap 2 log 2·((p−1)/(p+1))²; prime-2 flip gap 2 log 2/9, Liouville none.

## PrimeParityRamanujanCoordinates (uses BVI RamanujanLagCoefficientAndTotientQuotient)
- Multiplicative sign gauges: Σ_{d|n, n≤N} ω(n)/n = (ω(d)/d)·S_{⌊N/d⌋}(ω); divisor weight d cancels fibre cost.
- primeParityRamanujanSum(p,m,N) = Σ ω_p(n) c_m-coefficient(n)/n = Σ_{d|m} μ(m/d)ω_p(d) S_{⌊N/d⌋}(ω_p) (Möbius inversion of decimated parity counts).
- Decimation error: |S_{⌊N/d⌋}(ω_p) − ((p−1)/(p+1))H_N| ≤ 2(1 + log p)/(p+1) + ((p−1)/(p+1))(1 + log d); normalized decimated mean → (p−1)/(p+1).
- Normalized Ramanujan coordinate → ((p−1)/(p+1))·Σ_{d|m} μ(m/d)ω_p(d); = 0 for m ≥ 2 with p ∤ m.

## HarmonicParitySpectralCoordinates (uses RAPT TheSimplePrimeEigenlinesConvergeToRamanujanLines)
- primeParityHorizonVector (unit, entries ω_p(n)/√(nH_N)); harmonicRamanujanHorizonVector = Ramanujan horizon vector/√H_N; H_N/log N → 1.
- Harmonic-normalized Ramanujan vectors: norm² → 1, quasimode residual² → 0 at energy log N − E_m.
- ⟨parity, Ramanujan_m⟩ = primeParityRamanujanSum/H_N/√φ(m) → ((p−1)/(p+1))Σμ(m/d)ω_p(d)/√φ(m).
- Window projection onto eigenvalues within δ of log N − E_m: error² ≤ residual²/δ² → 0; norm² → 1.
- exists_primeParity_eigenline_coordinates: ∃δ: windows eventually contain one eigenvalue (simple eigenline), eigenvalue → E_m, and the squared parity coordinate on that eigenvector → (((p−1)/(p+1))Σ_{d|m}μ(m/d)ω_p(d)/√φ(m))² (orientation-free).

## FinitePrimeFlipsHavePositiveHarmonicDensity
- finiteFlipHarmonicDensity(F) = Π_{p∈F}(p−1)/(p+1) ∈ (0,1].
- Recurrence (adding p ∉ F): p·S_N(ω_{F∪p}) + S_{⌊N/p⌋}(ω_{F∪p}) = p·S_N(ω_F) − S_{⌊N/p⌋}(ω_F).
- Harmonic shell: 0 ≤ H_N − H_{⌊N/d⌋} ≤ 1 + log d.
- Bounded error: |S_N(ω_F) − dens(F)·H_N| ≤ K_F (induction on F with constant 3K + 2(1 + log p); strong induction on N; contraction by p ≥ 2).
- c_N(ω_F) → dens(F); gap 2 log 2·dens(F)².

## FinitePrimeExhaustionLosesUniformGaps (uses RAPT TheHorizonLawsHoldForProfilesOfBoundedVariation)
- primeFactors(n) ⊆ F ⇒ ω_F(n) = λ(n); flipping primes below Q agrees with Liouville on n < Q; stabilizes pointwise.
- Each stage: multiplicative sign gauge, positive gap, polar matching with constant log 4 + 4 + 2Σ_{p<Q} log p/(p−1).
- No positive g holds uniformly on a cofinal rectangle (Q ≥ Q₀, N ≥ N₀): choose Q > N, reduce to Liouville (no gap).

## NearMaximalGapsDoNotForceWeilPositivity (uses RHTower WeilConeUniquenessUnconditional)
- primeFlipWeight p n = ω_p(n)Λ(n), |·| = Λ.
- Prime flips are not fully Weil positive (cone uniqueness: weight must equal Λ at p); explicit C² compact negative test in the complete functional (Gamma and poles kept).
- ∀a < 2 log 2 ∃ prime flip: sign gauge, gap a, |weight| = Λ, polar matching, ¬WeilPositiveFull. Submaximal gap + multiplicativity + matching do not force the Weil sign.

## LargePrimeFlipsAttainTheMaximalGap (uses SMAP TheSelectiveMarginIsTwoLogTwo; RAPT box/ladder/smooth-rough machinery)
- Main theorem: for every prime p ≥ 11, finiteFlip {p} has hyperplane gap exactly 2 log 2 (IsGreatest). Maximal gap is not rigid.
- Twisted Poincaré: p ≥ 11, 0 < η ≤ 1: eventually, every z ⟂ flipped pole ω_p(n)/√n has D_N(z) ≥ (2 log 2 − η)|z|².
- Mechanism: two-scale decomposition of [1,N] into Q-smooth part a ≤ X and rough fibres b (Q > p). ω_p constant along rough fibres. Smooth box fibres over p-ladders {u p^i : i ≤ J}, p ∤ u; on a ladder ω_p = (−1)^i.
- Twisted Efron–Stein on the box (boxGap_mul_boxVar_add_le): boxEnergy ≥ g_J·boxVar + (log p·W_p(J) − g_J)·pFibreVar, g_J = boxGap ≤ 2 log 2, ladderMass W_p(J) = Σ_{i≤J} p^{−i} ∈ [1,2].
- Signed ladder: Σ(−1/p)^i ≥ c_p·W_p, c_p = (p−1)/(p+1); Σ p^{−i}((−1)^i − c_p)² ≤ (1 − c_p²)W_p.
- Flipped-pole pairing with mean-zero g: ⟨ω_p, g⟩² ≤ (1 − c_p²)W_p(Σ_{u≤X}1/u)·pFibreVar(g).
- Constraint data: Y = cH + B, cS = −A, c_pH ≤ S, A = G·P + Av + Ah (p-sector, variation, halo), errors (1+log X)³W/G and halo 2(walk + M·W)/log X.
- Assembly: rotation cost (1 − c_p²)/c_p² paid by ladder excess log p − 2 log 2; numeric condition 4p·2 log 2·(21/20)³ ≤ (15/16)(p−1)²(log p − 2 log 2) holds for p ≥ 11 (log 11 ≥ 2.35).
- Gap 2 log 2 then from Robin–Euler ceiling + twisted Poincaré.
- maximal_gap_does_not_select_the_source: for every P there is a prime p ≥ P: completely multiplicative sign gauge, ω(p) = −1, IsGreatest gap = 2 log 2, |ω_pΛ| = Λ, untwisted polar matching (log 4 + 4 + 2 log p/(p−1)), ¬WeilPositiveFull. The discrete margin at its maximum does not select ζ.

## SmallPrimeFlipsLieBelowTheMaximalGap (uses SMAP TheConductorTwoIsTheFirstExcitation)
- Squared parity coordinates: ground eigenline (m = 1) → c_p², conductor-p eigenline → 4c_p²/(p−1) (Σ_{d|p}μ(p/d)ω_p(d) = −2, φ(p) = p−1). E_p = γ + p log p/(p−1).
- Eigenpair necessary bound: a gap g of ω_p forces (γ + g − ε)(a² + b²) ≤ E_i b² + E_j a² on the plane of eigenvectors i,j meeting the parity constraint.
- Every gap of ω_p ≤ p log p/(p+3) (balance D c² = B(c² + w)).
- p < 11 (p ≤ 7): p log p/(p+3) ≤ (7/10) log 7 < 2 log 2 (7⁷ < 2²⁰). So small-prime flips have positive gap 2 log 2·c_p² but not 2 log 2.
- primeFlip_hasHyperplaneGap_two_mul_log_two_iff: ω_p has gap 2 log 2 ⇔ p ≥ 11 (exact cutoff 11).

## PrimeParityIsExhaustedByItsRamanujanTower (uses BVI NonMarkovianLagOperatorAlgebraAndPrimePowerRevival, RHTower SummableDivisorHarmonicMean)
- primeParityTowerProfile(p,K,n) = c_p + Σ_{k<K} 2c_p(−1)^{k+1}·sieveLagMultiplier(p^{k+1}, n); c_p + 2c_p/(p−1) = 1; 1 − c_p² = 4p/(p+1)².
- Tower profile = c_p(−1)^K on the fibre p^K | n, = ω_p(n) elsewhere; it is a literal finite sum of harmonic Ramanujan vectors (conductors 1, p, …, p^K) with coefficients 2c_p(−1)^{k+1}/√φ(p^{k+1}).
- Exact error² = ((1 + c_p²)H_{⌊N/p^K⌋} − 2c_p S_{⌊N/p^K⌋})/(p^K H_N) ≤ (4p/(p+1)²)/p^K uniformly in N ≥ 1; → that value as N → ∞.
- Coefficient mass c_p² + Σ_{k<K} coeff² = 1 − (4p/(p+1)²)/p^K → 1: prime-power Ramanujan modes exhaust parity; uniform exhaustion ∀ε ∃K ∀N.

## CofinitePrimeFlipsHaveZeroGap
- cofiniteFlip F = λ·ω_F (flips every prime outside F); completely multiplicative sign gauge; = −1 at primes p ∉ F.
- Reverse recurrence: p S_N(ω_{F∪p}^c) − S_{⌊N/p⌋} = p S_N(ω_F^c) + S_{⌊N/p⌋}(ω_F^c).
- |S_N(cofiniteFlip F)| ≤ 2/dens(F) for all N (base: |Σλ(n)/n| ≤ 2; induction balance p·(2/c_{F∪p}) = (p+1)(2/c_F) + 2/c_{F∪p}).
- Every cofinite flip has greatest gap exactly 0; harmonic correlation → 0.
- Harmonic squared distance from finite flip to Liouville = 2 − 2c_N(cofiniteFlip F); |· − 2| ≤ 4/(dens(F) H_N) → 2 for fixed F.
- Order of limits: horizon-first (fixed Q) → 2; cutoff-first (fixed N) → 0 (exact equality to λ below Q). Cofinite stages stabilize pointwise to 1 yet have zero gap.

## TheParityTowerHasAUniqueSecularRoot (uses RHTower ConstrainedProlateInfiniteSecular)
- primeParityTowerCoefficient: k = 0 ↦ c_p; k+1 ↦ 2c_p(−1)^{k+1}/√φ(p^{k+1}); squares 4c_p²/(p^k(p−1)); HasSum of squares = 1; all nonzero.
- primeParityTowerEnergy: 0 ↦ 0; k+1 ↦ (k+1) log p + log p/(p−1) = E_{p^{k+1}} − γ. Strictly increasing first two, tail ≥ E_2.
- Two-mode secular root (ground + conductor p) = p log p/(p+3).
- primeParitySecularRoot = infinite secular root; lies in (0, p log p/(p+3)) strictly (higher coefficients nonzero), annihilates the full secular series, below energy 1; unique zero in (0, E_1-level).

## FiniteReciprocalMassControlsTheHyperplane (uses HTGeometry HermitianSpectralWindowBounds)
- diagonal_hyperplane_nonneg_iff: −b x₀² + Σ w_i x_i² ≥ 0 on c x₀ + Σ a_i x_i = 0 ⇔ b Σ a_i²/w_i ≤ c² (one negative diagonal direction paid by a constraint iff reciprocal mass fits squared head coefficient).
- Packet bound: Σ_U a²/w ≤ Σ_S a²/w + (Σ_U a² − Σ_S a²)/η with gap η outside S.
- Strict failure ⇒ explicit negative vector on the hyperplane.
- Hermitian form: at energy t between ground (shifted) and the rest: t|x|² ≤ L|x|² − ⟨Ax,x⟩ on v^⊥ ⇔ (t − (L − λ_0))·Σ_{i≠0}⟨v,e_i⟩²/(L − λ_i − t) ≤ ⟨v,e_0⟩².
- Eventual packet sandwich with common limit ⇒ full limit.

## TheParityTowerDeterminesTheFiniteResolvent (uses THIM MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor)
- Tower coefficient = Möbius transform: c_p·Σ_{d|p^k}μ(p^k/d)ω_p(d)/√φ(p^k) (sum = 2(−1)^{k+1} for k ≥ 1).
- Each prime-power conductor p^k is realized by actual eigenline sequences: energy − γ → E_{p^k} − γ, squared parity coordinate → coefficient².
- Ground count: for 0 < s < 2 log 2, eventually exactly one eigenvalue below γ + s (conductor 1 only, by bottleneck).
- primeParityFiniteResolvent(p,N,s) = Σ_i ⟨parity, e_i⟩²/(E_i − γ − s). For 0 < s < 2 log 2 it converges to the infinite secular series Σ_k coeff_k²/(energy_k − s) (packet sandwich; tail controlled by unit mass and gap η = (2 log 2 − s)/2).
- Tower energies strictly increasing; every positive tower energy ≥ 2 log 2.

## TheParitySecularRootDeterminesTheGap (uses RAPT TheHorizonLawsHoldForProfilesOfBoundedVariation)
- Twisting by ω_p is an isometry between the harmonic hyperplane and parity^⊥.
- Between ground and rest: constrained bound (γ + s)|u|² ≤ log N|u|² − ⟨Au,u⟩ on parity^⊥ ⇔ finite resolvent(s) ≤ 0.
- Secular series strictly monotone on (0, E_1); negative below root, positive above.
- Exact greatest gap of ω_p = min(2 log 2, primeParitySecularRoot p); HasHyperplaneGap ω_p g ⇔ g ≤ that min.
- root < 2 log 2 ⇔ p < 11; for p < 11 the greatest gap is the secular root; every gap < p log p/(p+3) strictly.
- Root equation: Σ_k 4/(φ(p^{k+1})(E_{k+1} − root)) = 1/root.

## FinitePrimeFlipsHaveUnitConductorMass
- finiteFlipMobius F = ω_F * μ (multiplicative); = Σ_{d|m}μ(m/d)ω_F(d). On p^{k+1}: 2(−1)^{k+1} if p ∈ F, else 0. Square = Π_{p|m}(4 if p ∈ F else 0).
- spectralWeight(m) = mobius²/φ(m) = 4^{ω(m)}/φ(m) on F-factored m, 0 elsewhere; multiplicative; ladder sum at p ∈ F: 1 + 4p/(p−1)².
- Euler product: Σ over F-factored m = Π_{p∈F}(1 + 4p/(p−1)²).
- conductorCoefficient(m) = dens(F)·mobius(m)/√φ(m); Σ_m coeff² = 1 exactly (dens² · Π(1 + 4p/(p−1)²) = 1 since ((p−1)/(p+1))²(p+1)²/(p−1)² = 1).

## FinitePrimeCountsDetermineTheConductorCoordinates
- finiteFlipRamanujanSum F m N = Σ_{d|m}μ(m/d)ω_F(d)S_{⌊N/d⌋}(ω_F); normalized → dens(F)·mobius_F(m).
- finiteFlipHorizonVector (unit); ⟨flip, Ramanujan_m⟩ → conductorCoefficient(F,m).
- Isolated eigenline windows: squared flip coordinate on the actual eigenline of conductor m → coeff²; eigenline sequences realize energy E_m and mass coeff².

## FinitePrimeCountsDetermineTheFullResolvent
- finiteFlipSecular F s = −1/s + Σ_{m≥2} spectralWeight_F(m)/(E_m − γ − s); finite resolvent of the unit flip vector converges to dens(F)²·finiteFlipSecular(s) for 0 < s < 2 log 2 (packet sandwich, ground count one, conductor energies distinct by injectivity of E_m).
- Tail summable below 2 log 2 (all E_m − γ ≥ 2 log 2 for m ≥ 2). finiteFlipSecular strictly increasing on (0, 2 log 2).

## TheFinitePrimeSecularSignsDetermineTheGap
- Twist by ω_F is isometry harmonic hyperplane ↔ flip^⊥; constrained bound ⇔ finite resolvent ≤ 0.
- Classification: HasHyperplaneGap ω_F g ⇔ g ≤ 2 log 2 ∧ ∀s ∈ (0,g): finiteFlipSecular F s ≤ 0.
- finiteFlipGreatestGap = sSup of gaps; attained (IsGreatest); every g ≤ it is a gap.
- Bounds: 2 log 2·dens(F)² ≤ greatest gap ≤ 2 log 2; strictly positive.
- Monotonicity: F ⊆ G ⇒ spectralWeight_F ≤ spectralWeight_G, secular_F ≤ secular_G, greatest gap(G) ≤ greatest gap(F) (adding flipped primes cannot increase the gap).

## InteriorSecularRootsForceStrictPrimeGapDecrease
- finiteFlipSecular continuous on (0, 2 log 2) (locally uniform summable denominators).
- Submaximal greatest gap is a zero of the secular series; for s ∈ (0, 2 log 2): greatest gap = s ⇔ secular(s) = 0.
- F ⊊ G ⇒ secular_F < secular_G on (0, 2 log 2) (new prime p contributes spectralWeight 4/(p−1) > 0).
- F ⊊ G: gap(G) < gap(F) ⇔ gap(G) < 2 log 2 (equality only on the maximal plateau).

## PrimeTailExhaustionHasVanishingGreatestGaps (uses RAPT TheAdjunctionEnergySeparatesValuations)
- Σ 1/((M(n+2)+1) log(M(n+2)+1)) diverges (Cauchy condensation vs harmonic).
- M = B!: conductors B!(n+2)+1 have all prime factors > B (supported on the prime tail).
- Supported conductor m ≥ 2: weight/(E_m − γ − t) ≥ 1/(2m log m) (weight ≥ 1/m; E_m − γ − t ≤ 2 log m via tame different ≤ log m).
- Gap ≥ ε forces Σ_{m≥2} weight/(E_m − γ − t) ≤ 1/t; divergence ⇒ for every B some Q has gap(primes in (B,Q]) < ε. Greatest gap of tail flips (B, Q] → 0 as Q → ∞, though each stage is positive.
- Arbitrarily far primes ≥ 11, each individually maximal (gap 2 log 2), have joint flips with arbitrarily small positive greatest gap.

## OneDyadicProbeSelectsTheFinitePrimeSource
- dyadicPrimeToggle F toggles 2 ∈ F; ω_{toggle} = ω_2·ω_F.
- gap({2}) < 2 log 2.
- finiteFlip_two_gap_selection: among finite prime flips F: (gap(ω_F) has 2 log 2) ∧ (ω_2ω_F has gap ≥ gap({2})) ⇔ F = ∅. Two lower-bound conditions (maximal original gap + untwisted response to the prime-2 flip) select the untwisted finite-prime sign.

## ConductorMassBoundsGapLossAndProbePrecision
- Σ_m spectralWeight_F(m) = 1/dens(F)².
- F ⊆ G: secular_G(s) − secular_F(s) ≤ (1/dens(G)² − 1/dens(F)²)/(2 log 2 − s).
- Gap loss: (gap F − gap G)(2 log 2 − gap G) ≤ gap G·gap F·(1/dens(G)² − 1/dens(F)²); squared loss ≤ (2 log 2)²·(mass increment).
- Inserting prime p: mass increment = (4p/(p−1)²)/dens(F)² ≤ (16/p)/dens(F)²; (gap F − gap(F∪p))² ≤ 16(2 log 2)²/(p·dens(F)²) — remote primes change a fixed gap by O(p^{−1/2}).
- Dyadic calibration: gap{2} − gap{2,p} ≤ (16(2 log 2)²/(p·dens{2}²))/(2 log 2 − gap{2}) = O(1/p).
- For every B, ε: some prime p > B, p ≥ 11, individually maximal, with gap{2,p} ∈ (gap{2} − ε, gap{2}): the dyadic probe precision needed to exclude remote flips is unbounded.

## FinitePrimeConductorMomentsBoundTheGreatestGap (uses RAPT TheAdjunctionEnergySeparatesValuations)
- finiteFlipConductorEnergyMoment F = Σ_{p∈F} 4p log p/(p² − 1).
- Dual-number (TrivSqZeroExt) Euler product: Σ_m coeff²·(E_m − γ) = that moment exactly (local geometric first moments 4p(p+1) log p/(p−1)³).
- Nonempty F: dens(F) < 1.
- Weighted Cauchy–Schwarz on the tail mass A = 1 − dens² vs reciprocal and first moments: greatest gap ≤ dens²/(1 − dens²)·moment.

## PrimeTailGapsHaveAnInverseLogCubeBound (uses RHTower Sieve MertensSecond, MertensThird)
- Σ_{p≤Q}1/(p+1) ≥ S(Q) − 1 (Σ 1/(p(p−1)) ≤ 1); tail (B,Q]: ≥ log log Q − (c₂ + 1 + S(B)).
- log((p−1)/(p+1)) ≤ −2/(p+1) ⇒ dens(primes in (B,Q]) ≤ D_B/(log Q)², D_B = exp(2(c₂ + 1 + S(B))).
- Energy moment of tail ≤ (16/3)(log Q + c₁) (4p log p/(p²−1) ≤ (16/3) log p/p; Mertens first).
- Eventually: greatest gap of tail flips ≤ (64/3)D_B²/(log Q)³ (via gap ≤ dens²/(1−dens²)·moment ≤ 2dens²·moment).

## DivisibilityCountsControlInfinitePrimeFlips (uses RAPT TheMatchingCoefficientIsTheLogarithmicDensity)
- primeSetFlip P: completely multiplicative sign flipping exactly primes in P (possibly infinite); equals finiteFlip(P ∩ [1,N]) on n ≤ N.
- 1 − ω_F(n) ≤ 2·#{p ∈ F: p | n}; H_N − S_N(ω_F) ≤ 2H_N Σ_{p∈F}1/p; c_N(primeSetFlip P) ≥ 1 − 2Σ_{p∈P,p≤N}1/p uniformly in N.
- Cutoff error: harmonic squared distance between primeSetFlip P and its cutoff at Q ≤ 4·(reciprocal mass of P beyond Q), uniform in N.
- Infinite prime sets with Σ_{p∈P}1/p ≤ η exist (geometric growth p_n ≥ A·2^n).
- ∀a < 2 log 2 ∃ infinite prime set P: completely multiplicative sign gauge, ω(p) = −1 on P, gap a (via c_N ≥ 1 − 2η, gap 2 log 2(1 − 2η)²). No limit interchange needed.

## PrimeStrippingHasAnAdditiveHarmonicError (uses RHTower Sieve MertensSecond)
- Signed harmonic shell: |S_N(ω) − S_M(ω)| ≤ H_N − H_M for sign gauges.
- One-prime stripping (ω multiplicative, ω(p) = 1): |S_N(ω_p·ω) − c_p S_N(ω)| ≤ 2(1 + log p)/(p+1), uniform in N and ω.
- Finite set: |S_N(ω_F·ω) − dens(F) S_N(ω)| ≤ strippingCost(F) = Σ_{p∈F}2(1 + log p)/(p+1), uniform in N and residual pattern ω (ω = 1 on F).
- strippingCost ≤ 2(1 + 1/log 2)(log Q + c₁) for F ⊆ primes ≤ Q (Mertens first).

## EveryPrimePatternHasItsEulerProductHarmonicMean
- primeSetHarmonicDensity P = inf_Q dens(P ∩ [1,Q]) = Π_{p∈P}(p−1)/(p+1) (decreasing limit), ∈ [0,1].
- dens(F)(1 + Σ_{p∈F}1/p) ≤ 1; positive product ⇒ residual reciprocal tail beyond Q ≤ dens(cutoff Q)/dens(P) − 1.
- Every prime-sign pattern P: harmonic correlation → Euler product density (both the vanishing and positive cases; packet sandwich with stripping errors).
- Gap of primeSetFlip P ≥ 2 log 2·density(P)².

## PositiveEulerDensityIsExactlyHarmonicCutoffCompleteness
- Cutoff Q ≥ N: zero error. density(P \ [1,Q]) = density(P)/dens(cutoff Q).
- Exact squared cutoff error = 2(1 − c_N(residual pattern)); limit 2(1 − density(P)/dens(cutoff Q)).
- Finite cutoffs approximate the whole sign in eventual harmonic mean square ⇔ density(P) > 0; zero density ⇒ every fixed cutoff has limiting squared distance 2.

## InfinitePrimeCountsHaveAZeroOrUnitConductorMass
- primeSetMobius P m = Σ_{d|m}μ(m/d)ω_P(d) (stabilizes at cutoff Q ≥ m); spectralWeight = mobius²/φ; conductorCoefficient = density(P)·mobius/√φ.
- Finite cutoff weights ≤ infinite weights; positive density: Σ_m weight = 1/density² exactly.
- Σ weight summable ⇔ density(P) > 0 (zero density forces divergence).
- Σ_m coefficient² = 1 if density > 0, 0 if density = 0 (every coefficient zero).
- primeSetRamanujanSum normalized → density(P)·mobius(m) for every pattern and conductor.

## EveryPrimePatternHasActualConductorCoordinates
- primeSetHorizonVector P N = finite-cutoff flip vector (unit); inner product with Ramanujan_m = primeSetRamanujanSum/H_N/√φ(m) → conductorCoefficient(P,m) without any density hypothesis.
- Squared coordinate on the isolated actual eigenline of conductor m → coefficient²; eigenline sequences realize energy E_m and mass coefficient² for arbitrary prime support.

## PrimeCountsDetermineEveryBoundedSpectralMass (uses RAPT TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum)
- Regular adjunction thresholds T above any bound exist (no E_m = T; positive gap above sublevels).
- Bounded spectral mass (squared constraint mass on eigenvalues < T): at regular T → Σ_{E_m<T} coefficient²(P,m); exact eigenvalue count identifies selected eigenlines with the whole sublevel.
- density(P) = 0 ⇔ bounded spectral mass → 0 for every T (zero Euler density = escape from every bounded energy window).

## EveryPrimePatternHasItsFullArithmeticResolvent
- primeSetFiniteResolvent P N s = Σ_i ⟨ω_P vector, e_i⟩²/(E_i − γ − s); primeSetConductorResolvent P s = Σ_{m≥1} coeff(P,m)²/(E_m − γ − s) (summable on (0, 2 log 2) for every pattern).
- Mass escape lemma: unit mass, denominators bounded away from 0 by η, low-energy mass → 0 for every T ⇒ reciprocal reading → 0.
- For every prime pattern P (including zero density) and 0 < s < 2 log 2: finite resolvent → conductor resolvent (zero density: both 0 via escape; positive density: packet sandwich with unit mass).

## PositiveDensityTransfersTheExactCutoffGap
- primeSetSecular P s = −1/s + Σ_{m≥2} weight_P(m)/(E_m − γ − s); tail summable when density > 0; conductor resolvent = density²·secular; strictly increasing on (0, 2 log 2).
- Positive density: HasHyperplaneGap ω_P g ⇔ g ≤ 2 log 2 ∧ secular_P ≤ 0 on (0,g).
- Every pattern (any density) has an attained greatest gap primeSetGreatestGap (sup closed by ε in the definition); gaps = (−∞, greatest]; 2 log 2·density² ≤ greatest ≤ 2 log 2.
- Positive density: gap of ω_P ⇔ same gap for every finite cutoff; cutoff greatest gaps decrease to the infinite-pattern greatest gap.
