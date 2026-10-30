# BVI working log (mathematical facts)

Source: cat/04.txt (118526 lines, 368 files).
## PronicBezoutSplitAndPrimePowerIndecomposability (Pillar I)
- sieveSeq N c k = Σ_{d≤N, d|k} c(d) (defined here; = BSU sievedDivisorSum); centeredSieveSeq drops d = 1.
- Mixed multiplicative difference Δ^×_{d₁,d₂}F(m) = F(d₁d₂m) − F(d₁m) − F(d₂m) + F(m) annihilates log; single axis Δ^×_d log = log d.
- gcd(k,k+1) = 1 ⇒ divisor pairs (d₁|k, d₂|k+1) coprime, recovered from product (d₁ = gcd(n,k), d₂ = gcd(n,k+1)); (d₁,d₂) ↦ d₁d₂ bijection onto divisors of k(k+1) for N ≥ k+1. Coprime-multiplicative F: Σ_{n|k(k+1)}F(n) = s_N(F,k)s_N(F,k+1).
- Coprime d₁,d₂ ≥ 2 ⇒ d₁d₂ not a prime power ⇒ Λ(d₁d₂) = 0: centered successor products never see prime powers (4 excluded, 6 attained); Λ(k(k+1)) = 0 for k ≥ 2. (Fails in Beurling systems: gcd(k,k+1)=1 is the integer-specific input.)
## ReciprocalJumpKernelAndDilationLagSectors
- Reciprocal kernel Σ_{n=max(i,j)}^H 1/(n(n+1)) = 1/max(i,j) − 1/(H+1). Finite pronic energy of prefix sums = double jump pairing Σ_{i,j} f(i)g(j)K_H(i,j).
- Dilated Ramanujan primitives (pmRamanujanPrimitive r (n/p)): pronic pairing decomposes into Diophantine lag sectors h = pa − qb; gcd(p,q) and gcd(a,b) divide h; forbidden lags (gcd(p,q) ∤ h) vanish; successor sector h = 1 forces coprime p,q and coprime multipliers.
## DilationProfileIntegerJumpCoupling
- Continuous Hilbert dilation profile of the Route PM Ramanujan step vector at rational p/q = √p√q·Σ_n P_r(⌊n/p⌋)P_r(⌊n/q⌋)/(n(n+1)) (integer-cell Gram, P_r = Ramanujan primitive, bounded). Finite lag-sector truncation at H: error √(pq)B²/(H+1); quadratic horizon Q² (Q = max(p,q)) gives error B²/Q. Successor pair kernel = 1/(qb+1) − 1/(H+1).
## DilationJumpValuationClock
- Natural Ramanujan coefficient Re = ramanujanLagCoefficient r n; nonzero ⇔ r ≠ 0 ∧ clock(r) | n (clock = r/rad r). Pair amplitude nonzero ⇔ clock(r) | gcd(a,b). Nonzero pair at gap h ⇒ clock(r)·gcd(p,q) | h; other lag sectors vanish at every cutoff. Successor sector (h = 1) nonzero pointwise ⇔ r squarefree; nonsquarefree modes have zero successor contribution.
## RamanujanRadicalDilationReduction
- c_r(v n) = v·c_{rad r}(n) for v = clock(r) (φ(r) = v·φ(rad r)); full coefficient sequence = clock-dilated radical jump stream; primitives P_r(N) = v·P_{rad r}(⌊N/v⌋); dilation profile Φ_r(p/q) = v·Φ_{rad r}(p/q) exactly (Gram picks v² and scales vp, vq).
## DilationClockSectorBoundaryAndSuccessorTransport
- Sector transport: S_r(v h, H) = v S_s(h, ⌊H/v⌋) + v(1/(⌊H/v⌋+1) − v/(H+1))·M_s(h,⌊H/v⌋) (M = signed coefficient mass on fiber); boundary term vanishes at aligned horizon H = v(T+1) − 1. Kernel rescaling v²K_H(vi,vj) = vK_{H/v}(i,j) + v(1/(H/v+1) − v/(H+1)).
- Aligned transport: S_r(v, v(T+1)−1) = v·S_{rad r}(1, T): radical's successor sector survives at physical lag v = clock(r).
## DilationClockSuccessorSeedCoupling
- Least successor seed (pa = qb + 1, least a) at radical: resonance ≠ 0 ⇔ gcd(p,q) = 1 (even when r nonsquarefree). Clock-successor sector at H = v(pqs+1) − 1 approximated by v√(q/p)·seed with error v·s·φ(s)²/√(pq). Qualitative: no uniform lower bound, no control of other signed sectors.
## DilationClockRelativeGapAndSignedComplement
- Seed geometry: pa = qb+1 ⇒ q − 1 ≤ |p−q|·a (except p = q+1). |seed| ≤ φ(r)²|p−q|/(q−1). Clock-successor sector ≤ relative-gap term + inverse-scale term; profile ≈ signed complement (all other sectors at same horizon).
## DilationClockComplementPrimeSurvival
- For p < q ≤ 2p: total error ≤ 2vφ(s)²(q−p)/p + (B² + vsφ(s)²)/p. Using profile continuity at 1 and arbitrarily large prime pairs with ratio → 1 (exists_prime_pair_ratio_lt): ∃ primes p<q, arbitrarily large, with |clock sector| < G/(k+2), signed complement within G/(k+2) of diagonal Gram G > 0 (exists_prime_clock_complement_near_diagonal). Cofinal family only; no general signed-packet bound.
## DilationSuccessorFiberReciprocity
- gcd(p,r) = 1 ⇒ c_r(pa) = c_r(a). Diophantine jump pa = qb + h converts dilation coefficient pairs into additive lag correlation c_r(qb+h)c_r(qb). Complete residue correlation Σ_n c_r(n+h)c_r(n) = r·c_r(h) (character orthogonality); invariant under invertible affine sampling. Complete successor fiber Σ_t c_r(a+qt)c_r(b+pt) = r·μ(r) for p,q coprime to r (uniform in scales and seed).
## DilationSuccessorSectorHarmonicClassification
- Least seed parametrizes all positive successor solutions (a+qt, b+pt); seeds exist for coprime p,q > 1 (a ≤ q). Lag-one sector at H = pqT = Σ_{t<T} amplitude·(1/(p(a+qt)) − 1/(H+1)).
- Complete successor mass classified: Σ_t c_r(a+qt)c_r(b+pt) = r μ(r) if p,q both coprime to r, else 0 (determinant-one equation forces units in any surviving Fourier mode). successorSectorMean = μ(r)·[p,q ⊥ r].
- Sector = (mean/(pq))·H_K harmonic mode − boundary + remainder ≤ Σ_t |amp|/(p(a+qt)) (uniform). Adjacent scales (n+2, n+3) unconditional capstone.
## DilationSuccessorDigammaRenormalization
- Progression finite part: Σ_{k<N}1/(kL+d) − H_N/L → −(ψ(d/L) + γ)/L, error ≤ |d/L − 1|/(LN) (HTGeometry digamma anchor). Complete successor sector − (mean/(pq))·H_N → explicit digamma constant Σ_t amp·const − mean/(pq), rate O(1/N). Consecutive scales: unconditional limits.
## DilationSuccessorLeastSeedResonance
- Successor amplitudes bounded by φ(r)² (CGL). One block (H = pqr): p·S_1 = amp(seed)/a + error ≤ rφ(r)²/q. Normalized: √(pq)S_1 ≈ √(q/p)·seed resonance, error rφ(r)²/√(pq); noncoprime scales: sector empty. Profile ≈ seed + signed complement with uniform error O(1/min(p,q)) (dilation_profile_least_successor_seed_uniform). No estimate for the complement or for prime packets.
## QuotientDualOctaveReciprocityAndValuationSwitching (Pillar II)
- s_{N,μ}(k) = −Σ_{d|k, d>N}μ(d) (k ≥ 2). First octave k ∈ [N+1,2N]: s = −μ(k), s² = μ(k)², s(k)s(k+1) = μ(k)μ(k+1). LCM fibre F_{N,μ}(L) = μ(L) + μ(L)² ≥ 0 on first octave (0 at primes/odd squarefree/nonsquarefree, 2 at even-parity squarefree). Λ_N(k) = −Σ_{d≤N,d|k}μ(d)log d = Λ(k) + μ(k)log k on first octave (0 at primes).
- Second octave [2N+1,3N]: s = −μ(k) − 1_{2|k}μ(k/2); v₂(k) = 1 sector annihilated (s(2u) = 0, u odd), v₂ = 2 activated (s(4u) = μ(u)).
## BezoutSuccessorQuadraticFormAndDirichletEnergySplit (Pillar III)
- Dirichlet polarization: Σ_{k≤M}(Δs)² + 2Σs(k)s(k+1) = 2Σs² + s(M+1)² − s(1)².
- Bézout incidence count I(M;d₁,d₂) = #{k ≤ M: d₁|k, d₂|k+1}: zero unless coprime; Σs(k)s(k+1) = Σ_{d₁,d₂≤N}c(d₁)c(d₂)I(M;d₁,d₂). Hits separated by multiples of d₁d₂ (CRT) ⇒ I ≤ 1 when M ≤ d₁d₂. Super-horizon reach θ = 2: for √M ≤ d ≤ M with M < d(d+1): same-node count ⌊M/(d(d+1))⌋ = 0 while I(M;d,d+1) = 1 (k = d).
- Master synthesis (bezout_valuation_incidence_four_requirement_synthesis): Λ(k(k+1)) = 0, polarization, first-octave laws, θ=2 reach, log4/log6 separation, second-octave switching. (Structural identities; "requirements" refer to a design doc.)
## BezoutSelbergDiagonalCoercivityAndHalfDecorrelation (Pillar IV)
- Q_Bez(N,c) = Σ_{coprime d₁,d₂≤N}c(d₁)c(d₂)/(d₁d₂) = Σ_e μ(e)Y_{N,c}(e)² (same Selberg coordinates as Q_Sel = Σφ(e)Y²). Q_Sel − Q_Bez = Σ_{e≥2}(φ−μ)(e)Y² (e = 1 mode cancels). φ(p) − μ(p) = p; separates 4 (2) from 6 (1) where φ(4) = φ(6).
- 2μ(e) ≤ φ(e) for e ≥ 2 (equality only e = 6), φ − μ ≥ 1 ⇒ on ker P (harmonic sum 0): 2Q_Bez ≤ Q_Sel ("1/2-decorrelation") and Q_Sel ≤ 2(Q_Sel − Q_Bez) (coercivity).
- Q_Bez ≤ Q_Sel for every weight (φ − μ ≥ 1 on e ≥ 2).
## ChineseRemainderBezoutPeriodicityAndSawtoothDefect (Pillar V)
- CRT: for coprime d₁,d₂, k ↦ (k mod d₁, (k+1) mod d₂) bijects any window of length d₁d₂ onto residues ⇒ exactly one Bézout hit per period; I(M) = ⌊M/(d₁d₂)⌋ + {0,1}. Sawtooth defect δ_Bez = I − M/(d₁d₂) ∈ [−1,1] (0 for non-coprime).
- Σ_{k≤M}s(k)s(k+1) = M·Q_Bez + R_Bez, |R_Bez| ≤ (Σ|c|)² uniformly in M. Σs² = M·Q_Sel − signedLcmFractDefect (BSU).
- Master: Σ(Δs)² = 2MΣ_{e≥2}(φ−μ)(e)Y² − 2R_lcm − 2R_Bez + s(M+1)² − s(1)² (pole-free). On ker P: M·Q_Sel and Σs² ≤ Dirichlet energy + defects + s(1)².
## FermiCellJumpReciprocityAndPronicTailBridge (Pillar VI)
- Floor reciprocity Σ_{d≤N}c(d)⌊M/d⌋ = Σ_{k≤M}s_N(k). Fermi cell response on I_n = (1/(n+1),1/n] (measure 1/(n(n+1))): F(n) = 2Σ_{k≤n/2}s(k) − Σ_{k≤n}s(k). Jump F(n+1) − F(n) = 2·1_{2|n+1}s((n+1)/2) − s(n+1); consecutive boundaries never both activate the half-scale jump.
- Möbius sub-horizon: s_{N,μ}(m) = [m=1] for m ≤ N; prefix sum = 1. First octave n ∈ [N+1,2N]: F(n) = 1 + Σ_{N<k≤n}μ(k); jumps = μ(m); consecutive jump products = μ(m)μ(m+1); dilated Möbius Fermi combinator on cell I_n = −(1 + Σ_{N<k≤n}μ(k)); cell L² energy = (1 + Σμ)²/(n(n+1)) (first-octave Nyman tail = Mertens increments).
## SuccessorEnergyRigidityAndParityStability
- Y tail zero ⇔ c tail zero (triangular multiples transform). Q_Sel = Q_Bez ⇔ c = 0 on [2,N] (successor energy kernel = constants). Q_Sel = H² + V (V = sieveVariance = Σ_{e≥2}φY²); Q_Bez − H² = Σ_{e≥2}μY².
- Universal: −V ≤ Q_Bez − H² ≤ V/2; V ≤ 2(Q_Sel − Q_Bez) ≤ 4V. Q_Sel + Q_Bez − 2H² = Σ_{e≥3}(φ+μ)Y² (parity e = 2 mode removed); = 0 ⇔ c = 0 on [3,N] (max anticorrelation ⇔ parity-only); variance above parity ≤ 2×that defect.
## ExactSuccessorMomentRegionAndUniversalInequalities
- Ramanujan inverse prescribes arbitrary Selberg coordinates. Three-mode weights (modes 1, 2, 6): H = h, Q_Sel = h² + a² + 2b², Q_Bez = h² − a² + b². Exact joint moment region (N ≥ 6): (H,S,B) realizable ⇔ 2H² ≤ S + B ∧ 2B ≤ S + H². Universal α V + β C ≥ 0 ⇔ α − β ≥ 0 ∧ 2α + β ≥ 0 (cone −V ≤ C ≤ V/2 is exact).
## SixModeStabilityAndSharpQuarterDecorrelation
- e ≥ 2, e ≠ 6 ⇒ 4μ(e) ≤ φ(e) (totient ≤ 2 classification). Half-decorrelation defect V − 2(Q_Bez − H²) = Σ_{e≠6}(φ − 2μ)Y²; variance away from 6 ≤ 2·defect (factor 2 optimal); defect 0 ⇔ only modes 1, 6. 4(Q_Bez − H²) ≤ V + 2Y(6)². Idempotent removeSixMode (Ramanujan inverse) preserves H, deletes 2Y(6)² from Q_Sel and Y(6)² from Q_Bez; projected: 4C ≤ V, constant 1/4 sharp (mode 10: φ = 4, μ = 1). Period quadratic forms only, not finite-prefix discrepancies.
## ExactFinitePrefixDiscrepancyDualityAndReturnTimes
- Prefix discrepancy L(N,M,c) = Σ_{k≤M}s_N(k) − M·H = −sievedFractSum = Σ_{2≤e≤N} Re R_e(M)·Y(e) (R_e Ramanujan primitive). Dual energy A(N,M) = Σ_{e≥2} Re R_e(M)²/φ(e): L² ≤ V·A, attained by canonical zero-mean extremizer (V = L = A). Best universal constant K: N ≤ 1 ∨ A ≤ K. A = 0 ⇔ every d ≤ N divides M. No asymptotic bound on A asserted.
## SharpInitialPrefixObservabilityAndExactGramDeterminants
- Discrepancy increments = s_N(M+1) − H. Initial kernel: first T observations vanish ⇔ c = 0 on [2, min(T,N)] and tail harmonic mass Σ_{d>T}c(d)/d = 0. First N−1 prefixes determine all c(d), 2 ≤ d ≤ N (sharp: pair weight (n+1)δ_{n+1} − (n+2)δ_{n+2} invisible until M = n+1). Variance 0 ⇔ c = 0 on [2,N]. Any real prefix data realized by Möbius lift + harmonic endpoint correction (zero-harmonic).
- Observation matrix ⌊(i+1)/(j+2)⌋ − (i+1)/(j+2) has det (−1)^n/(n+1); factorizes as Ramanujan primitive matrix (det (−1)^n n!) × tail multiples matrix (det 1/(n+1)!); variance-dual Gram det (n!)²/Πφ(e+2). Exact finite; no uniform conditioning claim.
- Prefix Gram = R·diag(1/φ)·Rᵀ positive definite; diagonal = dual energy A(n+1, i+1).
## IntegralPrefixLatticeAndPrimePowerObstructions
- Integral Ramanujan primitive R_q(N) = Σ_{xy=q} x μ(y)⌊N/x⌋ ∈ ℤ. Integer prefix matrix (lengths 1..n, moduli 2..n+1) is unimodularly equivalent to diag(1,…,n) (Smith form; floor matrix det 1, divisor incidence det 1, shear/rotation). Integral interpolation solvable ⇔ i+1 | (F⁻¹y)_i; cokernel ≅ Π_{k≤n} ℤ/k, order n!. Mod m kernel size Π gcd(m,i+1); at p^a: p^{Σ_r⌊n/p^r⌋}; rank mod p = n − ⌊n/p⌋. Integrality for normalized amplitudes c(d)/d. Integer obstructions real-solvable. No analytic content.
## ReturnWindowTwoMomentKernelsAndSharpZeroBlocks
- At common return P (all d ≤ N divide P): discrepancy translates L(P+t) = L(t) and reflects L(P−t−1) = (H − Σc) − L(t). Window [P−a, P+b] zero ⇔ initial zeros up to max(b,a−1) and (a = 0 ∨ H = Σc). Positive radii: head zero + harmonic tail moment 0 + raw tail moment 0 (two-moment kernel). Centered 2N−3 window detects all nonconstant weights; 2N−4 window kernel = one final normalized second difference (n+2, −2(n+3), n+4) direction. Sharp horizon at arbitrary phases open.
## GcdOrbitProjectionAndExactTranslationPeriods
- Gcd projection: push normalized mass c(d)/d to gcd(d,h) = Selberg-orthogonal projection onto h-periodic signals; Y coords kept iff q | h; composition = projection to gcd(h,k); idempotent; preserves H; stride 1 keeps only harmonic mode. Periodic with period h ⇒ Y(q) = 0 for q ∤ h (DFT on factorial cycle).
- Exact period set: s_N(c,·) h-periodic ⇔ every active d (c(d) ≠ 0) divides h; least period = lcm of active divisors (signed cancellation never shortens the period). Gcd projection = literal orbit average over factorial cycle; Selberg-Pythagoras best approximation among stride-periodic weights.
## PrimeTailCalibrationAndMobiusDefect
- Terminal prime band N/2 < p ≤ N: Y(p) = c(p)/p, s_N(p) = c(1) + c(p), successor eigenvalue φ(p) − μ(p) = p. Successor reserve R = Q_Sel − Q_Bez ≥ Σ_{tail p}c(p)²/p. Sharp calibration t(1−t)c(1)²·Σ1/p ≤ (1−t)R + tΣ s_N(p)²/p, attained.
- Möbius: R_N(μ) ≥ Σ_{N/2<p≤N}1/p. Combined signed defect (LCM fract + Bézout sawtooth) of literal Möbius = M·R_N(μ) − 1 for 1 ≤ M ≤ N; at M = N ≥ #terminal primes − 1 ≥ (1/2)(n/log n) − 1 (N = 2n). ⇒ no eventual sublinear power bound C N^α (α<1) for the unrenormalized defect (not_eventually_moebiusCombinedPrefixDefect_le_rpow). Does not exclude estimates keeping cancellation with the diagonal main term.
## PowerSavingIncrementCriterion
- First-octave Fermi response − 1 = M(n) − M(N) (Mertens increments). Octave increment bounds C n^{1/2+δ} ∀δ ⇔ Mertens M(x) = O(x^{1/2+δ}) ∀δ (strong induction, geometric scale 3/4) ⇔ RH (mobiusFirstOctavePowerSaving_iff_riemannHypothesis, via RHTower Littlewood). Exact reformulation.
## DilatedCellScalingAndSecondOctaveFermiJumpBridge (Pillar IX)
- Fermi cell matrix dilation F(kd, n) = F(d, ⌊n/k⌋); dilated Möbius combinator on I_n = −F_{N/k,μ}(n/k). For n ≤ 2N the half-scale Möbius prefix = 1_{2k≤n}; dyadic resolvent cell threshold = 1_{k≤n} + Σ_j 2^j(Möbius prefix discrepancies).
- Second octave jumps: μ(m) − 1_{2|m}μ(m/2); four 2-adic sectors: odd μ(m); m = 2u: s = 0 but jump −2μ(u); m = 4u: jump μ(u); 8|m: 0. F_{N,μ}(n) = 1 + Σ_{N<k≤n}μ − Σ_{N<j≤n/2}μ on [N+1,3N]. Prefix Bézout correlation for M ≤ 2N concentrated on trans-horizon jumps = Σ_{N<m<M}μ(m)μ(m+1).
## PowerDampedPronicMultiplicativityAndRoutePMBridge (Pillar X, start)
- Power-damped Möbius μ(d)d^{−ε}: s_N = τ_ε(n) (pmPowerDampedDivisorCoeff) for n ≤ N; first octave s_N(k) = τ_ε(k) − μ(k)k^{−ε}; primes p ∈ (N,2N]: s_N(p) = 1. Power-damped Fermi source on I_n (n ≤ N) = −F_{N,c_ε}(n).
- τ_ε coprime-multiplicative ⇒ τ_ε(k)τ_ε(k+1) = τ_ε(k(k+1)) (pronic law); τ_ε(p^m) = 1 − p^{−ε}; τ_ε(4) − τ_ε(6) = (1−2^{−ε})3^{−ε} > 0. Discrete energy E_T = Σ A(n)²/(n(n+1)); pronic Abel identity Σ_{n≤T}A²/(n(n+1)) + A(T)²/(T+1) = A(1)² + Σ_{n<T}(A(n+1)² − A(n)²)/(n+1). riemannHypothesis_of_pmPowerDamped_pronic_abel_budget: cofinal ε → 0 bounded Abel sums ⇒ RH (conditional criterion, RHTower budget route; premise open).
## EndpointHaarCellDecompositionAndWitnessPronicTransfer (Pillar XI)
- Endpoint/repaired Haar prefixes of Route PM equal −F_{N,c_ε}(n) on sub-cutoff cells; cell L² energy F²/(n(n+1)). Dyadic resolvent recursion: R_k = D_k + 2R_{2k} (top term vanishes); singleCell(1,N) = D_1 + R_2. First tail cell I_{2M+1} at N = 2M: R_2 = 1 cancels the constant ⇒ singleCell = −μ(2M+1), energy μ(2M+1)²/pronic.
## SawtoothBezoutSuccessorGradientAndRouteFZZPBridge (Pillar XII, start)
- Centered sawtooth B̃₁(d,k) = {k/d} − (d−1)/(2d): step 1/d − 1_{d|k+1}. Weighted sum W = −Σc(d)B̃₁(d,k): ΔW = s_N(k+1) − H. On ker P: ΔW = s_N, Dirichlet energy of W = Σs². Bézout successor pair locks B̃₁(d₁,k) at min, B̃₁(d₂,k) at max ⇒ two-step product annihilates.
- Route FZZ-P centered sawtooth prefix = weighted centered sawtooth sum of the Ramanujan cofactor; gradient = BVI sieve − harmonic; pronic Abel identity. Master synthesis theorem packages identities (and RH criteria riemannHypothesis_of_pmPowerDamped_pronic_abel_budget / riemannHypothesis_of_cofinal_centeredSawtooth_budget — conditional, premises open).
## PredictableMartingaleDecompositionAndCovarianceCancellationBridge (Pillar XIII)
- A(n+1)² − A(n)² = (ΔA)² + 2ΔA·A(n). Pronic energy Σ A²/(n(n+1)) = compensated diagonal Σ(ΔA)²(1/(n+1) − 1/(T+1)) + 2·predictable martingale Σ ΔA(n)A(n)(1/(n+1) − 1/(T+1)). For Route PM (A_ε = centered τ_ε prefix, ΔA = τ̃_ε(n+1)): energy = covariance diagonal + 2·martingale; off-diagonal covariance = 2·martingale.
- If Fermi source ∈ L² (unconditional for ε ≥ 1/2): martingale/log N → −V_ε/2 where V_ε (divisor variance) has V_ε/ε → 1/2 (so normalized rate → −1/4 as ε → 0). RH criteria (conditional): cofinal bounded diagonal + 2·martingale ⇒ RH; harmonic version Σ τ̃²/m + 2·harmonic martingale bounded ⇒ RH. Reformulations of the Route PM budget.
## AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization (Pillar XIV)
- All octaves: F(2m+1) − F(2m) = −s(2m+1); F(2m+2) − F(2m+1) = 2s(m+1) − s(2m+2); second difference at odd cell = 2s(m+1) − Δs(2m+1); sibling polarization 2(F(2m)² + F(2m+1)²) = (F(2m)+F(2m+1))² + s(2m+1)².
- Sub-horizon damped: F(n) = 2A_ε(⌊n/2⌋) − A_ε(n) − (n mod 2)α_ε (α_ε = density = 1/ζ(1+ε)); even cells: drift cancels. Dyadic wavelet telescoping Σ_{j<K}2^j W A(n/2^j) = 2^K A(n/2^K) − A(n) reconstructs A from wavelets.
## RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation (Pillar XV)
- τ_ε depends only on rad(n): τ_ε(m^k) = τ_ε(m), τ_ε(dm) = τ_ε(m) for d|m; τ_ε(pm) = (p|m ? 1 : 1 − p^{−ε})τ_ε(m); 2τ_ε(m) − τ_ε(2m) = (2|m ? 1 : 1 + 2^{−ε})τ_ε(m). Sub-horizon Fermi jumps: odd steps −τ_ε(2m+1); even steps (2|m+1 ? 1 : 1+2^{−ε})τ_ε(m+1). Jump at 4: 1 − 2^{−ε}; at 6: (1+2^{−ε})(1−3^{−ε}).
## ModularGcdLcmMultiplicativityAndCenteredSuccessorCovariance (Pillar XVI, start)
- τ_ε(j)τ_ε(k) = τ_ε(jk)τ_ε(gcd) = τ_ε(lcm)τ_ε(gcd) for all j,k. Scaled successor: τ(dk)τ(d(k+1)) = τ(d·k(k+1))τ(d); odd two-step τ(2m+1)τ(2m+3) = τ(product); even two-step = (1−2^{−ε})τ(2m(m+1)). Centered τ̃ = τ − α: coprime products linearize τ̃(j)τ̃(k) = τ̃(jk) − α(τ̃(j)+τ̃(k)) + α(1−α); successor pair → τ̃(k(k+1)).
- Predecessor split of martingale increment τ̃(n+1)A(n) = τ̃(n+1)A(n−1) + τ̃(k(k+1)) − drift terms.
## SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance (Pillar XVII)
- d | n+1 ⇒ B̃₁(d,n) = +(d−1)/(2d), B̃₁(d,n+1) = −B̃₁(d,n): midpoint sum 0, square invariant, jump² + 2·jump·value = 0. Active (d|n+1)/inactive split of W: active flips sign; W(n+1)² − W(n)² = (s(n+1) − H)·(inactive midpoint sum): active self-energy cancels exactly.
- Route PM centered prefix A_ε − W_{N,c_ε} is affine on [0,N] (slope H_N(c_ε) − α_ε): divisor impulses cancel.
## ActiveSawtoothClosedFormAndShiftedExponentTotientBridge (Pillar XVIII)
- Active component at n: −½(s_N(c,n+1) − s_N(c/d, n+1)); at n+1: +½(…). Inactive drift = s_N(c/d, n+1) − H. c_ε(d)/d = c_{1+ε}(d) ⇒ s_N(c_ε/d) = τ_{1+ε} sub-horizon. τ_1(m) = φ(m)/m; τ_1(4) − τ_1(6) = 1/6.
## ActiveDeletedMartingaleAndShiftedEulerConvergence (Pillar XIX, start)
- Active-deleted identity: W(n+1)² − W(n)² = (s(n+1) − H)(s_{c/d}(n+1) − H) + 2(s(n+1) − H)·Inactive(n). For c_ε: diagonal τ_ε(n+1)² replaced by τ_ε·τ_{1+ε} (Euler factor gap (p^{−ε})²(p−1)/p³ ≤ 1/p², uniformly summable to ε = 0; prime deficit ≤ 4/p², sum → 0 as ε → 0). 0 ≤ τ_ε ≤ τ_{1+ε} ≤ 1 for ε ≥ 0.
- τ_ε·τ_{1+ε} = 1 ⋆ (damped Möbius with local weight p^{−ε} + p^{−1−ε} − p^{−1−2ε}); local gap = (unshifted gap)/p; prime deficit = p^{−ε}(1−p^{−ε})/(p(p−p^{−ε})) ∈ [0, 4/p²].
## ShiftedExponentAsymptoticDensityAndActiveMartingaleRate (Pillar XX)
- Cesàro mean of τ_ε τ_{1+ε} → shifted density = Π_p(1 − w_p/p) (Euler product); sandwich E[τ_ε²] ≤ shifted ≤ E[τ_ε] = α_ε. Ratio shifted/α_ε → 1 as ε → 0; shifted/ε → 1 (twice the rate 1/2 of E[τ_ε²]). Active martingale density (τ_ε(τ_{1+ε} − τ_ε)) = shifted − E[τ_ε²] ≥ 0, /ε → 1/2, equals divisor variance to first order ((density − V_ε)/ε → 0).
## HorizonFreeActiveDeletedEnergyAndShiftedCovariance (Pillar XXI)
- Horizon-free split A_ε(n) = active component −½(τ_ε − τ_{1+ε})(n+1) (≥ 0 for ε ≥ 0) + inactive residual. A(n+1)² − A(n)² = τ̃(n+1)(τ_{1+ε}(n+1) − α_ε) + 2τ̃(n+1)·Inactive(n). Energy = active-deleted diagonal + 2·inactive martingale.
- Shifted covariance C(ε) = E[τ_ε τ_{1+ε}] − α_ε α_{1+ε} > 0 (strict local factor inequality at every p). Active-deleted diagonal/log N → C(ε) (unconditional, ε > 0). If L² source (ε ≥ 1/2 unconditional): inactive martingale/log N → −C(ε)/2. RH criterion: cofinal bounded active-deleted diagonal + 2·inactive martingale ⇒ RH (conditional; reformulation).
## ShiftedExponentSmallDampingCovarianceRateAndActiveDrift (Pillar XXII, start)
- Active martingale /log N → (C(ε) − V_ε)/2 unconditionally for all ε > 0 (no L² hypothesis): the active piece is deterministic. α_1 = 1/ζ(2) ≤ 3/4 (p = 2 factor) ⇒ C(ε)/ε → 1 − 1/ζ(2) ≥ 1/4.
- Small-damping rates: active drift/ε → 1/4 − α_1/2; inactive drift/ε → −(1 − α_1)/2 (α_1 = 1/ζ(2)).
## BezoutPronicInteriorSawtoothAndPredecessorPeakSplit (Pillar XXIII)
- gcd(n,n+1) = 1 ⇒ moduli split three ways at step n: d|n (post-jump peak), d|n+1 (pre-jump trough), Bézout interior (neither); W = peak + trough + interior. Active pair = −½Δ(s − s_{c/d})(n), telescopes to terminal value. Route PM: A_ε(n) = Δ(active component)(n) + Bézout interior prefix; paired pre/post-jump active martingale terms cancel the centering density and produce τ_ε(n(n+1)).
## BezoutPronicTotientInteriorMartingaleSynthesis (Pillar XXIV)
- A(n+1)² − A(n)² = τ̃(n)τ̃(n+1) + τ̃(n+1)Δτ_{1+ε}(n) + 2τ̃(n+1)·Interior(n) (no diagonal square). Two-step midpoint: ½(A(n−1) + A(n+1)) = Interior(n) + ½Δτ_{1+ε}(n). Interior prefix − sawtooth interior sum is affine on [1,N]. Energy = active-deleted diagonal + 2·predecessor-peak martingale + 2·Bézout interior martingale; RH ⇐ cofinal bound of this sum (conditional reformulation of Route PM budget; same content).
## DiscretePrimitiveEnergyAndJordanComparison
- J₂(n) ≥ n·φ(n). Sharp facets for q ≥ 2: J₂ ≥ 5φ + 2μ (equality q ∈ {2,3}); J₂ ≥ 6φ + 4μ (q ∈ {3,4}); J₂ ≥ 6φ + 12μ (q ∈ {4,6}).
- Primitive energy = mean square of zero-mean successor primitive W on factorial cycle; 12E_prim = Franel gcd form − H² = Σ_{q≥2}J₂(q)Y(q)². Zero period mean uniquely selects W as primitive of s − H.
## SharpPrimitiveEnergySuccessorFrontier
- Exact frontier (N ≥ 6): min E_prim given (V, C) = max(5V+2C, 6V+4C, 6V+12C)/12; edges supported on {2,3}, {3,4}, {4,6}; attained by four-mode weights; realizable ⇔ V ≥ 0, −V ≤ C ≤ V/2. Prime modes: V = p−1, C = −1, E_prim = (p²−1)/12 ⇒ E_prim/V unbounded. Universal αV + βC + γE ≥ 0 ⇔ γ ≥ 0 ∧ 4α−4β+γ ≥ 0 ∧ 6α−3β+2γ ≥ 0 ∧ 2α+γ ≥ 0 ∧ 2α+β+2γ ≥ 0.
## CoprimalitySuccessorPredictorAndSquarefreeInformation
- Predictor K c(d) = μ(d)Σ_{d|m≤N}c(m)/φ(m); its signal = Σ_{m≤N, gcd(m,k)=1}c(m)/φ(m) (weighted coprimality response). Selberg multiplier μ(q)/φ(q): keeps exactly squarefree coordinates; range = squarefree-supported coefficients on [1,N].
## OptimalSuccessorPredictionAndExactPhaseLoss
- Complete-period pairings: mean s_c(k)s_b(k) = Σφ(q)Y_cY_b; mean s_c(k)s_b(k+1) = Σμ(q)Y_cY_b (CRT). One-step prediction error E(b) = mean (s_c(k+1) − s_b(k))² = phase loss + Q_Sel(b − Kc); predictor optimal and unique on [1,N]; minimal loss Σ(φ(q) − μ(q)²/φ(q))Y_c(q)². Zero error on cycle ⇔ exact prediction for all k.
## SharpSuccessorPhaseLossAndClosureClassification (start)
- Phase loss vanishes on modes 1, 2; for q ≥ 3 weight ∈ [¾φ(q), φ(q)]: (3/4)·(variance above parity) ≤ loss ≤ variance above parity; lower equality ⇔ modes {3,6}.
- Upper equality ⇔ squarefree coords above 2 vanish; loss 0 ⇔ c = 0 on [3,N]. Exact successor closure: ∃b, s_c(k+1) = s_b(k) ∀k ⇔ c supported on {1,2} (divisor sieves are not closed under +1 beyond parity). Constants 3/4 and 1 sharp (modes 3, 4).
## RamanujanLagCoefficientAndTotientQuotient
- Lag coefficient c_q(h) = Σ_{d|q} μ(q/d) d·1_{d|h} (Möbius inverse of CRT kernel: Σ_{q|g}c_q(h) = g·1_{g|h}); normalized c_q(h)/φ(q) = μ(q/g)/φ(q/g), g = gcd(q,h).
## ValuationVisibilityClockAndRamanujanSupport
- Clock(q) = q/rad(q) (valuations v_p(q) − 1). c_q(h) ≠ 0 ⇔ q ≠ 0 ∧ clock(q) | h (⇔ q/gcd(q,h) squarefree); first visible positive lag = clock; prime power p^{a+1}: clock p^a.
## TrueTranslationPredictionAndExactCompression (start)
- Complete-period lag pairing mean s_b(k)s_c(k+h) = Σ_q c_q(h)Y_b(q)Y_c(q) (Ramanujan diagonal). Translation predictor with multiplier c_q(h)/φ(q) minimizes shift prediction error; Pythagoras; lag 1 = coprimality predictor.
## ArithmeticLagSchedulesAndSharpRecoveryHorizon
- Lag observations at schedule H determine exactly the Selberg coords q with clock(q) | some h ∈ H; recovering schedules ⇔ every q ≤ N has clock(q) dividing some lag. Sharp consecutive horizon = max_{q≤N} clock(q); single-lag recovery ⇔ lcm of clocks | h. One-step prediction erases nonsquarefree modes forever (iterates) while true shifts recover them at their clock: iterating compression ≠ shifting.
## RenormalizedMobiusDefectAndFirstOctaveCancellation
- Renormalized defect D̃ = Σs(k)s(k+1) − Σs² = Σ s(k)Δs(k); 2D̃ = −Σ(Δs)² + s(M+1)² − s(1)²; step D̃(M+1) − D̃(M) = s(M+1)(s(M+2) − s(M+1)). At common return M (all d ≤ N | M, e.g. qN!) LCM and Bézout defects vanish: D̃ = −M·R_N.
- Möbius first octave (N ≤ M ≤ 2N−1): combined defect = M R_N(μ) − 1 + Σ_{N<k≤M}(μ(k)μ(k+1) − μ(k)²); increments ∈ [−2μ², 0] ⇒ renormalized Möbius defect antitone and ≤ 0 on first octave; linear law M R_N − 1 is an upper bound on [1, 2N−1].
## JordanUpperBoundAndGcdOrbitPrimitiveEnergy (start)
- J₂(n) ≤ n²φ(n); 4J₂(n) ≤ 3n²φ(n) for n ≥ 2 (equality n = 2) ⇒ 16E_prim ≤ N²V (equality N = 2).
- Gcd projection Γ_h restricts all four diagonals (V, C, R, 12E_prim) to modes q | h with simultaneous Pythagoras (contracts V, R, E). Cutoff-free stride bound 16E_prim(Γ_h c) ≤ h²V(Γ_h c) ≤ h²V(c); parity orbit h = 2: 4E = V, C = −V, R = 2V. Intrinsic: 16E_prim ≤ (least period)²·V.
## PowerDampedRenormalizedDefectAndPronicCeiling
- 2 | k(k+1) ⇒ τ_ε(k(k+1)) = (1 − 2^{−ε})·Π_{odd p | k(k+1)}(1 − p^{−ε}) ≤ 1 − 2^{−ε}: consecutive products τ_ε(k)τ_ε(k+1) ≤ 1 − 2^{−ε} (2-adic Bézout ceiling).
- Sub-horizon (M+1 ≤ N): D̃(c_ε) = Σ τ_ε(k(k+1)) − Σ τ_ε(k)²; 2D̃ = −Σ(Δτ_ε)² + (τ_ε(M+1)² − 1) ≤ 0 for ε ≥ 0 ⇒ combined defect ≤ M·R_N(c_ε). Synthesis theorem packages these.
## IteratedSuccessorPredictionAndReservePhaseLossSplit
- Predictor K keeps Y(1), flips Y(2) (K² = id on modes 1,2). Conservation: V(Kc) + loss(c) = V(c) (also Q_Sel and above-parity variance) ⇒ K is a 1/4-contraction on variance above parity; K^m contracts by 4^{−m}.
- Against reserve above parity R₃ = Σ_{q≥3}(φ−μ)Y²: ½R₃ ≤ loss ≤ (3/2)R₃ ≤ (3/2)R; lower equality only mode 3, upper only mode 6 (splits the {3,6} degeneracy).
## PostStepInactivePrefixAndSixDivisibilityPronicDefect (start)
- Post-step inactive prefix A_ε(m) + active(m) ∈ [A_ε(m), A_ε(m) + 1/2]; its increment = ½(τ̃(n) + τ̃(n+1)) + ½Δτ_{1+ε}(n) (two-point smoothing). τ_ε(m) = τ_ε(d)·Π_{p|m, p∤d}(1 − p^{−ε}) for d | m ⇒ antitone in divisibility (ε ≥ 0); supermultiplicative τ(a)τ(b) ≤ τ(ab).
- 6-adic ceilings: 3 | k or k+1 ⇒ τ_ε(k)τ_ε(k+1) ≤ τ_ε(6) = (1−2^{−ε})(1−3^{−ε}); always τ_ε(k)τ_ε(k+1)τ_ε(k+2) ≤ τ_ε(6).
## PostStepInactiveEnergyAndPronicGradientConservation (Pillar XXVI)
- Linear pronic Abel: Σ B(n)/(n(n+1)) + B(T)/(T+1) = B(1) + Σ ΔB(n)/(n+1); Σ 1/(n(n+1)) = 1 − 1/(T+1). Active component² pronic sum ∈ [0, 1/4].
- Post-step inactive energy and Route PM energy are equivalent within factor 2 + 1/2 ⇒ RH criterion (conditional) on post-step energy.
- Conservation: (Δτ_ε)² + 2τ_ε(n(n+1)) = τ_ε(n)² + τ_ε(n+1)²; sum: 2Στ_ε(k(k+1)) + Σ(Δτ_ε)² = 2Στ_ε² + τ_ε(N+1)² − 1 ⇒ boundary-free Σ τ_ε(pronic) ≤ Σ τ_ε², Σ(Δτ_ε)² ≤ 2Στ_ε² (ε ≥ 0). Centered version and parallelogram law for two-point average.
## ActivePairMartingaleDissipationAndShiftedTotientReduction (Pillar XXVII, start)
- −X(n+1)ΔX(n) = −½Δ(X²) − ½(ΔX)²: compensated sum ≤ ½X(1)²(1 − 1/(T+1)). Writing τ̃(n+1) = −2S(n+1) + (τ_{1+ε}(n+1) − α), active + predecessor-peak martingale = −ΣS²/pronic − Σ(ΔS)²·w + Σ(τ_{1+ε} − α)ΔS·w ≤ the shifted-totient term (self-interaction purely dissipative).
- Covariance diagonal = compensated centered pronic sum + ½ compensated gradient² + O(1) boundary/pronic terms.
## SummationByPartsActivePairAndUncenteredShiftedReduction (Pillar XXVIII)
- Compensated summation by parts for X(n+1)ΔY. Centering drift −α Σ S/pronic ≤ 0 ⇒ active-pair martingale ≤ Σ τ_{1+ε}(n+1)ΔS·w (uncentered). 0 ≤ τ_ε S ≤ ½τ_ε(1−τ_ε) ≤ 1/8; Σ τ̃S/pronic ≤ 1/8. Active-pair = Σ τ̃S/pronic + ¼Σ(τ_ε² − 1)/pronic − ¼Σ(Δτ_ε)²w + ½Σ(τ_ε τ_{1+ε}(n) − τ_{1+ε}(n)τ_ε(n+1))w ≤ 1/8 + ½·(shifted difference sum). α_ε eliminated entirely.
## GeneralRadicalMultiplicativeAndGcdLcmValuationAlgebra (Pillar XXIX)
- IsGcdLcmModular F: F(1) = 1, F(j)F(k) = F(lcm)F(gcd). ⇒ coprime-multiplicative, F(k)F(k+1) = F(k(k+1)), F(k)F(k+h) = F(k(k+h)) for gcd(k,h) = 1, conservation (ΔF)² + 2F(pronic) = F(n)² + F(n+1)², summed form.
- radicalPrimeProd w n = Π_{p|n}(1 − w(p)) is GCD–LCM modular for every w; τ_ε (w = p^{−ε}), φ(n)/n (w = 1/p). For w ∈ [0,1]: values in [0,1], antitone in divisibility, supermultiplicative, F(k(k+1)) ≤ 1 − w(2), three-step ≤ (1−w(2))(1−w(3)).
## ThreeStepPrimorialBezoutAndEvenCubicCeiling (Pillar XXX)
- gcd(k, k+2) = gcd(k,2); k(k+2) coprime to k+1; k even ⇒ 24 | k(k+1)(k+2). F(k)F(k+1)F(k+2) = (2|k ? 1 − w(2) : 1)·F(k(k+1)(k+2)); even start ≤ (1−w(2))²(1−w(3)) (sharp at k = 2); odd start sharp at k = 1.
## UniversalSawtoothInteriorMartingaleAndPostStepCalculus (Pillar XXXI)
- For every N, c, n (no sub-horizon restriction): W(n+1)² − W(n)² = (s(n)−H)(s(n+1)−H) + (s(n+1)−H)Δs_{c/d}(n) + 2(s(n+1)−H)·Interior(n) (diagonal-free); pronic Abel version; Interior(n) + ½Δs_{c/d}(n) = ½(W(n−1) + W(n+1)). Post-step inactive sawtooth increment = two-point average of (s − H) + ½Δs_{c/d}. Active-pair compensated martingale ≤ −(harmonic-divided cross-sum), boundary-free since active(1,1) = 0 for every c.
## DedekindPsiJordanTotientAndFiveFormSpectralSynthesis (Pillar XXXII, start)
- Five modal weights in Selberg coordinates: φ (variance), μ (successor covariance), φ − μ (reserve), φ − μ²/φ (phase loss), J₂ (12E_prim). ψ = J₂/φ (Dedekind psi), ψ(p^{k+1}) = p^k(p+1); at primes ψ = φ − 2μ, J₂ = (φ − μ)² − 1. At (4,6): φ equal (2), all other weights separate (μ: 0/1; φ−μ: 2/1; loss: 2/(3/2); J₂: 12/24; ψ: 6/12).
- (q+1)φ(q) ≤ J₂(q) for q ≥ 2 (equality at primes) ⇒ 3V + V_{≥3} ≤ 12E_prim (equality N = 3), 3V + loss ≤ 12E_prim.
- Phase loss splits under gcd projection; master five-form synthesis: chain ¾V_{≥3} ≤ loss ≤ V_{≥3}; ½V ≤ R ≤ 2V; 3V + loss ≤ 3V + V_{≥3} ≤ 12E_prim ≤ (3/4)N²V... (16E ≤ N²V).
## SelbergHilbertCoordinateEquivalence
- Coefficient space on [1,N] with norm² = complete-period mean square of s_N = Q_Sel; √φ(q)·Y(q) is an explicit Hilbert isometry onto Euclidean space, inverse = Ramanujan inversion. Lag predictor acts diagonally with eigenvalue c_q(h)/φ(q) (compression, not translation).
## WittSelbergReceiverCoordinates
- Real Big-Witt ghost coordinates (RHTower Deninger) transported into Selberg coordinates via Ramanujan inversion (wittSieveReceiver): Y(q) = ghost_q; norm² = Σφ(q)ghost_q²; Frobenius 2 reads ghost(2q) at cutoff 2N; Verschiebung m: Y(q) = m·Y(q/m) if m|q. Native lag compression multiplies ghosts by c_q(h)/φ(q). Coordinate bridge only.
## NonMarkovianLagOperatorAlgebraAndPrimePowerRevival (start)
- Lag multiplier at p^{a+1}: 1 if p^{a+1}|h; −1/(p−1) if p^a ∥ h; 0 if p^a ∤ h. Coprime multiplicative in q. Compressed translation is self-adjoint, commuting, but not a semigroup: defect M(h₁+h₂) − M(h₁)M(h₂); prime-power revival: sub-clock lags h₁, h₂ (erased) with h₁ + h₂ = p^a revive the mode with defect −1/(p−1).
- Lag table at h₁ = h₂ = 1: defect 0 at q = 1, 2; −3/4 at q = 3, 6; −1 at q = 4. ‖defect operator c‖² = Σφ(q)·defect²·Y(q)².
## ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing
- Interior(n) = W(n) + ½Δ(s_c − s_{c/d})(n). ΔInterior(n) = ½((s(n)−H) + (s(n+2)−H)) − ½Δ²s_{c/d}(n): middle impulse cancels; multiplied by middle impulse gives average of two lag-1 pronic covariances (no diagonal, no lag-2 term). Same for Route PM interior prefix. 2(s(n+1)−H)·Interior(n) = Δ(Interior²) − (ΔInterior)² − Interior·Δ²(s_c − s_{c/d}).
- Three-step interior: moduli dividing none of n, n+1, n+2; d | n and d | n+2 ⇒ d | 2; d | n+2, d ∤ n ⇒ d ∤ n+1.
## ShortHorizonPronicDiscrepancyAndVonMangoldtDuality (start)
- Σ_{M≥1} D_N(M,c)/(M(M+1)) = −Σ_{e=2}^N Λ(e)Y(e) (unconditional, finite sum of convergent series Σ Re R_e(M)/(M(M+1)) = −Λ(e)). Pure mode q: −Λ(q) (0 at q = 6, −log p at prime powers). Pronic weight turns Selberg coordinates into the von Mangoldt functional.
- Prime mode: Re R_p(M) = −(M mod p), (Re R_p)²/φ(p) ≤ p − 1; dual energy bounded uniformly in M by a period-free ceiling; short-horizon L² discrepancy ≤ H·V·ceiling; pronic-weighted ≤ (1 − 1/(H+1))·V·ceiling; infinite pronic squared series = Ramanujan-primitive Gram form on Y.
- Non-prime-power mode probe: pronic discrepancy series = 0. Gram recurrence (p ∤ q): G(pq,pq) = (p−1)G(q,q) − 2G(pq,q); flat probe u = v on {q, pq} gives p·u²G(q,q); for non-prime-power q, G(pq,q) → −G(q,q) as p → ∞.
## TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity
- k-tuple H, residue counts ν_H(d,r), collision energy C_H(d) = Σν² = #{(i,j): H_i ≡ H_j mod d} ≥ k, = k iff pairwise incongruent. S_p(H) = pC_H(p) − k² = Σ_{i,j}(p·1[H_i≡H_j] − 1); pS_p = Σ_r(pν_r − k)² ≥ 0; S_p = 0 iff equidistributed; pairwise distinct ⇒ S_p = k(p − k).
- Admissible at p (omits a class r₀): (p−1)((p−1)S_p − k²) = pΣ_{r≠r₀}((p−1)ν_r − k)² ⇒ S_p ≥ k²/φ(p), equality iff uniform on the other p−1 classes. k < p ⇒ admissible. (0,1) at p = 3: S_3 = 2, normalized 1/2 (the 1/2-decorrelation floor is the k = 2 case).
- radicalPrimeProd: F(n)F(n+h) = F(n(n+h))F(gcd(n,h)); ≤ F(gcd(n,h)).
- Prime-power structure factor S_{p^{a+1}}(H) = p^a(pC(p^{a+1}) − C(p^a)); pairwise distinct mod p^a ⇒ S = kφ(p^{a+1}).
## TranslatedWindowStrideAnnihilationAndLcmReturnObservability
- Prefix reconstruction stability: |Δa| ≤ ε on [1,d] ⇒ |c(d) − b(d)| ≤ 2τ(d)ε (2 ≤ d ≤ n, cutoff n+1).
- At visibility clock h_q = q/rad q: q/gcd = rad q (squarefree), |λ_q(h_q)| = 1/φ(rad q); mode stability φ(q)(ΔY(q))² ≤ φ(rad q)²·Q_Sel(Δ predictor).
- Discrepancy D_N(·,c) is periodic mod lcm(1..N) (log = ψ(N) ~ N, not log N!). Any phase A: D = 0 on [A, A + lcm + N] ⇔ V = 0.
- Window [A+1, A+2N−4]: every d ≤ N−2 has two multiples; central single-hit of d = N−1 has both ±d neighbours inside for d ≤ N−3; lcm(d₁,d₂) ≥ K ⇒ ≤ 1 common multiple in a length-K window. Arbitrary-phase 2N−3 horizon proved only at N = 3, 4 (case split mod 6, 12).
## MultiLagBezoutLayerHierarchyAndFourStepInteriorCalculus
- Sawtooth after a multiple: B̃_d(m + r) = −(d − (2r+1))/(2d) for d | m, r < d; before: B̃_d(n) = (d − (2r−1))/(2d) if d | n + r, 1 ≤ r ≤ d. r-th symmetric shell {n+1−r, n+r} has width 2r−1 and vanishes at odd midpoint d = 2r−1.
- Bézout interior (d ∤ n, d ∤ n+1) is supported on d ≥ 3; d ≥ 3 dividing n−1 or n+2 lies in it automatically; d | n−1 and d | n+2 ⇒ d = 3 where B̃ = 0.
- Two-layer decomposition: W(n) = [first layer {n, n+1}] + [L₂(n−1) − L₂(n+2)] + four-step interior (d dividing none of n−1..n+2), L₂(m) = ½Σ_{3≤d|m}(c(d) − 3c(d)/d). Second layer is a 3-step difference; telescopes to boundary terms. Multiplied by impulse at n+1: right endpoint lag 1, left endpoint lag 2 (lag transfer).
## InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget (start)
- Route PM: τ̃_ε(n+1) = Δ²S_ε(n) + ΔI_ε(n). 2τ̃_ε(n+1)I_ε(n) = Δ(I² + 2IΔS)(n) − (ΔI)² − 2ΔS(n+1)ΔI(n): cumulative prefix fully absorbed into a total difference plus non-positive gradient and a local impulse product. I² + 2IΔS = A² − (ΔS)².
- Compensated SBP: 2·InteriorMartingale(T) = pronic series of potential − boundary − gradient energy − 2·local impulse cross-sum.
- Renormalized budget identity: Energy = [diag − vH_T] + 2[pair − κH_T] + 2[interior + (v/2 + κ)H_T] (H_T = compensated harmonic sum). Small-damping rates v₀ = ½, κ₀ = ¼ − A/2 (A = Artin) ⇒ interior must cancel at rate (1 − A)/2 ≥ 7/24. RH criterion: three bracket bounds cofinally ⇒ RH (conditional reformulation of the Route PM budget).
## TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation
- Σ_{k≥0} 1/((H+1+k)(H+2+k)) = 1/(H+1); bounded g ⇒ |Σ_{M≤H} g/pronic − Σ_∞| ≤ B/(H+1).
- Finite horizon: |Σ_{M≤H} Re R_q(M)/(M(M+1)) + Λ(q)| ≤ bound(q)/(H+1); |Σ_{M≤H} D/(pronic) + ΣΛ(e)Y(e)| ≤ √(V·ceiling)/(H+1); pure mode error √(φ(q)·ceiling)/(H+1); non-prime-power modes decay at that rate. Pointwise |D_N(M,c)| ≤ √(V·ceiling(N)) (period-free).
- Truncated Gram form = Σ_{M≤H} D²/pronic: PSD, monotone in H, within V·ceiling/(H+1) of the full form; prime-dilation recurrence defect O(1/(H+1)). Avoids lcm(1..N) = e^{(1+o(1))N} averaging.
## CofinalMobiusGradientCoercivityAndRenormalizedDefect (start)
- |s_N(μ)(n)| ≤ τ(n) uniformly in N. Each odd squarefree in (N, 2N] selects a distinct adjacent edge ending at a multiple of 4 with gradient² = 1 ⇒ accumulated gradient energy ≥ #odd squarefree in (N,2N] for M ≥ 2N; with density 4/π² and subpower divisor bound: for fixed A ≥ 2, eventually R_N(M) ≤ −N/(2π²) uniformly on 2N ≤ M ≤ N^A (signed coercivity for the literal Möbius source; no upper bound on gradient energy asserted).
- Polarization incl. empty prefix: 2R_N(M,c) + Σ_{k≤M}(Δs)² = s(M+1)² − s(1)². Möbius: |2R + E| ≤ τ(M+1)² + 1 ≤ C_r (M+1)^{1/(r+1)} for every r (uniform in N); positive part of R ≤ τ(M+1)²/2.
- Edge map: odd squarefree k ∈ (N,2N] ↦ k−1 (k ≡ 1 mod 4) or k (k ≡ 3 mod 4); s_N(μ) vanishes at multiples of 4 in the first octave, s² = μ² = 1 at k ⇒ unit-gradient edges, injective. Budget: 2R + #oddSqf + 1 ≤ τ(endpoint)². Odd squarefree density in (N,2N] → (6/π²)(2/3)·... (count/N → 4/π²). Eventually E_N(M) ≥ (2/π²)N for all M ≥ 2N; R_N(M) ≤ −N/(2π²) for 2N ≤ M ≤ N^{r+2}.
## CofinalLinearWindowMobiusEnergyAndDefectBounds
- Complementary quotient compression: |s_N(μ)(k)| ≤ B for k ≤ (B+1)N (N,B ≥ 1) ⇒ E_N(M) ≤ 4B²M, |R_N(M)| ≤ 2B²M when M+1 ≤ (B+1)N.
- Fixed linear window 2N ≤ M ≤ AN: eventually (2/π²)N ≤ E ≤ 4A³N and −2A³N ≤ R ≤ −N/(2π²). Order Θ(N) settled; not uniform as A → ∞.
## UniformCofinalMobiusPrefixDiscrepancy (start)
- Σ_{k≤M} s_N(μ)(k) = 1 − Σ_{q≤B} Σ_{N<d≤M/q} μ(d) for M ≤ (B+1)N; |·| ≤ 1 + 2B·mertensSup((B+1)N), sublinear in N for fixed B (unconditional PNT-level Mertens o(x) from PNTPlus). Harmonic Σμ(n)/n → 0. |D_N(M,μ)| ≤ N for all M. ⇒ for every ε: eventually |D_N(M,μ)| ≤ εM uniformly in M ≥ N (signed first-moment cancellation, no rate).
- Joint cofinal: ∀ε ∃K: N, M ≥ K ⇒ |D_N(M,μ)| ≤ εM and |Σ_{k≤M} s_N(μ)(k)| ≤ εM (below cutoff, prefix = 1 exactly).
## CoprimeSquarefreeDensityAndMobiusDilationMeans
- Density of squarefree n coprime to squarefree Q: (6/π²)Π_{p|Q} p/(p+1). Prime deletion: count_Q(N) = count_{pQ}(N) + count_{pQ}(N/p); "plus" recurrence turned into contracting "minus" recurrence by eliminating one scale; base: squarefree count error ≤ 2√x + O(1).
- μ(an)μ(bn) = μ(a)μ(b)·1[(ab,n)=1]μ(n)²; mean of μ(an)μ(bn) for coprime a,b → μ(a)μ(b)·density(ab).
## CofinalMobiusQuadraticQuotientProfile (start)
- s_N(μ)(k) = 1[k=1] − Σ_{q≤B} μ(k/q)1[q|k, qN<k] for k ≤ (B+1)N. Q_N(M) = Σ_{k≤M} s² = 1 + Σ_{q,r≤B}[pair prefixes of μ((r/g)n)μ((q/g)n) between max(q,r)N/lcm and M/lcm].
- Q_N((B+1)N)/N → profile(B) = Σ_{q,r≤B} ((B+1−max(q,r))/lcm(q,r))·μ(r/g)μ(q/g)·density((qr)/g²); monotone, 0 at B = 0, 6/π² at B = 1; fixed B only.
- profile(B) ≥ 6/π² for B ≥ 1 (monotone via energy monotone in horizon).
## CoprimeMobiusCancellationAndOddDilationMeans
- Coprime-restricted Möbius mean → 0 for every Q (prime deletion minus-recurrence + bounded contraction, base = unconditional Mertens o(x); Q = 0 only the unit). Π_i μ(a_i n) = Πμ(a_i)·1[(Πa_i, n)=1]μ(n)^{#i}; odd product ⇒ Πμ(a_i)·coprime-Möbius(n) ⇒ every fixed odd dilation product has mean 0 (no coprimality/squarefree assumptions on a_i).
## CoprimeMobiusSignAndEvenDilationMeans
- Coprime squarefree density depends only on rad Q, positive. Each Möbius sign among n coprime to Q has density density(Q)/2 (also at rational scales A N/d). Every even dilation product has mean Πμ(a_i)·density(Πa_i) (overlaps allowed, zero multipliers give 0).
## CofinalMobiusOddMomentsAndQuotientProducts (start)
- Tuple product of quotient band terms supported on lcm(q)-multiples above max(q)·N; reindexes to a dilation product Π μ((L/q_i)n) between max·N/L and M/L. ⇒ for fixed B, r: (1/N)Σ_{k≤(B+1)N} s_N(μ)(k)^{2r+1} → 0 (odd moments vanish; unit contributes 1/N).
## CofinalMobiusAllMomentProfiles
- Every fixed moment of s_N(μ) on horizon (B+2)N, /N, has an explicit limit: m = 0 → B+2; odd → 0; even 2r+2 → Σ_{q∈[1,B+1]^{2r+2}} ((B+2 − max q)/lcm q)·Πμ(L/q_i)·density(ΠL/q_i). Moment profiles alone do not give value frequencies.
## CofinalMobiusRealHorizonMoments
- Real horizon ⌊(B+2+t)N⌋, t ∈ [0,1]: each moment limit is affine in t between adjacent integer profiles.
## CofinalMobiusPositiveNegativeSourceFrequency (start)
- With C = B+1, |s| ≤ C on k ≤ (C+1)N: x² + Cx ≤ 2C²·1[x>0], x² − Cx ≤ 2C²·1[x<0] ⇒ Q ± C·S ≤ 2C²·#{±}. With S = o(N) and Q/N → profile(C) ≥ 6/π²: eventually #positive, #negative ≥ profile(C)·N/(4C²) on horizon (C+1)N. Both signs have positive lower frequency (not equality, not limits).
- Unconditional: both sign counts eventually ≥ (6/π²)N/(4(B+1)²) on horizon (B+2)N.
## CofinalMobiusSourceAlphabet
- Reflection: squarefree R in band lN < R ≤ (l+1)N ⇒ s_N(μ)(R) = −μ(R)·s_l(μ)(R). Via THIM horizon radical state, every value on horizon (B+2)N lies in the finite alphabet A_{B+1} = {0} ∪ {±s_l(μ)(d): 1 ≤ l ≤ B+1, d | primorial(l)}. Large-prime extension (d ↦ dp, p > l) keeps s_l and flips μ ⇒ every alphabet value is attained at arbitrarily large N. Alphabet = exact set of cofinal values. (Truncated divisor observable classical: Helfgott–Thompson.)
## CofinalMobiusSourceValueLaw
- Lagrange cardinal polynomials on the alphabet + moment limits ⇒ each level frequency #{k ≤ (B+2)N: s = a}/((B+2)N) converges to an explicit finite expression; masses ≥ 0, supported on alphabet, sum 1, symmetric a ↔ −a (from odd-moment vanishing). (Quadratic radical decomposition classical: de la Bretèche–Dress–Tenenbaum.)
## CofinalMobiusSourcePositiveSupport (start)
- Coprime-to-primorial(l) Möbius sign bands m (density(primorial l)/2) inject via m ↦ dm into the level −μ(d)·sign·s_l(μ)(d): lower mass ≥ density(primorial l)/(2d(B+2)) for each state ⇒ alphabet = exact positive support of the limit law.
- Zero atom has mass ≥ 1/(B+2) (initial block 2..N). density(a) > 0 ⇔ a ∈ alphabet.
## CofinalMobiusRealHorizonSourceLaw
- Real horizon ⌊(B+2+t)N⌋: level frequency → sample-weighted mixture ((1−t)(B+2)ρ_B + t(B+3)ρ_{B+1})/(B+2+t); total mass 1 on upper alphabet; positive support = lower alphabet at t = 0, upper alphabet for t > 0. No rate.
## CofinalMobiusSourceClockSupport
- s_N(μ)(n) depends only on rad n. Visibility clock w = n/rad n; fibre {w·R: R squarefree, rad w | R}. On horizon (B+2)N: nonzero source ⇒ clock < B+2; every clock w < B+2 attains both ±1 at arbitrarily large N (first-octave reciprocity with R − 1 = N). Clock < B+2 ⇔ cofinal unit attainment.
## MobiusMagnitudePeriodicApproximation (start)
- Band magnitude |Σ_{q≤j, q|n} μ(n/q)|; local model replaces μ(n/q) by μ(gcd(n/q, primorial(R)²)) — periodic with period j!·primorial(R)²; differs only at n containing a prime square p² with p > R (rough factor common to all quotients).
- Exact: band magnitude = |μ(rough_R(n))|·local magnitude (j ≤ R); agree when n has no p² with p > R. |s_N(μ)(n)| = band magnitude at band j = (n−1)/N. Shifted disagreement count over X with m shifts ≤ Σ_i (X + h_i)/R (Σ_{d>R} 1/d² ≤ 1/R).
## MobiusMagnitudePatternDensity
- Periodic count error ≤ period. Every fixed shifted band-magnitude pattern (shifts h, values a) has a natural density; |density − local residue density(R)| ≤ m/R; local densities → density as R → ∞. Values in {0..j}; densities nonnegative, ≤ 1, total mass 1, zero off the integer alphabet. Uses SelbergCompactTestApproximation.exists_limit_of_eventual_approximation.
## CofinalMobiusJointMagnitudeLaw (start)
- Fixed shifts cross band boundaries at ≤ 1 + Σh_i positions ⇒ fixed-band pattern laws transfer to the literal source |s_N(μ)(n + h_i)|; raw masses affine between integer horizons; normalized by real horizon gives a probability law (unconditional; positive support not identified with boundary-only patterns).
- Full statement: joint magnitude pattern mass on ⌊(K+t)N⌋ = Σ_{j<K} bandDensity_j + t·bandDensity_K; normalized by K+t is a probability law on {0..K}^m.
## CofinalMobiusMagnitudeObservablesAndGradient
- Magnitudes on horizon ≤ (K+1)N lie in {0..K}; every real observable Φ of shifted magnitude vectors has a limiting mean (finite-alphabet transfer). Magnitude-gradient mean (|s(n+1)| − |s(n)|)² has an explicit limit; (|v|−|u|)² ≤ (v−u)² ⇒ eventual lower bound on the signed gradient energy, no signed-correlation premise.
## MobiusFirstBandTwoPrimeBound
- First-band magnitude = squarefree indicator. Excluding 4 | · and 9 | · on n, n+1 (inclusion–exclusion upper bound, shifted congruence counts): #{n ∈ (t, t+L]: n, n+1 squarefree} ≤ (7/18)L + 8 ⇒ adjacent occupied first-band density ≤ 7/18.
## CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget (start)
- H_T^comp = Σ_{n=1}^{T−1}(1/(n+1) − 1/(T+1)) = H_T − 2T/(T+1); |H_T^comp − log T| ≤ |γ| + 3; H^comp/log T → 1.
- Predecessor-peak martingale: /log N → κ(ε) = activePairDrift − activeMartingaleDrift for every ε > 0; κ(ε)/ε → (Re D(1) − A_adj)/2 as ε → 0⁺. ½C(ε) + κ(ε) = interior counterterm. Canonical budget with v = C(ε), κ(ε): first two brackets o(log T) unconditionally ⇒ interior bracket = ½Energy + o(log T) (the whole difficulty sits in the interior bracket).
- Divisor-harmonic defect: for summable logWeight a (|a(d)|(1+log d)/d), |Σ_{k≤N} (Σ_{d|k}a(d))/k − density(a)·log N| ≤ explicit constant uniformly in N (regError ≤ (6+|γ|)·Σ logWeight); same against H^comp.
## PronicPotentialSelfCancellationAndInteriorGradientConservation (start)
- Route PM: 0 ≤ S_ε ≤ ½ ⇒ (ΔS_ε)² ≤ ¼; active-pair pronic energy ∈ [0, ¼]. Σ potential/pronic = Energy − activePairPronicEnergy.
- Non-circular conservation: InteriorGradient(T) + 2·LocalImpulse(T) = ActiveDeletedDiagonal + 2·PredecessorPeak − activePairPronic − potential(1)(1 − 1/(T+1)) (energy and interior martingale cancel identically) ⇒ (gradient + 2 impulse)/log T → 2·counterterm(ε), unconditional for ε > 0; slope 1 − A_adj ≥ 7/12 as ε → 0⁺.
- Two-sided: Energy ≤ 2·InteriorPronic + ½ and InteriorPronic ≤ 2·Energy + ½ ⇒ RH criterion via bounded pure-interior pronic energy (conditional).
- Unconditional at ε ≥ ½: pure-interior pronic energy bounded uniformly in T (transported from RHTower endpoint budget); nothing below ½.
## ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile
- r-th layer L_r(m) = ½Σ_{2r−1 ≤ d ≤ N, d|m}(c(d) − (2r−1)c(d)/d); vanishes for 1 ≤ m < 2r−1; shell endpoints n+1−r, n+r share only d = 2r−1 (summand 0). w-step telescoping Σ_{n<M}(F(n) − F(n+w)) = Σ_{j<w}F(j) − Σ_{j<w}F(M+j) ⇒ r-th layer telescopes to F(0) minus 2r−1 terminal terms.
- Second layer: L₂(m) = ½(s_c(m) − 3s_{c/d}(m)) + c(1) + [2|m]c(2)/4 (N ≥ 2). Route PM: sub-horizon profile (τ_ε(m) − 3τ_{1+ε}(m))/2 + 1 − [2|m]2^{−ε}/4, zero at m = 1, 2 ⇒ horizon-free decomposition A_ε(n) = ΔS_ε(n) + [P₂(n−1) − P₂(n+2)] + four-step interior.
## OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError (start)
- Abel summation vs antitone weight: |Σ w_i a_i| ≤ B·w_0 if partial sums ≤ B. Bounded partial sums ⇒ pronic tail after H ≤ 2B/((H+1)(H+2)).
- Re R_q(M) + φ(q)/2 is q-periodic mean 0 ⇒ |Σ_{M≤H} Re R_q(M)/pronic + Λ(q) − φ(q)/(2(H+1))| ≤ 2B_q/((H+1)(H+2)) (second-order finite-horizon von Mangoldt). Sieve version: subtract Σφ(e)Y(e)/(2(H+1)).
- Mean-centered discrepancy D̃ = D + ½Σφ(e)Y(e): Σ_∞ D̃/pronic = −ΣΛY + ½ΣφY; finite-horizon sieve remainder after subtracting ½ΣφY/(H+1) is O_{N,c}(1/((H+1)(H+2))).
## InteriorJumpOrbitCenteringAndCompensatedBounds (start)
- Interior atom: −B̃_e(n) with residues n ≡ 0, −1 (mod e) deleted. Along jump progression d−1+dk (period m = e/gcd(d,e)) the mean is 0 if gcd(d,e) = 1, else (e − g)/(2e²) ≥ 0; zero iff g = 1 or g = e; ≤ 1/(2e). Example d+2 vs 2(d+2): 1/(8(d+2)) > 0 (proper overlap prevents centering). Atom |·| ≤ ½. Centered periodic sequence has prefixes ≤ m ⇒ Abel bound m/d against harmonic / compensated weights (finite cutoff; not uniform in N).
- Centered jump prefix ≤ m = e/gcd(d,e); compensated / harmonic Abel bounds m/d; finite-cutoff interior sum along a jump progression after removing Σc(e)·mean(d,e): |·| ≤ Σ|c(e)|·(e/gcd)/d (grows with e).
## BirthDelayedInteriorJumpCenteringAndUniformPairBounds
- Anchored atom = atom − (e−1)/(2e) (initial value). Subtract conditional mean only after birth k ≥ e/d (⇔ e ≤ d−1+dk). Pre-birth terms ≤ 1/e each ⇒ head ≤ (e/d)/e ≤ 1/d; tail ≤ 2(e/g)/(d(K+1)) ≤ 2/g ⇒ uniform pair bound 1/d + 2/gcd(d,e) (no growth in e) for d ≥ 2. Finite-cutoff interior and Route PM prefix (with linear density correction n(Y(1) − Re D(ε))) satisfy Σ|c(e)|(1/d + 2/gcd(d,e)). Remaining: signed modulus sum and strict contraction (not established).
## UniformActiveDeletedCompensatedRemainder (start)
- |a(n)| ≤ τ(n)n^{−ε} ⇒ summable logWeight. Applies to μ(n)n^{−ε} and to the shifted-exponent product coefficient ⇒ uniform O(1) compensated harmonic remainder of the divisor field and active-deleted diagonal after canonical drift removal (diagonal piece of the interior remainder problem).
- Proved: for every ε > 0 ∃C: |ActiveDeletedDiagonal(T) − C(ε)·H_T^comp| ≤ C uniformly in T (shifted product coefficient + both single fields + harmonic−H^comp ≤ 2).
## AsymmetricAdjacentDivisorTruncation
- Two independent cutoffs D (for η-field at n) and A (for ε-field at n+1): |adjacent mean − adjacent density| ≤ 2·tail_η(D) + 4·mass_η(D)·tail_ε(A) + mass·mass/N (bounded full field pays first tail; CRT unit defect pays finite head; limit passes truncation to the density). mass ≤ D; reciprocal tail_ε(A) ≤ A^{−ε/2}·Σ|w_{ε/2}(d)|/d.
## UniformAdjacentDivisorCompensatedRemainder (start)
- Choosing D = ⌈N^α⌉ (α = ε/(8(1+ε))), A = ⌈N^{1/2}⌉: adjacent mean has power rate C·N^{−δ}, δ = min(αη/2, ε/8, ¼) > 0, for every ε, η > 0 ⇒ (via Abel/ShiftPartialSummation) horizon-independent compensated bound for adjacent correlations (predecessor-peak bracket). Interior contraction not supplied.
- Abel with partial sums ≤ B·T^a (a < 1) ⇒ compensated-kernel sum bounded uniformly ⇒ ∃C: |Σ(adjacent product − density)·(1/(n+1) − 1/(T+1))| ≤ C for all T (ε, η > 0).
## UniformRenormalizedInteriorEnergyRemainder
- Compensated vs harmonic shift for 0 ≤ f ≤ 1 costs ≤ 2. Single field, predecessor-peak bracket: |PredecessorPeak(T) − κ(ε)H_T^comp| ≤ C for every ε > 0 (via adjacent densities (ε,ε), (ε,1+ε) and single fields).
- KEY: |2·Interior(T) + 2·counterterm(ε)·H_T^comp − Energy(T)| ≤ C for every ε > 0 (coefficient-one comparison). ⇒ strict interior contraction (2I + 2c·H ≤ (1−δ)E + C) ⇔ bounded actual energy. Exact equivalence; neither side proved. The interior martingale is energy in disguise — the Route PM budget cannot be split off into the interior.
## EnergyCenteredPronicGramPositivityAndVonMangoldtLowerBound (start)
- Energy-centered discrepancy D + ΣΛ(e)Y(e) has pronic mean 0; its pronic square series = energy-centered Gram form ≥ 0. Pronic Gram form = (ΣΛY)² + energy-centered form ⇒ (ΣΛ(e)Y(e))² ≤ Gram form. Mean-centered (½ΣφY shift) Gram form ≥ 0, bilinear coupling with Λ and φ functionals.
- Prime dilation (p ∤ q, r): Λ(pq) = Λ(pr) = 0; energy-centered recurrence G^ec(pq,pr) + G^ec(pq,r) + G^ec(q,pr) = (p−1)G^ec(q,r) + (p−1)Λ(q)Λ(r).
- Gram = mean-centered form + (ΣφY)(ΣΛY) − ¼(ΣφY)². Energy-centered diagonal recurrence G^ec(pq,pq) = (p−1)G^ec(q,q) + (p−1)Λ(q)² − 2G^ec(pq,q).
## ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds
- Progression harmonic Σ_{k<K+1} 1/(kq + r), 1 ≤ r ≤ q: 1/r − 1/q ≤ sum − H_K/q ≤ 1/r; |sum − log K/q| ≤ 1/r + (|γ|+1)/q.
- d₂ | n, d₁ | n+1 ⇒ coprime, max(d₁, d₂+1) ≤ n+1, d₁d₂ ≤ (n+1)², 1/(n+1) ≤ min(1/d₁, 1/(d₂+1)) ≤ 1/√(d₁d₂) ⇒ shifted-divisor progression defect ≤ min(1/d₁, 1/(d₂+1)).
## MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge (start)
- Centering discrepancy κ(q) = φ(q)/2 − Λ(q). G^mc(p,q) = G^ec(p,q) + κ(p)κ(q) ⇒ mean-centered form = energy-centered form + (ΣκY)² ≥ energy-centered. κ(pq) = (p−1)φ(q)/2 for p ∤ q; mean-centered prime-dilation recurrence is pure-totient: G^mc(pq,pr) + G^mc(pq,r) + G^mc(q,pr) = (p−1)G^mc(q,r) + p(p−1)φ(q)φ(r)/4. Large-p limit G^ec(pq,r) → φ(r)Λ(q)/2 − G(q,r); non-prime-power q ⇒ G^ec(pq,r) + G^ec(q,r) → 0.
## TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation
- Shifted two-mode (u,v) on {r, pr}: Gram form = (u−v)²G(r,r) + p v²G(r,r) + 2(u−v)v(G(pr,r) + G(r,r)); shear-balanced u = v gives p v²G(r,r). Energy-centered adds (p−1)v²Λ(r)²; mean-centered adds p(p−1)φ(r)²v²/4.
- Exact (Hilbert step vector f_{pr} = √p D_{1/p} f_r − f_r): G(pr,r) + G(r,r) = √p Φ_r(p); G(pr,qr) + G(pr,r) + G(qr,r) + G(r,r) = √p√q Φ_r(p/q) (upgrades a prior inequality). √p Φ_r(p) → φ(r)Λ(r)/2 along primes (→ 0 for non-prime-power r): Φ_r(p) = O(p^{−1/2}).
- Prime star {r} ∪ {pr: p ∈ S}: form = (w₀ − Σw)²G(r,r) + 2(w₀ − Σw)Σw(p)(G(pr,r) + G(r,r)) + Σ_{p,q}(w(p)√p)(w(q)√q)Φ_r(p/q); balanced w₀ = Σw ⇒ pure dilation-profile form.
## RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence (start)
- Route PM cofactor divisor weight Re(cofactor(ε, Q+1, d)) = Ramanujan inverse of q ↦ Re w_ε(q) at cutoff Q+1 ⇒ Y(e) = Re w_ε(e); |weight(d)| ≤ d^{−ε}; Selberg / Bézout / variance forms are diagonal sums of (Re w_ε(e))² with φ, μ weights.
- Dictionary: BVI prefix discrepancy at this weight = Re(Route PM cumulative prefix); −ΣΛY = PM energy mean; pronic Gram form = PM Gram quadratic; energy-centered = PM energy variance; mean-centered = PM mean-centered quadratic.
- BVI Gram budget criteria: energy-centered (or mean-centered, or raw) Gram form of cofactor weight bounded uniformly in Q ⇒ Fermi source ∈ L²(0,∞) and Mellin analytic on Re s > ½ (conditional; transports RHTower variance criterion). Synthesis theorem packages energy sandwich, gradient conservation drift, Gram dictionary, two-prime dilation identity.
## CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity (start)
- Y_ε(pr) = −Y_ε(r)/(p^{1+ε} − 1) (p ∤ r); Y(r) − Y(pr) = p^{1+ε}/(p^{1+ε}−1)·Y(r) (local Euler factor). Pairing depth k with k+1: Y(r)S_r(N) + Y(pr)S_{pr}(N) = E_p Y(r)(S_r(N) − p^{−ε}S_r(⌊N/p⌋)); step source: E_p Y(r)(f_r(x) − p^{−1−ε}f_r(x/p)); Hilbert: E_p Y(r)(f_r − p^{−½−ε}D_{1/p}f_r). Growing dilation weight converted into decaying Dirichlet power.
- Hypercube over squarefree P ⊥ r: Σ_{m|P} Y(mr)S_{mr}(N) = E(P)·Y(r)·Σ_{d|P} μ(d)d^{−ε}S_r(⌊N/d⌋), E(P) = Π_{p|P}(1 − p^{−1−ε})^{−1}; same for step sources with d^{−1−ε}. Finite cancellation E(P)·Σ_{d|P}μ(d)d^{−1−ε} = 1 removes the undilated singularity.
- Two-mode with actual weights on {r, pr}: Gram form = E_p²Y(r)²[(1 + p^{−1−2ε})G(r,r) − 2p^{−1−ε}(G(pr,r) + G(r,r))] = E_p²Y²[(1 + p^{−1−2ε})G(r,r) − 2p^{−½−ε}Φ_r(p)]; energy-centered adds (p−1)/(p^{1+ε}−1)²·Y²Λ(r)². Prime star with actual weights: Y(r)²[(1 + Σ1/(p^{1+ε}−1))²G(r,r) − 2(1+Σ)Σ(G(pr,r)+G(r,r))/(p^{1+ε}−1) + Σ_{p,q}(√p/(p^{1+ε}−1))(√q/(q^{1+ε}−1))Φ_r(p/q)].
- Unconditional prime summability: Σ_p 1/(p^{1+ε}−1), Σ_p p/(p^{1+ε}−1)², Σ_p |G(pr,r) + G(r,r)|/(p^{1+ε}−1), same for G^ec. Band residue μ * bandSquarefree: value 1/(p^{1+ε}−1) at p ∤ d, 0 at p^k (k ≥ 3), Σ|·|/n summable.
## AllDepthHilbertDilationCubeAndHyperCubeGramFactorization (start)
- rayDilate is linear, D_u D_v = D_{uv}, Re⟨D_{1/a}f_r, D_{1/b}f_r⟩ = Φ_r(a/b). Σ_{m|P} Y(mr)f_{mr} = E(P)Y(r)·Σ_{d|P} μ(d)d^{−½−ε}D_{1/d}f_r in SoninL2 ⇒ hypercube Gram = E(P)²Y(r)²Σ_{d₁,d₂|P} μ(d₁)μ(d₂)(d₁d₂)^{−½−ε}Φ_r(d₁/d₂) (also G^ec for non-prime-power r).
- Hypercube diagonal d₁ = d₂: Σ_{d|P} d^{−1−2ε}·G(r,r). μ(d) = (−1)^{ω(d)} on squarefree; Möbius divisor sums stratify into alternating depth shells; E(P)·Σ_k(−1)^kΣ_{ω(d)=k}d^{−1−ε} = 1. Energy-centered primitive S^ec = Re S + Λ: cross-depth pair keeps only the base Λ(r) (Λ(pr) = 0); hypercube: Σ_{m|P}Y(mr)S^ec_{mr}(N) = Y(r)Λ(r) + E(P)Y(r)Σ_k(−1)^kΣ_{ω(d)=k}d^{−ε}Re S_r(⌊N/d⌋).
## PrimePacketConditionalTailAndCoherentPrefix (start)
- Prime packet X(n) = Σ_{p∈S} a(p)S^ec_p(n): pronic mean 0; bilinear = energy-centered Gram. Split at H: Gram = prefix bilinear + (H+1)·headMean_a·headMean_b + centered-tail bilinear (tail residual has pronic mean 0; pronic tail mass 1/(H+1)). ⇒ prefix energy + (H+1)·headMean² ≤ packet energy (coherent lower bound).
- Primes p > H: before the first jump X(n) = Σa(p)log p − n·Σa(p) (affine); headMean = M₀(H)·logMoment − M₁(H)·mass with pronic prefix moments M_k(H) = Σ_{n≤H} n^k/(n(n+1)). Only mass and log-moment channels survive in the prefix.
- Two-moment lower bound for packets above H: M₀L² − 2M₁AL + M₂A² + (H+1)(M₀L − M₁A)² ≤ packet energy (A = mass, L = log-moment). Prime pair common ramp: Σ_{n<min(p,q)} n/(n+1) − log p log q ≤ G^ec(p,q).
## PronicResidueGapEnergyAndPrimePairDistance
- Residue-gap term ((n mod p) − (n mod q))²/(n(n+1)). Pronic mass of [a,b) = 1/a − 1/b. Exact cell energy for q = p + h (cells k·p..(k+1)p, kh ≤ p); prefix up to (K+1)p (K = p/h) = h·H_K − h²K²/(p(K+1)); tail ≤ q²/N. ⇒ h·H_K − h ≤ gap energy ≤ h·H_K + (p+h)²/(p(K+1)) ≤ h·H_K + 4h for h ≤ p.
- Prime distance: G^ec(p,p) + G^ec(q,q) − 2G^ec(p,q) = gapEnergy(p,q) − (log p − log q)² ≤ symmetric gap budget (nearby primes cost ~ gap·log(p/gap)). Not a bound for arbitrary packets.
## RamanujanDilationProfileResidueGapBudget (start)
- p·Re R_r(⌊n/p⌋) = −Σ_{(a,b): ab=r} μ(b)(n mod pa) (floor expansion). Scaled distance Σ (pR_r(n/p) − qR_r(n/q))²/pronic = (p+q)G(r,r) − 2√p√q Φ_r(p/q) ≤ residueBudget(r)·gapBudget(p,q), residueBudget(r) = #antidiag·Σμ(b)²a. Gap budget scales linearly under common dilation.
- Profile defect: 0 ≤ G(r,r) − Φ_r(p/q) and 2√p√q(G(r,r) − Φ_r(p/q)) ≤ residueBudget(r)·gapBudget(p,q) − (√p − √q)²G(r,r).
## OrderedPronicGapCellsAndCollectivePrefixEnergy (start)
- Compensated residue difference on quotient cell k (kh ≤ p): values kh − p on [kp, k(p+h)), (k+1)h on [k(p+h), (k+1)p); pronic mean 0, energy h/k − h²/p; every finite prefix mean ≤ 0. Ordered disjoint gaps (p + h ≤ r): pair covariance ≤ 0 at every horizon T.
- Nonneg coefficients + nonpositive covariances ⇒ energy ≤ Σa_i²B_i; signed ⇒ factor 2 (split a = a⁺ − a⁻; no factor counting gaps). Chain constructor pronicGapChainLower places gaps inside a pre-overlap cluster (base > K·Σh). Levels i, j with |i − j| ≥ 2 have disjoint supports ⇒ parity split gives all-level bound with factor 2 more.
- Gap-chain collective bound: Σ_{n<T}(Σ_k Σ_i a_i·cell)²/pronic ≤ 4Σa_i²(h_i H_K − K h_i²/p_i). Cells sum to the literal residue difference + birth term h·1[p ≤ n] on n < (K+1)p. Birth packet energy ≤ (H/P)Σa_i²h_i (Cauchy over gaps, zero before base P). ⇒ literal signed residue-gap packet on prefix (K+1)P: ≤ 8Σa_i²(h_i H_K − Kh_i²/p_i) + 2(H/P)Σa_i²h_i. Finite prefix only; signed tail not controlled.
## RamanujanOrderedGapCollectivePrefixEnergy
- Cofactor dilation d scales chain (offset' = d·offset + d−1); scaled prefix bound d·(8H_K + 2H/P)Σa²h restricted to original horizon. Scaled Ramanujan packet Σa_i(p_i R(n/p_i) − q_i R(n/q_i)) has global pronic mean exactly 0 (floor-dilation mean: each term −Λ(r+2)). Prefix energy ≤ residueBudget(r+2)·(8H_K + 2H/P)·Σa_i²h_i; bilinear via Cauchy. Tail unresolved.
## RamanujanGapChainExactPrefixGram
- Exact cell: Σ over cell k of scaled distance = h·c_k(r)²/k + (h²/p)(R(k−1)²/k − R(k)²/(k+1)) (c_k = Ramanujan natural coefficient = lag coefficient); prefix to (T+1)p: h·Σ_{k≤T} c_k²/k − h²R(T)²/(p(T+1)) (T = min(K, p/h)) ⇒ lower bound on full profile distance (p+q)G − 2√(pq)Φ.
- Ordered gaps in common cluster: off-diagonal covariance = −h_i h_j R(K)²/(P(K+1)) (endpoint product only). Exact packet Gram: (Σa_ib_ih_i)·J_K − (Σa_ih_i)(Σb_ih_i)R(K)²/(P(K+1)), J_K = Σ_{k≤K} c_k(r)²/k. Energy ≤ (Σa²h)J_K (no cofactor cost); ≥ ½(Σa²h)J_K (via R(K)² ≤ J_K·K(K+1)/2, K·H ≤ P). At resets K = r·t (R = 0) Gram is exactly diagonal ⇒ coefficient readout a_j = ⟨packet, gap_j⟩/(h_j J_K). Prefix energy = 0 ⇔ K < visibility clock (r+2)/rad(r+2).
## RamanujanGapChainConditionalTailCoercivity
- Prefix mean of packet = (Σa_ih_i)R(K)/((K+1)P). Conditional tail completion: total energy = (Σa²h)·J_K + centered tail Σ(X(N+n) + (Σah)R(K))²/pronic (forced tail mean cancels head endpoint loss exactly). ⇒ every signed chain pays full jump energy (Σa²h)J_K ≤ global energy; profile distance ≥ h·J_{min(K,p/h)}.
- Clock readout: at K = clock + t, endpoint-corrected probe (gap_j packet + h_jR(K)) recovers a_j = ⟨X, probe⟩/(h_jJ_K).
## AllLevelPronicResidueGapCentering (start)
- On every quotient cell [kp,(k+1)p) the residue difference (n mod p) − (n mod (p+h)) has ≤ 1 jump (at s = (j+1)q, j = kp/q); conditional pronic mean is −(k−j)(s − kp)/(j+1) if s < (k+1)p else jq − kp; lies in [−h, 0] even beyond pre-overlap. Packet of local means for moduli P + offset_i: energy ≤ (Σh_i/P)·Σa_i²h_i at every horizon ⇒ full packet reduces to locally centered packet with uniform cost; mixed-level covariance of the centered packet remains the open dispersion obligation.
- Centered cell: pronic mean 0, variance (s − kp)((k+1)p − s)/((j+1)²p) if interior jump else 0. Local-mean packet bounded by (H/P)Σa²h (Cauchy, zero below P); full packet ≤ 2·centered packet + 2(H/P)Σa²h.
## SharedBirthPronicCellCovariance (start)
- Explicit pronic tail of a centered cell at every cut (tent shape). Product start (cells of p and r = p + offset with unit gaps starting at pr): covariance 0. Shared start with p = g·l, r = g·k, k = l + offset (common start kp = lr): covariance = (r+1)·tail of the smaller cell beyond kp + l = positive tent value ((k+1)p − s)/((j+1)p) or (s − kp)(g−1)/((j+1)p) (s = next jump of p+1) if interior jump; positive iff g > 1 and interior jump. ⇒ same-level nonpositive-covariance argument does NOT extend across levels (unconditional family with positive covariance = smaller diagonal variance).
- Shared-start covariance ≥ 0; = 0 at g = 1; pre-overlap value 1/k − 1/p; coherent family (g = k + padding + 1) has positive covariance equal to the smaller cell's diagonal variance.
## NaturalCutoffMultiDepthCofactorAndConditionalTailBridge (start)
- E(Π_{p∈S}p)·Y_ε(1) = RHTower aperture scale; divisor-cube sum of Y(m)R_m(N) = Re of complete Ramanujan primitive (links to PMRamanujanCompleteAperture small-damping divergence ⇒ natural denominator order q ≤ Q needed). Y(1) = Re D(ε), Y(p) = −Re D(ε)/(p^{1+ε} − 1).
- Prime cofactor packet r ≤ R < p: Λ(pr) = 0 for 2 ≤ r < p ⇒ energy-centered packet = Re packet + Y(p)log p; for N < p: (−Re D·log p + Re D·N + Re prefix(R−1,N))/(p^{1+ε} − 1).
- Natural-cutoff energy-centered prefix (Route PM cumulative prefix − energy mean) has pronic mean 0; energy variance = headEnergy(H) + (H+1)·headMean² + centered tail variance (orthogonal, any H).
- Head energy ≤ 2·prefixEnergy + 2·energyMean².
## TwoLagFiveModePolytopeAndHigherMomentPhaseRecoveryBridge (bridge to BSU, THIM)
- H₃ = (0,1,2): centered 3-tuple variance 3Cov₀ + 4Cov₁ + 2Cov₂ = Σ Λ_{H₃}(e)Y(e)², Λ_{H₃} = 3φ + 4μ + 2λ₂; 0 ≤ Λ_{H₃} ≤ 4φ via two-lag moment cone facets; values 1, 0, 2, 8, 16 at e = 2,3,4,6,12 (0 at 3 since H₃ covers Z/3; 4φ at 6, 12) ⇒ 0 ≤ V_{H₃} ≤ 4V. Five-mode weight on {1,2,3,4,6,12}: Cov₀ = a² + 2b² + 2c² + 2d² + 4e², Cov₁ = −a² − b² + d², Cov₂ = a² − b² − 2c² − d² + 2e², V_{H₃} = a² + 2c² + 8d² + 16e², 12E_prim = 3a² + 8b² + 12c² + 24d² + 96e².
- 3-point moments recover signed Y(q) for odd q (2-point only Y²). Even pair {6,10}: all moments of degree ≤ 5 blind to (a,b) ↦ (a,−b); zero-lag 6th moment separates (gap 960a³b³); affine 2-pt + 6th recover up to global sign.
- Totient threshold Φ_max(N) = max_{p^a≤N} φ(p^a) < N observations determine the full phase; window < φ(p^a) cannot separate valuation clock shift. Active power sampling j^m: exact attained amplification 2d(τ(d)−1)/(d−1) for squarefree coefficients; samples realizable beyond any scale.
## ClockWaveletTensorBuchstabL2TelescopeAndShortWindowBridge (bridge to THIM)
- Lag multipliers tensorize across cross-coprime moduli/lags; composite clock wavelet at transverse clock isolates valuation shells v_p(q) ∈ {a, a+1} with ±p^a. Prime horizon step: E_{N+1}(M) − E_N(M) = ⌊M/(N+1)⌋(c(N+1)² + 2c(N+1)H_N) + 2c(N+1)D_N(⌊M/(N+1)⌋); scale-halving subadditivity. Möbius L² energy ≤ 1 + j(M − N) on first three bands.
- Short window defect = ΔLCM remainder + ΔCRT remainder − M·reserve; ≤ 0 for all weights ⇔ endpoint observation states equal (radical states for squarefree weights).
## BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge (bridge)
- Barban–Vehov weight b_X: Y(e) = 0 for X < e ≤ N, |Y(e)| ≤ A/φ(e); V and |Bézout form| ≤ 4A²(1 + log X); normalized (w(1) = 1): ≤ 4A²(1 + log X)/(log X)². |Q_Bez| ≤ Q_Sel generally. ker P endpoint weight (harmonic mean 0): V = Q_Sel, 2Q_Bez ≤ V, discrepancy = cumulative sum, bounded by ℓ¹. Franel GCD-square form of b_N ≤ N²·diag and ≤ 64A²N(1 + log N). Deletion-averaged source: 1 at k = 1, 0 on [2, X], (Λ(k) − b_X(k))/(log M − log X) beyond.
- Vasyunin: Fermi–Nyman head/tail Gram = finite pronic-cell sums (zero remainder). Kloosterman distinct moduli: full lcm blocks vanish; fibre ≤ gcd; bound min(terminal, shared-gcd budget). Stadlmann reciprocal phase = Kloosterman(0,Σc) = Ramanujan sum; second moment qφ(q).
- Log-energy sandwich: 0 ≤ (log-dilation + log-prefix − ρ·log-forcing covariances) ≤ log N·Energy, gap = pronic log deficit ≥ 0. Within incidence damping radius 1/(96(N+1)(log N)²): Route PM renormalized defect ≤ −½ on six-horizon prefixes.
## BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge (bridge, start)
- Beurling invariance obstruction: Möbius inversion, strict log-submodular Gibbs table, prime-power log completion, Gamma gauge in [1,2], three-sector large-label decomposition all hold in every abstract Beurling system (incl. RH-violating) ⇒ multiplicative-only / one-large-prime arguments cannot prove RH. Z-specific input: dilation profile = √(pq)·integer-cell Gram; additive lags h = pa − qb at horizon Q² with error B²/Q; least successor seed pa = qb + 1 (a ≤ q) resonance with uniform O(1/k) error.
- Logarithmic cotangent transport: increments of t/(2π)·log((n+j)/n) positive, strictly decreasing, < t/(2π(n+j)); unweighted defect < 0 below t < 2πn, nonincreasing beyond sub-resonant head; weighted defect = zeta source remainder functional.
- Schur collar (THIM): m_a(x) ≤ 4e^{4t}(m_a(t+x) − m_a(t−x)), damped refinement; low-prime collar budget. Möbius defect ≤ −1 on six-horizon prefixes with |s| ≤ 2; uniform damping radius gives D < −½ on radical fibers / prime powers; unit envelope |s_N(c_ε)(k)| ≤ 1 for all ε > 0 on k ≤ CN ⇔ C ≤ 5 (k ≤ 5N + b ⇔ b < 5).
## VaughanTypeIIShortAndAllHorizonMobiusL2Energy
- ζ * truncAF(μ, N) = s_N(μ); typeIIShort_N(k) = 1[k=1] − s_N(μ)(k) (= −s for k ≥ 2, 0 for k ≤ N). Prefix L² energy = 1 + Σ typeIIShort². All horizons: E ≤ M(H_M)³ (divisor-square moment), gradient ≤ 4(M+1)H³, |R_N(M)| ≤ 2(M+1)H³ (no window restriction). Linear window: Type-II short energy ≤ B²(L − V) (removes (log L)³).
- Möbius Vaughan identity μ = μ_U + μ_V − ζμ_Uμ_V + (μ − μ_U)·typeIIShort_V; trans-horizon quotient windows split into Type I + Type II.
## VinogradovKorobovCofinalMobiusDiscrepancy (start)
- |M(N)| ≤ CN·exp(−κ·vkScale(N)/24) (κ = 1/(12·10⁸), RHTower VK); every window Σ_{N<d≤Q}μ(d) bounded by sum of two VK rates (any Q); literal prefix Σs_N(μ) on M ≤ (B+1)N bounded by 1 + Σ_q VK rates. First octave: typeIIShort = μ; short-interval mean squares of s_N(μ) on (N, 2N] equal those of μ ⇒ unconditional short-interval L² cancellation (MoebiusMeanSquareRealForm).
## CompletePronicVaughanCalibration
- Route PM centered prefix = Σ_{d≤n} μ(d)d^{−ε}⌊n/d⌋ − Re D(ε)·n. Five Vaughan pieces (two small legs, −U×V rectangle, both-large remainder, −density·n − ΔS) sum exactly to interior prefix; interior energy = Σ of 25 weighted Gram entries = diagonal + signed mixed remainder.
- For ε ∈ (0, ½): |I_ε(n)| ≤ 3/2 + C n^{1−ε}/(log n)⁴ (RHTower log-four remainder) ⇒ interior energy ≤ head + 9/2 + 2C²Σ majorant, majorant n^{2−2ε}/((log n)⁸ n(n+1)) is NOT summable for ε < ½ (dominates 1/(2n)) — the squared log-saving bound is too weak. Mixed remainder bounded relative to diagonal uniformly in cutoffs. Sign flip of component k changes energy by 4·(row k off-diagonal Gram) (exact mixed observation diagonal data misses). |InteriorEnergy − Energy| ≤ K uniformly (difference absolutely summable).
## TheVaughanDiagonalContainsLinearPoleMass (start)
- Pole piece −ρn − ΔS (cutoff independent) has diagonal ≥ ρ²T/4 − ¼ ⇒ Vaughan diagonal is linear in T; pole Gram/T → ρ² along any moving cutoffs. Interior prefix/n → 0 (absolute convergence of divisor density) ⇒ interior energy/T → 0 for every ε > 0 (no zero-free input). Mixed pole row/T → −ρ² (cutoff independent): the mixed part cancels asymptotically all of the diagonal; no cutoff choice makes all pole cross entries sublinear. Relative cancellation alone does not bound the residual.
- Eventually some pole cross entry ≤ −ρ²T/8 for every (U,V). Mixed/diagonal → −1 uniformly in cutoffs; diagonal + mixed = interior energy exactly.
## TheFixedVaughanGramHasRankOneLeadingTerm
- Fixed cutoffs: each Vaughan piece/n → explicit mean (small densities Σ_{d≤U} μ(d)d^{−1−ε}; unsigned density ζ(1+ε) = 1/Re D(ε); small×small −ζ·dens_U·dens_V; large = Re D − dens_U − dens_V + ζ dens_U dens_V; pole −Re D). Means sum to 0. Normalized Gram → outer product of means (rank one); diagonal density Σmean² > 0; any combination's energy density = (Σ w·mean)².
- Bounded interior energy ⇔ |mixed/diagonal + 1| ≤ C/T eventually (reciprocal-horizon relative error needed, not just relative cancellation). Covering rectangle n < (U+1)(V+1) kills the both-large piece; square horizon N² with cutoffs N.
## TheAbsoluteVaughanRemainderBudgetHasTheTrivialExponent (start)
- Unsigned floor sum Σ_{d≤n} d^{−ε}⌊n/d⌋ = ζ(1+ε)n + c_ε n^{1−ε} + R_ε(n) (sub-half smooth-power expansion, THIM). Small×small piece = −ζ·floor − c_ε n^{1−ε}·(partial pole sum) − smooth remainder; pronic norm of smooth remainder ≤ C_ε·A_U·A_V with A_U = Σ|μ(a)|a^{−ε−½} (absolute critical Wiener partial sums).
- A_U ≤ U^{½−ε}/(½−ε) + 1 and A_N ≥ ¼N^{½−ε} (squarefree quarter density) ⇒ (A_N²)² ≍ N^{2−4ε}; smooth remainder at square horizon T = N²: energy ≤ C·T^{1−2ε} (trivial exponent); NO fixed power saving δ > 0 possible in this absolute budget (lower bound). Concerns the absolute budget, not the signed remainder.
## UniformFloorMeansAndMovingVaughanGrams (start)
- Floor average (1/n)Σ_{d≤n} a(d)⌊n/d⌋ → Σa(d)/d; dominated |a| ≤ b ⇒ |error| ≤ floor-mean defect of b (→ 0 for summable b/d). Small×small piece = −floor average of (μ_U * (μ_V * ζ))(d)d^{−ε}; |μ_U * μ_V * ζ| ≤ τ(n)²; majorant τ(d)²d^{−ε} has summable reciprocal mass ⇒ first three Vaughan means and errors bounded uniformly in both cutoffs; all five means ≤ Re D + 3·mass; uniform mean error sequence → 0.
- Gram/T − mean_i·mean_j ≤ Gram error (Cesàro of mean errors) → 0 uniformly in (U,V). Both-large mean = ζ(1+ε)(Re D − dens_U)(Re D − dens_V) (≥ 0 when U = V). dens_U → Re D. Moving cutoffs/horizon → ∞: means → Re D·(1, 1, −1, 0, −1); normalized Gram → Re D²·s_is_j (rank one); diagonal/H → 4Re D² (also at square horizon N² with cutoffs N).
## UniformCancellationInTheUndampedVaughanConvolution (start)
- Undamped small×small prefix Σ_{d≤n}(μ_U * μ_V * ζ)(d) = Σ_{a≤U,b≤V} μ(a)μ(b)⌊n/(ab)⌋; |prefix − n·h_U·h_V| ≤ UV (h_U = Σ_{d≤U}μ(d)/d, |h_U| ≤ 1). Möbius ring identity μ = μ_U + μ_V − μ_U μ_V ζ + large ⇒ prefix = M(min(U,n)) + M(min(V,n)) − M(n) + Σ large; large = Σ_{U<a≤n} μ(a)Σ_k Σ_{V<b≤n/(ak)} μ(b); if |M(x)| ≤ Lx for x ≥ D ≤ V: |Σ large| ≤ 2Ln(H_n)².
- Uniform: if |M(x)| ≤ Lx and |h_x| ≤ K for x ≥ D: |prefix − n h_U h_V| ≤ D² + D + 3Ln + 2Ln H_n² + Kn for all U, V (short cutoffs via rounding, long via ring identity). With arbitrary log-power Mertens/harmonic rates: error ≤ D² + D + (…)/log(D)^p.
## UniformLogarithmicCancellationInTheVaughanConvolution
- D = ⌊n^{1/4}⌋ ⇒ for every q: |Σ_{d≤n}(μ_U*μ_V*ζ)(d) − n h_U h_V| ≤ C n/(log n)^q uniformly in U, V.
## UniformStretchedExponentialCancellationInTheVaughanConvolution
- With unconditional stretched Mertens/harmonic rates (exp(−(log x)^{1/3}/216)): uniform error ≤ C n exp(−c (log n)^{1/3}), c = (1/8)^{1/3}/432; ⇒ error·(log n)^q ≤ C n c^{−3q}(3q)! for all q with one threshold. (File ends with #print axioms lines.)
## UniformLogarithmicCancellationInMobiusFloorSums (start)
- Σ_{d≤U} μ(d)⌊n/d⌋: |· − n h_U| ≤ U (rounding); = 1 − Σ_{k≤n}Σ_{U<d≤n/k}μ(d) (Möbius inversion); |· − 1| ≤ 2Ln H_n if |M| ≤ Lx beyond D ≤ U; uniform bound D + 1 + 2Ln H_n + Kn.
- Single Möbius floor sum = convolution prefix with V = 1 ⇒ |Σ_{d≤U}μ(d)⌊n/d⌋ − n h_U| ≤ C n/(log n)^q uniformly in U.
## UniformCriticalPronicPairingsFromLogarithmicCancellation
- If |f_i(n)| ≤ A n (all n) and eventually |f_i(n)| ≤ B√n/(log n)² uniformly in i: one summable envelope g(n) for (√n|f| + f²)/(n(n+1)) ⇒ uniform bound on pronic energy ‖f_i‖²_T and on the mixed smooth pairing Σ√n|f_i|/(n(n+1)). Threshold: two logs below √n suffice (Σ 1/(n log² n) < ∞).
## UniformLogarithmicPrefixRemaindersInAllVaughanRows
- For 0 < ε ≤ ½, every q: all five smooth-subtracted Vaughan rows r_i(n) (row − c_ε h_U h_V s_i n^{1−ε}) satisfy |r_i(n)| ≤ C n^{1−ε}/(log n)^q uniformly in U, V. Ingredients: centred divisor prefix log rate, truncated-Möbius pattern prefix log rate, Vaughan convolution fluctuation log rate, unit-pattern remainder |·| ≤ F n^{(1−ε)/2}, active sawtooth ≤ ½. Large row = interior − (other four). Also uniform linear bound |r_i(n)| ≤ E n (unit-bounded coefficient pattern prefix ≤ (1 + 1/(1−ε) + 1/ε) n).
## UniformHarmonicVaughanGramsAtHalfDamping
- ε = ½: all remainders have one summable envelope ⇒ uniform energy and mixed bounds. Centred Gram_{ij}(T) = (c_½ h_U h_V)² s_i s_j Σ_{n≤T}1/(n+1) + O(1) uniformly in U, V, T (row = a_k√n + r_k; cross terms a_i·Σ√n r_j/(n(n+1)) bounded; r_i r_j bounded by common energy). Harmonic (log T) rank-one leading term; error bounded.
## UniformHarmonicEnergyLawsForVaughanSuperpositions
- ε = ½, any packet w: |‖packet_w‖²_T − (c_½ h_U h_V (w₃ − w₂))²·Σ_{n≤T}1/(n+1)| ≤ C(Σ|w_i|)², uniform in U, V, T. Smooth coefficient zero (e.g. w₂ = w₃) ⇒ uniform finite packet energy. Only the convolution difference w₃ − w₂ carries harmonic (log T) growth.
## PositiveFloorMajorantsControlPronicEnergy
- |a| ≤ b, Σb/d < ∞ ⇒ centred floor prefix of a dominated cellwise by that of b. Bounded pronic norm ⇔ Σ f²/(n(n+1)) < ∞. Cellwise limits + one summable square envelope ⇒ convergence in total pronic distance (dominated convergence) and at every moving finite horizon.
## FixedVaughanPacketsHaveTwoExplicitObstructions
- packet_w = Σ w_i·piece_i; packet_1 = interior. packet_w − w₃·interior = Σ_{i≠3}(w_i − w₃) piece_i. Small leg − mean·n = Σ_{d≤U} μ(d)d^{−ε}(⌊n/d⌋ − n/d), |·| ≤ small mass, pronic norm ≤ √2·Σ|μ(d)|d^{−ε−½}. Pole leg − mean ≤ ½.
- Pole sum beyond the rectangle (n ≥ UV) = h_U h_V; small×small floor − dens_U dens_V n bounded by product of masses.
- NORMAL FORM: for fixed U, V, 0 < ε < 1, every packet: packet − w₃·interior − (linear mean)·n − (smooth mean = c_ε h_U h_V (w₃ − w₂))·n^{1−ε} has bounded pronic norm. Two explicit obstructions to admission: linear drift and smooth power n^{1−ε}; plus the receiver (interior) direction w₃. If w₂ = w₃ and linear mean 0: |packet − w₃·interior| ≤ floor budget pointwise.
- Linear and smooth means 0 ⇒ (admitted ⇔ w₃ = 0 or interior has bounded pronic norm). Admission ⇒ linear mean 0 (Gram/T → mean²). Paid directions: e₀ + (dens_U/Re D)e₄ and e₁ + (dens_V/Re D)e₄ always admitted (pole leg compensates small leg's linear mean). If w₂ = w₃ and linear mean 0: w = (w₀−w₃)·paid₁ + (w₁−w₃)·paid₂ + w₃·1.
## VaughanPacketsHaveAnExactResidualEnergyDensity
- 0 < ε < ½: interior pronic energy / T^{1−2ε} → 0 (VK: energy ≤ C T^{1−2ε} exp(−κ·vkScale/270)). Smooth power n^{1−ε}: ‖·‖²_T/T^{1−2ε} → 1/(1−2ε).
- Centred packet: ‖packet − mean·n‖²_T / T^{1−2ε} → (smooth mean)²/(1−2ε); pairings by polarization; centred Gram/T^{1−2ε} → (c_ε h_U h_V)²/(1−2ε)·s_i s_j with smooth signs s = (0,0,−1,1,0) (second rank-one scale).
- Centred large-leg Gram at covering horizon T < (U+1)(V+1) = mean₃²·‖n‖²_T; at square cutoffs = ζ(1+ε)²(Re D − dens_N)⁴‖n‖².
- EXACT ADMISSION CLASSIFICATION (0<ε<½, fixed U, V): admitted ⇔ linear mean = 0 ∧ smooth mean = 0 ∧ (w₃ = 0 ∨ interior bounded). For U, V ≥ 1 (h_U ≠ 0, c_ε ≠ 0): smooth mean = 0 ⇔ w₂ = w₃. With w₃ = 0: admitted ⇔ linear mean = 0 ∧ w₂ = 0. Second-scale density (c_ε h_U h_V)²/(1−2ε) > 0.
## TheAdmittedVaughanCoefficientSpace (start)
- Admitted coefficient vectors form a submodule of ℝ⁵. Paid frame (2 vectors) and full frame (paid + all-ones receiver) are linearly independent. If interior is NOT bounded: admitted submodule = span(paid frame) (dimension 2).
- If interior bounded: admitted = span(full frame), dim 3. dim admitted = 3 ⇔ interior bounded ⇔ quotient dim 2. Unique coordinates (w₀−w₃, w₁−w₃, w₃). Finite-dimensional linear-algebraic RECAST of the interior-boundedness question (interior bounded at ε ⇔ RH-type statement for ε < ½); does not decide it.
## VaughanAdmissionAtHalfDamping
- ε ≥ ½: interior pronic norm bounded (from discrete energy budget). ‖√n‖²_T = Σ1/(n+1) → ∞ (√n not admitted). ε = ½: admitted ⇔ linear mean 0 ∧ smooth mean 0 ⇔ (U,V ≥ 1) linear mean 0 ∧ w₂ = w₃; admitted = span(full frame), dim 3, quotient dim 2.
## VaughanAdmissionAboveHalfDamping
- ε > ½: Vaughan majorant τ(d)²d^{−ε} in critical Wiener algebra (Σ|g|d^{−½} < ∞) ⇒ centred floor prefix pronic norm ≤ (√2+1)·mass(ε−½), uniform. All five centred pieces and all packets uniformly bounded (≤ B Σ|w_i|). Admitted ⇔ linear mean 0; admitted = ker(mean functional), dim 4, quotient dim 1 (pole coordinate gives −Re D ≠ 0).
- Phase diagram of admitted dimension: ε > ½: 4; ε = ½: 3; 0 < ε < ½: 3 iff interior bounded, else 2.
## ZeroVaughanCutoffsRemoveTheSmoothObstruction (start)
- U = 0 or V = 0 ⇒ small×small piece, its mean, smooth mean vanish; admission ⇔ linear mean 0 ∧ (w₃ = 0 ∨ interior bounded).
## TheZeroCutoffVaughanCoefficientSpace
- Empty cutoff: unused small×small coefficient e₂ is admitted (zero packet). Admitted = span(paid₁, paid₂, e₂) (dim 3) if interior unbounded; + receiver (dim 4) if bounded. dim 4 ⇔ interior bounded ⇔ quotient dim 1. ε = ½: admission ⇔ linear mean 0; dim 4.
## TheVaughanAdmissionRankReadsTheZeroAbscissa
- Baseline rank = 3 if U=0 ∨ V=0 else 2. For every ε > 0: rank ≥ baseline + 1 ⇔ interior has bounded pronic norm ⇔ bounded interior energy. Rank-damping set = interiorReceiverDampings = receiverDampings, independent of (U, V).
- sInf(derived set of rank dampings) = Θ − ½ (zeta zero abscissa). Θ < 1 ⇔ boundary < ½. RH ⇔ 0 is an accumulation point ⇔ cofinal extra rank near 0 ⇔ extra rank at every ε > 0. Extra rank ⇔ first damping column square-summable ⇔ all columns square-summable. (RH REFORMULATIONS — finite-dimensional rank readout of the receiver; trap: not a proof route by itself.)
## TheCentredVaughanPoleHasPositiveFiniteEnergy
- Active-pair first increment = 2^{−ε}/4 > 0; first cell energy (2^{−ε})²/32. Centred pole Gram (4,4) = active-pair pronic energy, cutoff-independent; converges to L ∈ [(2^{−ε})²/32, ¼]. ⇒ normalized centred Gram cannot decay faster than T^{−(1−2ε)}: positive finite pole cell obstructs faster power decay.
## TheVaughanLimitRowsAreIndependentInTwoCells (start)
- Re D = 1/ζ(1+ε) ≤ Π_{p∈S}(1 − p^{−1−ε}) for every finite prime set S.
- Re D ≤ (1 − 2^{−ε}/2)(1 − 3^{−ε}/3). Active component at prime p = ½p^{−ε}(1 − 1/p). Centred prefix cell 2 = 2 − 2^{−ε} − 2Re D; active increment 2 = 3^{−ε}/3 − 2^{−ε}/4.
- Two-cell determinant of (centred prefix, centred pole) ≥ (2^{−ε})²/36 > 0 (Euler bound at p = 2, 3 + polynomial positivity) ⇒ linearly independent. Pronic Gram determinant ≥ (f₁g₂ − g₁f₂)²/12 (Lagrange identity restricted to two cells) ⇒ prefix–pole Gram det ≥ (2^{−ε})⁴/15552 at every T ≥ 2.
- Limit frame (cutoffs → ∞): rows (P, P, −P, 0, −Δactive) with P = centred prefix; span = span(P, pole), dimension exactly 2 for ε > 0.
## MovingVaughanRowsConvergeCellByCell
- U, V → ∞: each centred piece converges cellwise to the limit frame (small legs → P once U ≥ n; large leg → 0 once n < UV; pole constant; small×small → −P from the sum identity). h_U → 0 ⇒ smooth-subtracted rows same limits.
## UniformHalfDampingVaughanGramsHaveAnActualLimit
- ε = ½: one summable pair envelope for all remainders ⇒ limit Gram entries absolutely summable; moving remainders → limit frame in full pronic norm and at any moving horizon; centred Gram − (c_½ h_U h_V)² s_i s_j Σ1/(n+1) → actual infinite limit Gram (cross terms a_k·M_l → 0 since h_U → 0).
## UpperHalfVaughanGramsHaveAnActualLimit (start)
- ε > ½: envelope E(n) = 4|centred floor prefix of τ²d^{−ε} majorant| + 1, pronic norm ≤ 4(√2+1)mass(ε−½) + 1; dominates every centred Vaughan row cellwise.
- ε > ½: one summable square envelope for all centred rows; centred Gram → actual infinite limit Gram (independent H, U, V → ∞); rows → limit frame in full pronic norm and at any moving horizon.
## TheVaughanFloorCoefficientsConvergeInCriticalWienerNorm
- n ≤ U, V ⇒ (μ_U*μ_V*ζ)(n) = μ(n). ε > ½: μ_U(d)d^{−ε} → μ(d)d^{−ε} and −(μ_U*μ_V*ζ)(d)d^{−ε} → −μ(d)d^{−ε} in critical Wiener norm Σ|·|d^{−½} (dominated convergence with τ² majorant).
## TheActualVaughanLimitGramHasRankTwo
- ε ≥ ½: limit Gram entries summable, symmetric, PSD. Limit Gram = (1,1,−1,0,0)⊗row₀ + e₄⊗row₄ ⇒ rank ≤ 2. Prefix–pole minor ≥ (2^{−ε})⁴/15552 ⇒ 2×2 submatrix PD ⇒ rank exactly 2. Pole energy ≥ (2^{−ε})²/32.
## TheActualEndpointVaughanGramHasRankTwo
- ε = ½ specialization: minor ≥ 1/62208, pole energy ≥ 1/64, Gram ≠ 0, rank 2.
## TheHalfDampingVaughanGramLimitsFormARankThreeRay (start)
- Harmonic mass ℓ(U,V,T) = (c_½ h_U h_V)²Σ_{n≤T}1/(n+1) ≥ 0. Limit ray R(ℓ) = G + ℓ·s⊗s (s = (0,0,−1,1,0)). Large row of G is 0; R(ℓ)₃₃ = ℓ. If ℓ(U_t,V_t,H_t) → ℓ then centred Gram → R(ℓ). Centred Gram₃₃ − harmonic mass → 0.
- Centred Gram₃₃ → ∞ ⇔ harmonic mass → ∞. Any finite joint limit L forces mass → L₃₃ ≥ 0 and L = R(L₃₃). Finite endpoint limits ⇔ mass converges. R(0) = G (rank 2); ℓ > 0 ⇒ rank R(ℓ) = 3 (minor on {0,4,3} = ℓ·det ≥ ℓ/62208).
## ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits
- Σ_{n≤UV}1/(n+1) ≤ (1+log U)(1+log V). Mass(U,V,UV) ≤ c²·w(U)w(V), w(N) = h_N²(1+log N) → 0 (log·h_N → 0). ⇒ mass at product horizon → 0 uniformly in factorization; uniformly bounded; centred Gram at T = UV uniformly bounded; U, V → ∞ ⇒ Gram(U,V,UV) → G (rank 2).
## EveryNonnegativeEndpointVaughanLimitIsRealized
- h_N ≠ 0 for N ≥ 1 ⇒ positive vanishing scales; choose H to realize any ℓ ≥ 0. Joint finite limits (H, U, V → ∞) = exactly the nonnegative ray {R(ℓ) : ℓ ≥ 0}.
## TheExtremeVaughanCutoffReadsItsHarmonicSum
- dens_1 = 1; cutoffs (1, V ≥ n): small×small piece = −n; centred large piece = (Re D − 1)·centred small×small piece ⇒ Gram₂₃ = (Re D − 1)Gram₂₂. Residual error contrast E₂₃ − (Re D − 1)E₂₂ = Re D·(c_ε h_T)²/(1−2ε) > 0. Frequent harmonic floor (h_T² ≥ a/T i.o.) ⇒ contrast·T ≥ c i.o.; NOT o(1/T); errors E₂₂, E₂₃ cannot both be o(1/T), nor both O(T^{−δ}) with δ > 1.
- Abel inversion: |h_n| ≤ K n^{−η} ⇒ |M(N)| ≤ K(2 + 1/(1−η))N^{1−η} ⇒ Θ < 1 (power decay of harmonic Möbius sums gives a zero-free strip).
## UniformVaughanPowerBoundsAreFixedStrips
- Unit/full cutoffs: undamped prefix(1, n, n) = 1 ⇒ |1 − n h_n| ≤ error. Mertens power |M(n)| ≤ B n^{1−η} ⇒ uniform undamped Vaughan error ≤ C n^{1−κ} for every κ < η/(2+η) (split D = n^{1/(2+η)} balances head D² against tail n·D^{−η}).
- EQUIVALENCE: Θ < 1 ⇔ ∃ η > 0 uniform (in U, V) power bound |prefix − n h_U h_V| ≤ C n^{1−η}. (Strip reformulation; not unconditional.)
## PowerCancellationSurvivesTheDampedFloorTransform
- Divisor-square-bounded s with Σ_{d≤x}s ≤ B x^{1−κ}: damped floor transform centred prefix ≤ K n^{1−ε−γ} for every γ < κ(1−ε)/(1+κ) (split at n^{1/(1+κ)}: head ≤ C D^{1−ε}(1+log D)⁴, tail ≤ (13/ε)B D^{−κ−ε} n). Prefix power ⇒ pronic norm ≤ K√(1 + 1/(1−2(ε+γ)))·√(T^{1−2(ε+γ)}); linear bound absorbs finite head.
## FixedStripsControlAllVaughanFluctuationReceivers (start)
- Mertens power bound transfers to every truncation μ_U. Bounded patterns with common power cancellation ⇒ common improved pronic norm power. Uniform undamped Vaughan power ⇒ damped convolution fluctuation norm ≤ C√(T^{1−2(ε+γ)}). CONDITIONAL on Θ < 1: one γ > 0 saving for all Vaughan fluctuation sources, truncated pattern prefixes, and interior.
## UniformVaughanResidualPowerRatesAreFixedStrips
- Θ < 1 ⇒ ∃ γ > 0 with all five smooth remainders ‖r_i‖_T ≤ B√(T^{1−2(ε+γ)}) uniformly in U, V ⇒ residual Gram error |Gram/T^{1−2ε} − (c h_U h_V)²s_i s_j/(1−2ε)| ≤ C T^{−γ} uniformly. Converse: power bound on the two extreme-cutoff entries E₂₃, E₂₂ ⇒ h_T² ≤ B T^{−δ} ⇒ Θ < 1.
- EQUIVALENCE (0 < ε < ½): Θ < 1 ⇔ uniform power rate in the full residual Vaughan Gram law.
## FactorialOrderOneInTheVaughanConvolutionIsAPowerSaving
- Common-threshold factorial log envelope |err|·(log n)^q ≤ C A^q q! n ⇔ uniform power saving ⇔ Θ < 1. (Unconditional result has factorial order 3: (3q)!, see stretched rate.) Order-one factorial growth = strip; trap: order 3 → 1 is the whole strip problem.
## SignedVaughanTailsVanishAtTheirAbsoluteScale
- Re D − dens_N = Σ_{d>N}μ(d)d^{−1−ε} (signed reciprocal tail). Mean-zero bounded pattern ⇒ N^ε·tail → 0 (o of absolute scale); |N^ε·tail| ≤ 2 + 1/ε. Bounded vanishing f: f(U)f(V) → 0 whenever UV → ∞ (one of U, V large). ⇒ product of scaled Möbius tails → 0 at divergent product horizon.
## UniformTruncatedMobiusReceiversHaveZeroTrivialDensity (start)
- Common mean-zero partial-sum modulus over a family ⇒ common damped pattern prefix modulus θ n^{1−ε} eventually.
- Σ_{d≤x}μ_U(d) = M(min(U,x)) ⇒ all truncations share one mean-zero modulus (|·| ≤ ηx for x ≥ X(η), uniformly in U). ⇒ truncated pattern prefixes ≤ θ n^{1−ε} uniformly; pattern receivers/T^{1−2ε} → 0 uniformly ⇒ arbitrary moving truncations at any divergent horizon have zero trivial density. Centred small leg = pattern prefix of μ_U; Σ μ_U(d)d^{−1−ε} = dens_U.
## ProductHorizonVaughanGramsHaveZeroTrivialDensity
- ‖n‖²_T ∈ [T/2, T]. Product horizon T = UV: centred large-leg Gram/T^{1−2ε} ≤ ζ(1+ε)²·((U^ε tail_U)(V^ε tail_V))² → 0. All five centred norms are o(√T^{1−2ε}) at product horizons (small legs via uniform truncation estimate, pole bounded, interior via VK, small×small via sum identity). |Gram_{ij}| ≤ trace (Young). Trace/T^{1−2ε} → 0 with one threshold for all factorizations; bounded moving packets too; any aspect ratio U/V allowed.
## VaughanReciprocalTailPowerGainsAreFixedStrips (start)
- tail_N := Re D − dens_N; (N+1)^{1+ε}(tail_N − tail_{N+1}) = μ(N+1) (Abel inversion recovers Möbius).
- Abel: M(N) = tail₀ − (N+1)^{1+ε}tail_N + Σ_{n≤N}((n+1)^{1+ε} − n^{1+ε})tail_n; increment ≤ (1+ε)2^ε n^ε. ⇒ |tail_n| ≤ K n^{−ε−η} ⇒ |M(N)| ≤ C N^{1−η} ⇒ Θ < 1. Conversely Mertens rate β ⇒ |tail_N| ≤ (2+1/ε)C N^{−ε−(1−β)}.
- EQUIVALENCE (every ε > 0): Θ < 1 ⇔ reciprocal-tail power gain beyond N^{−ε}.
## TheEmptyVaughanLegDetectsAFixedStrip
- Square horizon N², cutoffs N: centred large-leg energy/(N²)^{1−2ε} ∈ [ζ²/2, ζ²]·(N^ε tail_N)⁴. ⇒ Θ < 1 ⇔ power saving C N^{−δ} in normalized empty-leg energy (δ = 4η).
## VaughanTailPowerGainsAtEveryPositiveDamping
- Same equivalences for all ε > 0 (increment bound via mean value).
## TheVaughanEmptyLegReadsTheZeroAbscissa (start)
- |M(n)| ≤ C n^β ⇒ Θ ≤ β; β > Θ ⇒ such C exists. Tail gain η ⇒ Θ ≤ 1 − η; every η < 1 − Θ realized. Tail-rate set ⊂ [0, 1−Θ], contains [0, 1−Θ); 0 always a rate (|N^ε tail| ≤ 2+1/ε). Θ = 1 ⇒ rate set = {0}. Optimal tail decay index = 1 − Θ (zero-abscissa readout).
- Tail decay index = sup(rate set) = 1 − Θ, independent of ε > 0. Square-energy rates (cutoff variable): δ ∈ set ⇔ δ/4 tail rate; index = 4(1 − Θ). Horizon-variable index = 2(1 − Θ). Index > 0 ⇔ Θ < 1. RH ⇔ tail index = ½ ⇔ square index = 2 ⇔ horizon index = 1 ⇔ all strict tail gains η < ½ ⇔ all strict square energy gains δ < 2. No tail gain > ½ and no square energy gain > 2 (Θ ≥ ½). Positive tail rate η ⇔ Mertens bound N^{1−η}; full rate sets independent of damping.
## VaughanEndpointScalesHaveUnavoidableOscillation
- Eventual tail bound δ N^{−ε−½} ⇒ |M(N)| ≤ C + Kδ√N. With M(x) = Ω±(√x) (mertens_omega_pm_sqrt): ∃ c > 0, i.o. |N^{ε+½} tail_N| > c; scaled tail ↛ 0. Square empty-leg energy > c N^{−2} i.o.; N²·energy ↛ 0. Endpoint scales are attained only with oscillation (no o-improvement at the RH endpoint).
## VaughanEndpointRatesForceSimpleBoundaryZeros (start)
- Attained Möbius power bound |M(n)| ≤ C n^β (β < 1) caps the order of every zeta zero on Re s = β at 1 and bounds its local factor: 1 ≤ 4C·polylogConst·|ρ|·|p(ρ)| (one-sided Mertens frontier oscillation). Attained positive tail rate η ⇒ every zero on Re s = 1 − η is simple. Endpoint tail rate ½ (or square energy rate 2, horizon rate 1) attained ⇒ RH AND all critical zeros simple. (Endpoint attainment is stronger than RH.)
## LinearBandVaughanTypeIIBilinearEstimate
- typeIIShort V vanishes on [1, V] and = −sieveSeq V μ beyond ⇒ Type-II piece vanishes when B−1 ≤ L ≤ V; otherwise restricts to m ∈ (V, L]. Linear band effHigh(B,P) ≤ (K+1)V ⇒ effective-set short energy ≤ K²(effHigh − V) ≤ K²B/P (log-free, replaces 2(B/P)(1+(1+log B)³)). Nonzero dyadic block of typeIILong U has P ≥ U/2+1 ⇒ if effHigh(B, U/2+1) ≤ (K+1)V every active block is in the band ⇒ log-free hybrid Vaughan Type-II estimate (√(4CK² log L) × root envelope, summed over log₂L + 1 dyadic blocks).
## KloostermanTerminalBlockAndGlobalFrequencyCollision (start)
- Global cross-phase frequency fibre over z has ≤ gcd(q+1, r+1) elements (injective gcd-slice label).
- Fibre Cauchy–Schwarz + Parseval: Σ_z |pair coefficient(q,r,z)|² ≤ gcd(q+1,r+1)|w_q|²|w_r|²·E_res(q)E_res(r). Global frequency collision energy ≤ |Q|²·Σ_{q≠r} gcd·|w|²|w|²E_res E_res (unconditional). Terminal Gram quadratic² ≤ that × (period·(M mod period) − (M mod period)²). Type-II short source on linear window N ≤ (K+1)V: interval source budget/residue energy ≤ (q+1)·mult(q,N)·K²(N−V) (log-free).
## LinearBandPowerEnvelopeAndChiralKloostermanCollision (start)
- Kubalalika root power ≤ 64√(1+log B)·(B^{3/2}(Tr)^{−½} + B V^{−½} + (Tr)^{¼}B^{¾}U^{−½} + B U^{−½}). Linear-band Type-II piece envelope ≤ 256√C·K(1+log B)²·(same sum) — saves two log powers vs (1+log B)⁴. Mixed second/third-derivative von Mangoldt block sum Σ_{A≤n<B}Λ(n)e(phase) ≤ (1.2·10⁶ + 256√C K)(1+log B)²·(A^{1/3}(Tr)^{1/6}√(UV) + four Type-II terms) under linear-band and curvature conditions.
- Real source on prime-clock family: global collision energy = 2Σ_{q≠r}|w_q|²|w_r|²·(unit Fourier energy q)(unit Fourier energy r) (exact, no |Q|² loss); linear-band ⇒ product of (q+1)mult·K²(N−V) bounds.
- Common-period average of squared total-response mass defect = global collision energy ⇒ same linear-band log-free bound.
## DifferentiatedBarbanVehovKernelsAndSmoothPrimeSigmaRate (bridge wrapper)
- Squarefree r: |coprimeLogMoebius(r,Y) − r/φ(r)| ≤ C(r/φ(r))/log²(Y/D) + (7+|γ|)D^{−¼}4^{16}σ_{−½}(r). Long Barban–Vehov kernels = (1/lcm(q,r))·harmonic log window moments m = 0,1,2 (with log(lcm/q), log(lcm/r) shifts). Omitted-head base/cross/derivative polynomial mains = Selberg coefficient min-log quadratic forms in A = log(M/p₁), B = log(M/p₂), u = min(A,B). Thresholded Selberg–Möbius sums at ratio N/q = shifted log kernels; zero-twist mollified diagonal = product-fibre Gram energy Σ|coefficient|².
## OffMultipleDecimationSieveAndPNTPlusMobiusAsymptotics (bridge wrapper)
- Decimation inverts inflation; off-multiple prime sieve = Σ_{d|P#}μ(d)S_d D_d; Σ μ(d)/d = sieve density; L(E_q b, s) = L(b,s) − q^{−s}L(D_q b, s); Euler-density scale law for characterful functionals. Σμ(n)n^{−σ} = 1/ζ(σ) (σ > 1); Euler clock mean; mollification by probability density is L² contraction. PNT+: Σ_{n≤x}μ(n)⌊x/n⌋ = 1; floor tail o(x); Σμ(n)/n = o(1); Liouville o(x); Chebyshev in APs.
## SquarefreeResidueInversionAndCofactorRadicalSupport (start)
- Ramanujan residue inverse preserves multiple-vanishing and squarefree support. Squarefree-supported c: c(d) = μ(d)·(μ(d)c(d)). Route PM cofactor weight (and its real part) vanishes off squarefrees (in particular if 4 | d). Cofactor sieve sequence: sieveSeq(dk) = sieveSeq(k) for d | k; invariant under powers and p^{a+1}u ↦ pu; depends on k only through its radical (prime support).
## PhaseUniformWindowSandwichAndQuadraticObservabilityHorizon
- Row shift c − κ·δ₁ shifts response by −κ, H by −κ, leaves variance V. Q_Sel(shift) = (H − κ)² + V. Window: |Σ_{A<k≤A+K}s(k)² − K·Q_Sel| ≤ ‖c‖₁² (lcm fractional defect moves ≤ ‖c‖₁²), at every phase A.
- Finite Ramanujan inversion: c(d) = d Σ_{m≤N/d}μ(m)Y(dm). ⇒ ‖c‖₁ ≤ Σ_q σ(q)|Y(q)|; Cauchy–Schwarz ⇒ ‖c‖₁² ≤ S_N·Q_Sel, S_N = Σ_{q≤N}σ(q)²/φ(q). σ(q)² ≤ κ(q) q d(q) φ(q), κ ≤ 27/4 (losses only at 2, 3); Σd(q) ≤ N(1+log N) ⇒ S_N ≤ (27/4)N²(1+log N).
- Phase-uniform sandwich |Σ_W(s−κ)² − K Q| ≤ S_N Q. Constant response on a window of length K > S_N ⇒ V = 0 and H = κ. Vanishing prefix discrepancy on K+1 > S_N + 1 consecutive prefixes ⇒ V = 0 (quadratic observability horizon (27/4)N²(1+log N), replacing exponential lcm(1..N) windows; does not reach conjectured linear horizon 2N − 3).
## PhaseUniformWindowPoincareAndLongWindowDissipation (start)
- Successor reserve R = Σ_{e≥2}(φ(e) − μ(e))Y(e)², blind to unit shift; V/2 ≤ R ≤ 2V (2μ(q) ≤ φ(q), q ≥ 2). Window successor correlation = K·Q_Bez ± 2‖c‖₁²; window Dirichlet energy = squares − 2·correlation, shift-invariant; ‖centred row‖₁² ≤ S_N V.
- Window reserve sandwich |D_W − 2K R| ≤ 6 S_N V; (K − 6S_N)V ≤ D_W ≤ (4K + 6S_N)V. Window Poincaré Σ_W(s − H)² ≤ D_W + 7 S_N V (torus constant 1 up to 7S_N V; multiplicative form for K > 6S_N). Long-window dissipation 2R_W ≤ 4H² − (K − 11S_N)V; in ker P (H = 0) every window longer than 11 S_N with V > 0 is strictly dissipative at every phase. No information below the polynomial horizon.
## QuadraticWindowHorizonSharpnessAtCommonReturns
- Any window sandwich constant S at level N satisfies (N − 1 − log N)² ≤ (1+S)(1+log N)³ ⇒ S ≥ N^{2−o(1)}. Witness: all-ones row (response d_N(k)), Q_Sel ≤ H_N³ (Y(e) ≤ H_N/e), value N at N! (divisor spike). Inverse ℓ¹ constant C ≥ N²/(1+log N)³. ⇒ quadratic horizon is SHARP for mean-square window–period transfer; linear observability horizon 2N − 3 (if true) is qualitative, invisible to window mean-square comparison. (TRAP: no improvement of sandwich constants reaches linear horizon.)
## PolynomialWindowTranslatedMomentTransfer
- Joint incidence {k : d_i | k + h_i ∀i} is empty or one class mod lcm(d) (CRT) ⇒ window count within 1 of K/N!·period count. Translated moment of degree m: |Σ_W Π s(k+h_i) − K T(h)| ≤ ‖c‖₁^m ≤ (S_N Q_Sel)^{m/2}; centred version with (H−κ)² + V. Every complete-period observation is available to relative accuracy δ from one window of length (S_N Q)^{m/2}/δ at arbitrary phase (polynomial instead of N!).
## PolynomialHorizonRecoveryFromArbitraryPhaseWindows (start)
- Cov(g) = Σ_{2≤e≤N} c_e(g)Y(e)² (Ramanujan sums). Lag Möbius inversion: Σ_{ab=f}μ(a)c_e(b) = fμ(e/f)[f|e]; Y(q)² = Σ_{u≤N/q}(qu)^{−1}Σ_{ab=qu}μ(a)Cov(b) — all Selberg energies from lags 1..N, stability constant H_N² ≤ (1+log N)².
- Lag readout stable: lag data within η ⇒ each Y(q)² within H_N²η (Σ d(f)/f ≤ H_N²). Window lag covariance within S_N V/K of period covariance ⇒ Selberg energies recovered within H_N² S_N V/K from one window at arbitrary phase. Fifth and sixth window moments of two rows at unrelated phases A, B agreeing within Kη (with η + (‖c‖₁^m + ‖e‖₁^m)/K ≤ δ³) ⇒ rows agree up to translation within 2(Σφ(q))δ (top-anchor stability, unit top-order coordinate). Constants of complete-period theorems unchanged.
## TranslatedMomentTransferHierarchySharpness
- Degree-m transfer constant S_N^{m/2} suffices; top-band row 1_{(N/2,N]}: Q_Sel ≤ H_N³, response M₀ = N − ⌊N/2⌋ at N!, period m-th moment ≤ M₀^{m−2}Q_Sel ⇒ any constant S satisfies M₀^m − H_N³M₀^{m−2} ≤ S(√H_N³)^m ⇒ S = N^{m−o(1)}. Degree-m observations need windows N^{m±o(1)}; sixth-moment protocols need N^{6−o(1)}; NO moment-transfer argument reaches a linear horizon (TRAP).
## MultiLagCovarianceConeFiniteGeneration (start)
- Ramanujan lag weight c_e(j) multiplicative in e. c_e(j) = 0 if e/gcd(e,j) not squarefree. h-smooth part g = gcd(e, (h!)^e), rough part r = e/g coprime to h!. Smooth part not dividing (h!)² ⇒ invisible to all lags 1 ≤ j ≤ h.
- Rough part r ≥ 2 coprime to h!: φ(r) ≥ p_h − 1; if μ(r) = 1 then φ(r) ≥ (p_h − 1)(p_h' − 1) (two primes beyond h). Lags 1..h see rough part only through μ(r): c_{gr}(j) = μ(r)c_g(j); c_e(0) = φ(e).
- FINITE GENERATION: generator set G_h = {g ≥ 2 : g | (h!)²} ∪ {g·p_h : g | (h!)²} ∪ {p_h p_h'}. Variance direction (1,0,..,0) in cone (via p_h and p_h p_h'). Smooth g ≥ 2 absorbs rough r: v_{gr} = (μ(r)+b)v_g + b v_{g p_h}, b = (φ(r)−μ(r))/p_h ≥ 0. Every mode vector, hence every row's covariance profile (Cov(0..h)) at every cutoff, lies in the cone of G_h. Every generator is realized by a row (Ramanujan residue inverse). Universal linear lag inequality Σα_j Cov(j) ≥ 0 ⇔ holds on generators (finite certificate). h = 1: G = {2, 6}; criterion α₁ ≤ α₀ ∧ 2α₀ + α₁ ≥ 0. h = 2 contains {2,3,4,6,12}.
## CyclotomicIncidenceRecurrenceAndArbitraryPhaseObservability (start)
- Unit shift E; Q_N = Π_{q≤N}Φ_q (monic, degree Φ(N) = Σφ(q), 2Φ(N) ≤ N(N+1)). E^d − 1 = Π_{q|d}Φ_q kills d-periodic sequences ⇒ Q_N(E) kills every level-N response and every prefix discrepancy (sawtooth combination). Monic recurrence + vanishing on deg p consecutive values ⇒ vanishing forever after.
- Responses N!-periodic; response zero on [1,N] ⇒ row zero on [1,N]. ARBITRARY-PHASE OBSERVABILITY: response vanishing on Φ(N) consecutive integers (any phase A) ⇔ row zero; discrepancy vanishing on Φ(N) consecutive ⇔ V = 0. Horizon Φ(N) ≤ N(N+1)/2 (no log), vs lcm window and N² log N sandwich; not sharp (2N − 3 at common returns). MINIMALITY: any polynomial killing all level-N responses is divisible by Q_N (shifts of [d|·] are the d residue indicators) ⇒ degree ≥ Φ(N).
## SelbergSupportExactRecurrenceComplexity
- Σ_{ζ^d=1}ζ^k = d[d|k] ⇒ s(k) = Σ_{ζ∈T_N} Y(ord ζ)ζ^k (roots of unity of order ≤ N). P(E)s(n) = Σ Y(ord ζ)P(ζ)ζ^n. Characters linearly independent (Dedekind) ⇒ P(E) kills s ⇔ Π_{Y(q)≠0}Φ_q | P. Minimal recurrence = Π_{q∈supp Y}Φ_q; RECURRENCE COMPLEXITY = Σ_{Y(q)≠0}φ(q) (totient mass of Selberg support). Support class S: Σ_{q∈S}φ(q) consecutive values at any phase determine row; single Selberg mode q needs φ(q).
## TrapezoidWindowSandwichAtQuadraticOrder (start)
- Nontrivial m-th root of unity at circle distance ≥ 1/m from 1 ⇒ response frequencies (orders ≤ N) are 1/N²-separated (Farey). δ-separated family: Σ_{t≠r}1/dist² ≤ 4/δ² (no log). Trapezoid kernel = product of two geometric sums.
- Trapezoid-smoothed dual large sieve: δ-separated unit frequencies ⇒ |Σ_{i<L}Σ_{j<K}|Σa(ζ)ζ^{T₀+i+j}|² − LKΣ|a|²| ≤ Σ|a|²/δ² at every phase (off-diagonal kernel ≤ 1/(4 dist²) via geometric sums, AM–GM). Response frequencies (δ = 1/N²): error ≤ N⁴Σ|a|²; Σ_ζ Y(ord ζ)² = Σφ(q)Y(q)² = Q_Sel. Box window squeezed between trapezoids with ramps L = N²: |Σ_W|Σaζ^k|² − KΣ|a|²| ≤ (2N² − 1)Σ|a|².
- WINDOW SANDWICH AT QUADRATIC ORDER: |Σ_W s² − K Q_Sel| ≤ (2N² − 1)Q_Sel, any offset κ ⇒ sandwich constant 2N² − 1 (removes log); lower bound N²/(1+log N)³ ⇒ optimal constant N^{2+o(1)}.
## UniformLagWindowCovarianceAtQuadraticOrder
- Σ_{ζ primitive of order q}ζ^g = c_q(g) (Ramanujan sum = power sum of primitive roots; induction on divisors). Σ_{ζ∈T_N}f(ord ζ)ζ^g = Σ_q f(q)c_q(g). Polarization (s'(k) ± s'(k+g) with coefficients Y(1 ± ζ^g)): |Σ_W(s−H)(s(·+g)−H) − K Cov(g)| ≤ (2N² − 1)V uniform in lag g. Normalized window covariance within (2N²−1)V/K; lag readout within H_N²(2N²−1)V/K.
## QuadraticOrderWindowDirichletAndDissipation (start)
- Cov(1) = Σμ(e)Y(e)² = V − R. Window Dirichlet |D_W − 2KR| ≤ 4(2N²−1)V; (K − 4S)V ≤ D_W ≤ (4K + 4S)V, S = 2N² − 1.
- Window Poincaré Σ_W(s−H)² ≤ D_W + 5(2N²−1)V. Sup bound (s(k) − H)² ≤ (Φ(N) − 1)V (|c_q(k)| ≤ φ(q), Cauchy–Schwarz). Long-window dissipation 2R_W ≤ 4H² − (K − 10N²)V; ker P windows longer than 10N² strictly dissipative.
## FlatSelbergRowAndExactQuadraticSandwichOrder
- s(N!) = Σφ(q)Y(q). Flat Selberg row (Y = 1 on [2,N], Y(1) = 0): H = 0, V = Φ(N) − 1, s(N!) = Φ(N) − 1 — attains pointwise bound (exact constant Φ(N) − 1). Every sandwich constant ≥ Φ(N) − 2. Σ_{k≤N}Φ(⌊N/k⌋) = N(N+1)/2 ⇒ Φ(N) ≥ N²/8 + N − (N/2)H_N. Optimal sandwich constant ∈ [N²/8 + N − (N/2)H_N − 2, 2N² − 1]: EXACT ORDER N².
## CanonicalPrimitiveSpectralFormAndJordanWindowEnergy
- Parseval over full period P (frequencies P-th roots): Σ_{k<P}|Σa ζ^k|² = PΣ|a|². Canonical primitive W(k) = −Σc(d)ψ_d(k) (zero-mean, W(k+1) − W(k) = s(k+1) − H) = Σ_{ζ≠1}Y(ord ζ)·ζ/(ζ−1)·ζ^k. Coefficient energy = primitive energy E; 12E = Σ_{q≥2}J₂(q)Y(q)². Window: |Σ_W W² − KE| ≤ (2N²−1)E; pointwise W² ≤ (Φ(N)−1)E. Prefix discrepancy = W(M) − W(0) ⇒ same window law for L_N(M,c) + W(0).
## LogFreeLargeSieveFromWindowSandwich (start)
- Dual sums over response frequencies: Σ_W|Σ_{ζ∈T}a ζ^k|² ≤ (K + 2Q² − 1)Σ|a|². Duality principle transfers same constant to primal sums.
- LOG-FREE LARGE SIEVE (unconditional): Σ_{ζ∈T}|Σ_W x(k)ζ^k|² ≤ (K + 2Q² − 1)Σ|x|² for T ⊆ roots of order ≤ Q. Proper Farey points: Σ|Σ_{n∈A}e(na/q)|² ≤ (N + 2Q² − 1)|A|. Montgomery sieve: |A|Σ_p(p − ω_p)/ω_p ≤ N + 2Q² − 1; sieve bound |A| ≤ (N + 2Q² − 1)/L. Replaces N + Q²(1 + log(Q²/2+1)) and Q² + 4πN; Montgomery–Vaughan N + Q² − 1 reached up to factor 2 on Q².
## LogFreeMultiplicativeLargeSieve
- Initial window n < N version; textbook form Σ_{q≤Q}Σ_{(a,q)=1}|Σc_n e(na/q)|² ≤ (N + 2Q² − 1)Σ|c|². Multiplicative: Σ_{q≤R}(q/φ(q))Σ_{ψ primitive mod q}|Σ_{n<N}c_n ψ̄(n)|² ≤ (N + 2R² − 1)Σ|c|² (Gauss-sum reduction), replacing N + R²(1 + log(R²/2+1)).
## GaloisInvarianceAndTranslationClosureAtEveryLag
- Response coefficients depend only on ord ζ (Galois-invariant). ζ^h constant on primitive q-th roots ⇔ q/gcd(q,2) | h; common value ±1. Translate k ↦ s(k+h) is a response ⇔ every active Selberg order q has q/gcd(q,2) | h; translated row Y(q)·(±1). Lag 1: closed ⇔ Selberg support ⊆ {1,2}. Row space NOT translation-invariant in general.
## MomentSignVisibilityAndZeroProductRelations (start)
- Period-averaged translated moment M_m(c;v) = Σ over m-tuples of response frequencies with Πζ_i = 1 of Π Y(ord ζ_i)ζ_i^{v_i}.
- Multi-characters v ↦ Πζ_i^{v_i} of distinct tuples linearly independent. SIGN VISIBILITY LAW: degree-m moments of Y and εY agree for all shifts ⇔ every zero-product m-tuple of active frequencies has Π ε(ord ζ_i) = 1. Two-point data blind to every sign pattern (ζ₁ζ₂ = 1 ⇒ equal orders). Odd q ≥ 3 with Y(q) ≠ 0: flipping sign of mode q changes a third moment (ζ·ζ·ζ^{q−2} = 1).
## QuadraticOrderL1ObservabilityConstant
- σ(q)φ(q) ≤ q² ⇒ σ²/φ ≤ q(q/φ)³; (q/φ(q))³ = Π_{p|q}(1 + x_p), x_p = (p/(p−1))³ − 1; x_n/n ≤ 6/((n−1)(n−2)) telescopes ⇒ Σ_{q≤N}(q/φ(q))³ ≤ e^{19/2}N ⇒ S_N ≤ e^{19/2}N² (no log). Inverse ℓ¹: ‖c‖₁² ≤ e^{19/2}N²Q_Sel. Unit Selberg row (all Y = 1): Σc = s(N!) = Φ(N), Q_Sel = Φ(N) ⇒ any constant ≥ Φ(N) ≥ N²/8 + N − (N/2)H_N. Exact order N². Degree-m moment transfer error ≤ (e^{19/4}N√Q_Sel)^m.
## ExactOrderOfTheMomentTransferHierarchy (start)
- (e^{19/4}N)^m is a degree-m transfer constant. Unit Selberg row: |s| ≤ Φ(N) everywhere, s(N!) = Φ(N), period m-th moment ≤ Φ^{m−1} ⇒ any degree-m constant S ≥ Φ(N)^{m/2}/2. Exact order N^m: observability horizon of degree-m translated statistics is N^m.
## ArithmeticLargeSieveForSquarefreeModuli
- Parseval over p-th roots: Σ_η|Σb_nη^n|² = pΣ_h|class sum|². Montgomery at a prime (arbitrary complex weights): ((p − c_p)/c_p)|Σb|² ≤ Σ_{η primitive p}|Σbη^n|². Primitive roots of order pq (coprime) = products of primitive roots of orders p, q ⇒ multiplicative: h(q)|Σb|² ≤ Σ_{ζ primitive q}|Σbζ^n|², h(q) = Π_{p|q}(p − c_p)/c_p. LOG-FREE ARITHMETIC LARGE SIEVE: |A|Σ_{q≤Q sqfree}h(q) ≤ N + 2Q² − 1; |A| ≤ (N + 2Q² − 1)/L.
## ParsevalForTranslatedMomentArrays
- M_m(c;v) = Σ_{zero-product tuples}A_c(ζ)Πζ_i^{v_i}, A_c = ΠY(ord ζ_i). Multi-character orthogonality over [0,N!)^m ⇒ Σ_v(M_m(c;v) − M_m(c';v))² = (N!)^m Σ_{Πζ=1}(A_c − A_{c'})². Sign-scaled row: cost Σ(ΠY)²(1 − Πε)²; sign pattern: 4×(energy of odd-ε-weight relations). Visibility is MEASURED (quantitatively) by length-m relations.
## StableRelationSpectrumFromPolynomialWindows (start)
- Window moment within (e^{19/4}N)^m Q_Sel^{m/2}/K of period moment. Windows (arbitrary shift-dependent phases) within η for all shifts ⇒ ‖A_c − A_{c'}‖₂ ≤ η + transfer errors. K ≫ N^m ⇒ N-independent stable recovery of the relation spectrum. Degree 2: ‖A_c − A_{c'}‖₂² = Σφ(q)(Y_c(q)² − Y_{c'}(q)²)².
- Degree 2: zero-product pairs (ζ, ζ^{−1}) ⇒ relation energy = Σφ(q)(Y_c(q)² − Y_{c'}(q)²)² ⇒ stable magnitude profile from polynomial windows.
## TupleStructureFactorsAtSquarefreeModuli
- Tuple response Σ_{h∈H}(s(n+h) − H_c) = Σ_{ζ≠1}Y(ord ζ)(Σζ^h)ζ^n ⇒ tuple variance = Σ_{2≤q≤N}Y(q)²S_q(H), S_q(H) = Σ_{ζ prim q}|Σ_{h∈H}ζ^h|² (structure factor = Montgomery sum). Squarefree q: S_q(H) ≥ k²Π_{p|q}(p − c_p)/c_p ⇒ tuple variance ≥ k²Σ_{q sqfree}h_H(q)Y(q)². Hardy–Littlewood admissible H (misses a class mod every p): h_H(q) ≥ 1/φ(q) ⇒ Var_H ≥ k²Σ_{2≤q≤N sqfree}Y(q)²/φ(q) (multiplicativity over prime factors is new).
## PronicEnergyTailAtTheQuadraticHorizon
- Pronic weight w(k) = 1/(k(k+1)); tail mass Σ_{H<k≤H+n} = 1/(H+1) − 1/(H+n+1). Abel inequality: partial sums of g beyond H bounded by B ⇒ weighted sums ≤ B·w(H+1). ⇒ |Σ_{k>H}W(k)²/(k(k+1)) − E/(H+1)| ≤ (2N²−1)E/((H+1)(H+2)). For H ≥ 4N² − 4: pronic tail ∈ [E/(2(H+1)), 3E/(2(H+1))] — PRONIC ENERGY COERCIVE for primitive energy beyond quadratic horizon (constant ~N^{−2}). Same for centred prefix discrepancy.
## ValuationLawForZeroProductRelationsAndVisibilityDegree (start)
- LAYER LAW: Πζ_i = 1, p prime, a ≥ 1, no order divisible by p^{a+1} ⇒ number of orders on top layer p^a | ord ζ_i is ≠ 1, and even if p = 2 (raise to p^{a−1}R: off-layer killed, on-layer → nontrivial p-th roots; −1 for p = 2). Visible ε at degree m ⇒ some active m-tuple with Πε ≠ 1 obeying layer law at every prime. Top dyadic layer signs invisible to moments of every degree.
- Two modes sharing top dyadic layer, each with private odd prime layer: relative sign invisible to all moments of degree ≤ 5 (private layers need ≥ 2 hence odd weight ≥ 3; dyadic layer forces even total). Modes 2p, 2r (distinct odd primes): seen at degree 6 via ζζζ^{p−2}ξξξ^{r−2} = 1 (ζζζ^{p−2} = −1 for primitive 2p-th root). VISIBILITY DEGREE of {2p, 2r} is exactly 6.
## CompleteClassificationOfZeroProductRelations
- Layer admissibility (every prime p, a ≥ 1, no q_i divisible by p^{a+1}: layer count ≠ 1, even if p = 2). CLASSIFICATION: positive order tuple carries primitive roots with product 1 ⇔ layer admissible (construction prime-by-prime with residue bump; glue coprime prime powers). COMPLETE VISIBILITY LAW: degree-m moment distinguishes Y from εY ⇔ some layer-admissible m-tuple of active orders has Πε ≠ 1 — purely valuation-theoretic.
## CyclotomicLogarithmFormulaForThePronicGram (start)
- Pronic character series: Σ_{M≥1}z^M/(M(M+1)) = 1 + Q(z), Q(z) = (1−z)log(1−z)/z, Q(1) = 0, valid on closed disk (radial continuity). Ramanujan primitive R_q(M) = Σ_{ζ prim q}ζ/(ζ−1)(ζ^M − 1); Σ_ζ ζ/(ζ−1) = φ(q)/2 (a_ζ + a_{ζ^{−1}} = 1) ⇒ mean-centred primitive R_q(M) + φ(q)/2 = Σa_ζζ^M.
- CYCLOTOMIC-LOG FORMULA: mean-centred pronic Gram G^{mc}(p,q) = φ(p)φ(q)/4 + Σ_{ζ prim p}Σ_{ξ prim q}a_ζ a_ξ Q(ζξ) (finite; logs of cyclotomic numbers 1 − ζξ).
## CotangentSawtoothFormOfThePronicGram
- a_ζa_ξQ(ζξ) = (1/(1−ζ) + 1/(1−ξ) − 1)log(1 − ζξ); Re 1/(1−ζ) = ½ on circle ⇒ kernel purely imaginary, log-modulus cancels, only args survive. Im 1/(1−e(x)) = cot(πx)/2; arg(1 − e(y)) = π((y)). ⇒ G^{mc}(p,q) = φ(p)φ(q)/4 − (π/2)Σ_{(a,p)=1}Σ_{(b,q)=1}(cot(πa/p) + cot(πb/q))((a/p + b/q)) — elementary Dedekind–Vasyunin sums in two moduli.
## VasyuninCotangentSumsInThePrimePronicGram
- Hecke distribution relation Σ_{b<q}((y + b/q)) = ((qy)). Vasyunin sum V(h,k) = Σ_{a=1}^{k−1}cot(πa/k)((ha/k)). Primes: G^{mc}(p,q) = (p−1)(q−1)/4 − (π/2)(V(q,p) − V(1,p) + V(p,q) − V(1,q)); V(p,p) = 0 ⇒ G^{mc}(p,p) = (p−1)²/4 + πV(1,p). Pronic Gram of divisor theory = cotangent sums of the Nyman–Beurling (Báez-Duarte/Vasyunin) Gram; (V(q,p), V(p,q)) reciprocity pair.
## ExplicitDilationProfileAtRationalScales
- G^{ec} = C − D(p)D(q), G = C − D(p)D(q) + Λ(p)Λ(q), D(q) = φ(q)/2 − Λ(q). Four-term identity ⇒ dilation profile at prime ratio p/q (p, q ∤ r): √(pq)Φ_r(p/q) = G(pr,qr) + G(pr,r) + G(qr,r) + G(r,r), each explicit cotangent–sawtooth.
## PronicPositivityOfTheVasyuninPrimeKernel (start)
- Vasyunin prime kernel K(p,q) = G^{ec}(p,q) (D(p) = (p−1)/2 − log p) is PSD on every finite prime set (pronic inner product). ⇒ πV(1,p) ≥ log²p − (p−1)log p (Σ a cot(πa/p) ≥ (p/π)(log²p − (p−1)log p), right leading order); K(p,q)² ≤ K(p,p)K(q,q).
## TwoSidedCotangentMomentLawFromPronicEnergy
- Prime energy-centred primitive F_p(M) = log p − (M mod p). Pronic mass of [0,n] = 1 − 1/(n+1). G^{ec}(p,p) ≤ log²p + p + (p−1)²/p (head M < p, tail mass 1/p). Σ_{a<k}cot(πa/k) = 0; V(1,k) = (1/k)Σ a cot(πa/k). ⇒ log²p ≤ πV(1,p) + (p−1)log p ≤ 2log²p + p + (p−1)²/p; cotangent moment Σ_{a<p}a cot(πa/p) = −(p(p−1)/π)log p + O(p²) explicitly.
## PronicReciprocityLawForVasyuninSums
- |K(p,q)| ≤ (K(p,p) + K(q,q))/2. PRONIC RECIPROCITY: (log q − log p)² ≤ π(V(q,p) + V(p,q)) + (q−p)(log q − log p) ≤ (log q − log p)² + 2(log²p + log²q + p + q + (p−1)²/p + (q−1)²/q). π(V(q,p) + V(p,q)) = −(q−p)log(q/p) + O(p+q), entirely from pronic positivity.
## VasyuninFormulaForTheDiscreteBaezDuarteGram (start)
- Root e(a/m); Σ_{a<m}ζ_a^k = m[m|k]. Residue M mod m = −Σ_{0<a<m}α_a(ζ_a^M − 1), α_a = ζ_a/(ζ_a − 1), Σα_a = (m−1)/2. Σ_{0<a<m}log|1 − ζ_a| = log m (cyclotomic norm). α_aQ(ζ_a) = −log(1 − ζ_a). Pronic series of (M mod m₁)(M mod m₂)/(M(M+1)) = ((m₁−1)log m₂ + (m₂−1)log m₁)/2 − (π/2)Σ_{a,b}(cot(πa/m₁) + cot(πb/m₂))((a/m₁ + b/m₂)).
- VASYUNIN FORMULA (discrete Báez-Duarte Gram): m₁m₂·bdGram(1/m₁,1/m₂) = ((m₁−1)log m₂ + (m₂−1)log m₁)/2 − (π/2)(V(m₂,m₁) − V(1,m₁) + V(m₁,m₂) − V(1,m₂)). Diagonal m²bdGram(1/m,1/m) = (m−1)log m + πV(1,m). Cross tail explicit: 2·fractCrossTail(1/m) = (1−1/m) + (1+1/m)fractSqConst − ((m−1)log m + πV(1,m))/m.
## VasyuninReciprocityForAllModuliFromPronicCovariance
- Pronic mean of residue: Σ_M(M mod m)/(M(M+1)) = log m (spectral + cyclotomic norm). Second moments S(m₁,m₂) = Vasyunin series. Covariance S − log m₁ log m₂ PSD. S(m,m) ≤ 2(m−1)²/m (head/tail at M = m). ALL MODULI: log²m ≤ πV(1,m) + (m−1)log m ≤ 2(m−1)²/m; (log m₁ − log m₂)² ≤ π(V(m₂,m₁) + V(m₁,m₂)) + (m₂−m₁)(log m₂ − log m₁) ≤ 4((m₁−1)²/m₁ + (m₂−1)²/m₂) − (log m₁ + log m₂)².
## PronicBaezDuarteCriterion
- L_N(M,c) = −Σc(n)(M mod n)/n. Báez-Duarte residual ‖1_{(0,1]} − Σc(n)ρ_{1/n}‖² = Σ_M(1 + L_N(M,c))²/(M(M+1)). RH ⇔ ∀ε ∃ finite row with pronic energy of 1 + L_N < ε (approximate constant −1 by prefix discrepancies in pronic energy — opposite extremal problem to the receiver). EXACT RH EQUIVALENCE (reformulation).
## VonMangoldtReadoutFormOfTheBaezDuarteCriterion
- Pronic mean of L_N = −Σ_eΛ(e)Y_c(e) (von Mangoldt readout R). Residual = (1 − R)² + Q^{ec}(c). RH ⇔ readout → 1 with centred energy → 0. UNCONDITIONAL FLOOR: (1 − R)² + Q^{ec} ≥ κ/log N for N ≥ 2 (Báez-Duarte distance lower bound from critical-line zeros).
## BaezDuarteEnergyOfThePowerDampedMobiusRows
- Row −w_{ε,Q}: residual = (1 − m(ε,Q))² + V(ε,Q) (energy mean, energy variance). If ∀η ∃ε,Q with residual < η then RH (sufficient, conditional). Unconditional floor ≥ κ/log(Q+1).
## ReadoutEnergyUncertaintyPrinciple (start)
- R(tc) = tR, Q(tc) = t²Q; min_t (1−tR)² + t²Q = Q/(R²+Q). UNCERTAINTY PRINCIPLE: κR(c)² ≤ (log N − κ)Q(c) for every row on [1,N], N ≥ 2. RH ⇔ R²/Q unbounded over finite rows.
- Proof: residual of tc ≥ κ/log N for all t; optimal t = R/(R²+Q) gives Q/(R²+Q) ≥ κ/log N. RH ⇔ ∀K ∃ row with K·Q < R² (ratio unbounded). (RH REFORMULATION.)
## LogHarmonicReadoutAndTheMobiusRowEnergyFloor
- Readout R(c) = Σ_eΛ(e)Y_c(e) = Σ_{d≤N}c(d)log d/d (Σ_{e|d}Λ = log d). Q^{ec} even in c. Möbius row: Σμ(d)log d/d → −1 ⇒ unconditionally Q^{ec}(μ_N) ≥ κ/(4 log N) eventually; residual (1 + Σμ(d)log d/d)² + Q^{ec}(μ_N) ≥ κ/log N for all N ≥ 2.
## MobiusVasyuninFormulaForThePronicGramAtAllModuli
- Σ_{d|m}R_d(M) = m⌊M/m⌋ ⇒ M mod m = −Σ_{d|m,d≥2}R_d(M). S(m₁,m₂) = Σ_{d₁|m₁,d₂|m₂,≥2}G(d₁,d₂). MÖBIUS–VASYUNIN: G(m₁,m₂) = Σ_{a₁b₁=m₁}Σ_{a₂b₂=m₂}μ(a₁)μ(a₂)S(b₁,b₂) for m₁,m₂ ≥ 2 — pronic Gram is the double Möbius transform of Nyman–Beurling cotangent second moments.
## RelationSpectrumDeterminesTheRowUpToTheCompanion
- Same degree-m relation spectrum ⇔ same degree-m translated moments (Parseval). Same relation spectra in degrees 5 and 6 (⇔ all degrees) ⇔ rows agree on [1,N] or one is the companion (half-period reflection flipping top dyadic layer). No other invisible rows.
## ExactVasyuninReciprocityAsResidueDifferenceEnergy
- EXACT: π(V(m₂,m₁) + V(m₁,m₂)) + (m₂ − m₁)(log m₂ − log m₁) = Σ_M((M mod m₁) − (M mod m₂))²/(M(M+1)) (residue-difference pronic energy, ≥ 0). Pronic mass [a,b) = 1/a − 1/b. m₁ < m₂: defect ≥ m₁(m₂−m₁)/m₂ (residues differ by ≥ m₁ on [m₁,m₂)); ≤ 4((m₁−1)²/m₁ + (m₂−1)²/m₂). No o(m₁ + m₂) bound for unequal moduli.
## EnergyMeanOfThePowerDampedSourceTendsToOne (start)
- Σ_nΛ(n)n^{−s} = Re(−ζ'/ζ)(s) (s > 1); per prime Σ_k log p·p^{−s(k+1)} = log p/(p^s − 1) ⇒ Σ_p log p/(p^s−1) = −ζ'/ζ(s). Energy mean m(ε,Q) = Re D·Σ_{p≤Q+1}log p/(p^{1+ε}−1) (prime powers vanish: not squarefree).
- m(ε,Q) → m(ε) = Re D·(−ζ'/ζ)(1+ε) = −ζ'(1+ε)/ζ(1+ε)² as Q → ∞; residues (s−1)ζ → 1, (s−1)²ζ' → −1 ⇒ m(ε) → 1 as ε → 0+. READOUT HALF SETTLED: ∀η ∃δ: ε < δ ⇒ eventually (1 − m(ε,Q))² < η. Dual question for the source reduces EXACTLY to whether energy variance V(ε,Q) → 0 along such a path (open).
## DampedChebyshevTangentFormOfTheReceiver
- Damped von Mangoldt Λ_η(k) = −Σ_{d|k}μ(d)d^{−η}log d (Λ_0 = Λ); damped readout m(η) = −ζ'(1+η)/ζ(1+η)² (derivative of Re D). TANGENT LAW: ∂_ηA_η(n) = E_η(n) := Σ_{k≤n}Λ_η(k) − n m(η) (centred damped Chebyshev). A_ε → 1 as ε → 0+ (Σ_{d|k}μ = [k=1], 1/ζ(1+ε) → 0) ⇒ A_ε(n) − 1 = ∫_0^ε E_η(n)dη. Minkowski in pronic norm (Cauchy–Schwarz, triangle, ‖1‖_T ≤ 1).
- CONDITIONAL CRITERION: if ‖E_η‖_T ≤ g(η) ∀T with g integrable on (0,ε₀) then receiver E_T(ε) ≤ (1 + ∫_0^ε g)² and RH; and dual residual ≤ (∫_0^ε g)². One obligation for both halves — the bound IS the receiver in prime-counting form (zero-free statement for η < ½); NOT proved. (TRAP.)
- Unconditional: (A_ε(n) − 1)/ε → ψ(n) − n; truncated dual residual/ε² → Σ_{n≤T}(ψ(n) − n)²/(n(n+1)) (pronic energy of the Chebyshev error).
## DampingWorkAsArithmeticMarkovBoundaryFlux (start)
- Damped divisor prefix / cutoff evolves under damping-independent finite downward-jump generator (von Mangoldt divisor rates + log adjacent-prefix rates); centring adds constant density-derivative forcing. Pronic energy identity: signed counting-measure flux + nonnegative jump energy + forcing. Flux and jump energy can both grow linearly while cancelling exactly (finite-support inputs) ⇒ no cutoff-uniform bound for combined work asserted.
- Λ_η(n) + D_η(n)log n = Σ_{d|n}Λ(d)D_η(n/d) (D_η = damped divisor coefficient). Prefix tangent Σ_{k≤n}Λ_η(k) = Σ_dΛ(d)P_η(n/d) + Σ_{k<n}P_η(k)(log(k+1) − log k) − log n·P_η(n). Row sum Σ_dΛ(d)⌊n/d⌋ + Σ_{k<n}k(log(k+1) − log k) = n log n. Generator G v(n) = (Σ_dΛ(d)⌊n/d⌋(v(n/d) − v(n)) + Σ_{k<n}k(log(k+1)−log k)(v(k) − v(n)))/n (downward jumps, total departure rate log n, kills constants). Normalized prefix P_η(n)/n satisfies ∂_η = G (damping-independent!). Centred: ∂_η = G − m(η). Square identity 2vGv = G(v²) − Γ(v) (jump energy ≥ 0). Pronic energy derivative = boundary flux − total jump energy − 2m(η)Σ(n/(n+1))·centred mean. Flux has no sign (chain does not preserve the pronic measure).
## ZeroDampingSignedWorkHasFiniteHarmonicTrace
- Signed work 2Σ_{n≤T}A_ε(n)E_ε(n)/(n(n+1)) → 2Σ_{n≤T}(ψ(n) − n)/(n(n+1)) as ε → 0 (fixed T); this series is absolutely summable with total −4γ (Mertens Abel tail). Limits ordered (damping first, then horizon); no interchange/positive-damping bound asserted.
## ArithmeticDampingTransitionKernel (start)
- Σ_{d|n}d^{−η}D_η(n/d) = 1 (any η). Σ_{k≤n}k^{−η}P_η(n/k) = n. P_η ≥ 0 monotone for η ≥ 0. Cesàro transition K_η(n,k) = (k/n)(k^{−η}P_η(n/k) − (k+1)^{−η}P_η(n/(k+1))): ≥ 0 (η ≥ 0), rows sum to 1, supported on k ≤ n, diagonal n^{−η}, identity at η = 0. Σ_k K(n,k)/k = P_η(n)/n (source = transition applied to 1/k). Floor profiles φ_d(n) = ⌊n/d⌋/n are exact eigenfunctions: Kφ_d = d^{−η}φ_d (all real η). Floor-profile moments separate finite rows.
- Floor profiles separate rows (triangular). SEMIGROUP: Σ_j K_s(n,j)K_t(j,k) = K_{s+t}(n,k) for all real s, t (Markov semigroup for s,t ≥ 0) — proved via eigen-moments + separation.
## ArithmeticDampingEntranceLaw
- Entrance law π_η(k) = Re D·k·(k^{−1−η} − (k+1)^{−1−η}) ≥ 0, total mass 1 (Re D·ζ(1+η) = 1). Reciprocal-observable tail Σ_{k>N}π_η(k)/k = Re D·(N+1)^{−1−η} (telescopes exactly; faster than probability tail). K_η(n,k) → π_η(k) as n → ∞ (P_η(n/d)/n → Re D/d).
## ArithmeticDampingCenteredOperator
- Centred rows K_η(n+1,k+1) − π_η(k+1); counting Scheffé ⇒ Σ_k|centred row| → 0. Centred operator on c₀ has norm ≤ 2; output truncations converge in operator norm ⇒ COMPACT on c₀ (η > 0). Controls c₀, NOT critical pronic energy.
## ArithmeticDampingCenteredSemigroup (start)
- Centred operator = finite action − entrance pairing. Finite raw action composes (semigroup) for any input; centring constant-shift compatible. Composition discrepancy is coordinate-constant and both outputs vanish at infinity ⇒ discrepancy zero ⇒ centred operators form a semigroup on c₀.
- Entrance pairing composition law; centred operators C_s∘C_t = C_{s+t} (positive-time semigroup on c₀).
## ArithmeticDampingCenteredSpectrum
- C_η eigen-equation at state 0 fixes entrance value; b − b(0) solves raw lower-triangular equation (diagonal (n+1)^{−η}). Eigenvalues exactly d^{−η}, d ≥ 2; eigenspaces lines ℝv_d, v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d (residue modes). C_η injective. 0 ∈ spectrum (d^{−η} → 0, no bounded inverse). σ(C_η) = {0} ∪ {d^{−η} : d ≥ 2} on c₀ (Fredholm alternative for compact). c₀ statements only; no pronic-norm estimate.
## ResidueModeCoordinatesDiagonalizeTheDampingChain
- Coordinates φ_e(b) = Σ_{d|e}μ(e/d)ΔS_b(d), S_b(x) = x·b(x−1). Inverse: x·b(x−1) = Σ_{e≤x}φ_e(b)⌊x/e⌋ (φ_1 = b(0)). Biorthogonal φ_e(v_f) = δ_{ef} (e ≥ 2). Reciprocal r(x) = 1/x has φ_e(r) = μ(e). DIAGONALIZATION: φ_e(C_η b) = e^{−η}φ_e(b) (density of span of modes in c₀) — chain = vertical shift F(s) ↦ F(s+η) of Dirichlet series Σφ_e e^{−s}; reciprocal orbit coefficients μ(e)e^{−η} = coefficients of 1/ζ(s+η). Orbit formula: x(C_ηb)(x−1) = x(C_ηb)(0) + Σ_{2≤e≤x}e^{−η}φ_e(b)⌊x/e⌋. Rank-one projections Π_e = φ_e(·)v_e orthogonal idempotents commuting with C_η. Coordinates e ≥ 2 determine b ∈ c₀. Expansion only pointwise floor sum; no uniform/receiver-norm bound.
## SuperlinearObservabilityHorizonAtArbitraryPhase (start)
- Alternating sums over subsets vanish if one weight zero. Grid: moduli d_S = D − M·Σ_{j∈S}2^j (S ⊆ [0,m)), offsets ι_S = Σ_{j∈S}j·M2^j, M = (2^m)!, D coprime to M ⇒ grid moduli pairwise coprime ⇒ CRT phase A with d_S | A + ι_S for all S.
- On window of length m(D − M2^m), d_S hits exactly A + ι_S + Jd_S (J < m) = A + JD + Σ_{j∈S}(j−J)M2^j; in block J weight of j = J vanishes ⇒ toggling J ∈ S flips sign, same position ⇒ signed hits cancel (identity Π_j(1 − X^{(j−J)b_j}) = 0). Grid row Σ_S(−1)^{|S|}δ_{d_S} has top coefficient 1 at D.
- SUPERLINEAR HORIZON: for every m and N ≥ (m+2)(2^{m+1})!(1+2^{m+1}) there exist phase A and nonzero row with zero response on m·N consecutive integers. NO LINEAR OBSERVABILITY LAW AT ARBITRARY PHASE (no C with C·N vanishing responses ⇒ zero row). True arbitrary-phase horizon between ≫ N (per fixed m) and Φ(N) ≍ N².
## SuperlinearDiscrepancyObservabilityHorizon
- Three grids with bases D, D−K, D−2K (K = M2^m) share one CRT phase (all moduli D − Mτ, τ < 3·2^m pairwise coprime). Nonzero combination of three grids kills both linear observables (harmonic mode H and discrepancy at phase) ⇒ discrepancy vanishes on mN+1 consecutive prefixes yet variance > 0 (grid tops carry coefficients). For N ≥ (m+4)(2^{m+3})!(1+3·2^{m+1}). NO LINEAR DISCREPANCY OBSERVABILITY at arbitrary phase; the universal 2N − 3 horizon (valid at common returns and N ≤ 4) FAILS at arbitrary phase for large N. (TRAP for linear-horizon programs.)
## CoprimeMoebiusSigmaSumsDecay (start)
- w(n) = μ(n)/σ(n), |w(n)| ≤ 1/n, multiplicative, w(δa) = 0 if (a,δ) > 1. Kernel β_δ(n) = n^{−1}Π_{p|n,p∤δ}(p+1)^{−1} ≥ 0 multiplicative; β_δ * (μ/id) = w·1_{(·,δ)=1}.
- T_δ(Y) = Σ_{d≤Y}β_δ(d)m(⌊Y/d⌋), m(N) = Σ_{n≤N}μ(n)/n. Rankin mass Σ_{d≤Y}β_δ(d)d^{1/4} ≤ K δ^{1/4} (finite Euler product, local factor ≤ (1−p^{−3/4})^{−1}(1+3p^{−7/4}) for p|δ; Π_{p|δ}(1−p^{−3/4})^{−1} ≤ (25/4)δ^{1/4}). Log split 1 + log Y ≤ 2(1 + log⌊Y/d⌋)(1 + log d); (1+log x)² ≤ 64x^{1/4}.
- Coprimality sieve S(X) = Σ_δμ(δ)(w(δ)T_δ(X/δ))². Given |m(N)| ≤ C(1+log N)^{−4}: |T_δ(Y)| ≤ 256CKδ^{1/4}(1+log Y)^{−2}; then |S(X)| ≤ 16·65536C²ζ(5/4)(1+log X)^{−4}. Unconditionally |m(N)| ≤ C/(1+log N)⁴ for all N ≥ 1 ⇒ both decays unconditional.
## TheCofinalMobiusProfileIsAsymptoticallyLinear (start)
- P(B) = lim_N Q_N((B+1)N)/N cofinal quadratic energy of literal Möbius sieve on linear horizon (B+1)N. P(t+1) = P(t) + γ_{t+1}, band slope γ_t = Σ_{q,r≤t}D(q,r)/[q,r] = mean square of complementary truncation Σ_{q|k,q≤t}μ(k/q) over band (tN,(t+1)N]; P(B) = Σ_{t≤B}γ_t.
- Gcd reindexing (q,r) = (gb,ga), (a,b)=1; D(a,b)/(gab) = ρ w(a)w(b)/g (ρ = 6/π², squarefree a: Π_{p|a}p/(p+1) = a/σ(a)) ⇒ γ_t = ρΣ_{g≤t}S(⌊t/g⌋)/g.
- Harmonic fibres A_j(t) = Σ_{⌊t/g⌋=j}1/g = H(⌊t/j⌋) − H(⌊t/(j+1)⌋) → log(1+1/j); A_j(t) ≤ 3/j for j² ≤ t. Σ_j 1/(j(1+log j)²) < ∞ (telescoping). Harmonic-average theorem: |f(X)| ≤ C(1+log X)^{−4} ⇒ Σ_{g≤t}f(⌊t/g⌋)/g → Σ_j f(j)log(1+1/j) (dominated convergence below √t, tail O((1+log t)^{−3})).
- RESULTS: γ_t → κ = ρΣ_{j≥1}S(j)log(1+1/j); P(B)/B → κ (Cesàro); Buchstab sum rule Σ_{b≥1}A(b)/(b(b+1)) = −κ. Limits N → ∞ then B → ∞ in this order. Band averages A(b) change sign (A(10) > 0) ⇒ sum rule is not a sign statement.
## CoprimeMoebiusHarmonicSumsDecay
- m_f(Y) = Σ_{a≤Y,(a,f)=1}μ(a)/a; smooth kernel κ_f(k) = 1/k if all primes of k divide f: κ_f * (μ/id) = (μ/id)1_{(·,f)=1}. Rankin mass Σκ_f(k)k^{1/4} ≤ Π(f) = Π_{p|f}(1−p^{−3/4})^{−1} exactly (Euler product); Π multiplicative, Π(f) ≤ (25/4)f^{1/4}.
- |m_f(Y)| ≤ CΠ(f)(1+log Y)^{−2} unconditional. Pair sum S'_g(X) = Σ_{(a,b)=1,(ab,g)=1}μ(a)μ(b)/(ab) = Σ_δμ(δ)([(δ,g)=1]μ(δ)m_{δg}(X/δ)/δ)²; |S'_g(X)| ≤ CΠ(g)²(1+log X)^{−4}.
- Π(g)² = Σ_{d|g}h(d) on squarefree g, h(p) = (1−p^{−3/4})^{−2} − 1 ≤ 9p^{−3/4} ⇒ Σ_{g≤N}μ(g)²Π(g)²/g ≤ (1+log N)·exp(9ζ(7/4)) (Π² has bounded harmonic mean).
## TheCofinalMobiusSlopeIsThePeriodVariance (start)
- Period mean square C(N) = Σ_{d,e≤N}μ(d)μ(e)/[d,e]. μ(ga)μ(gb) = μ(g)²μ(a)μ(b)[(g,ab)=1] ⇒ C(N) = Σ_{g≤N}μ(g)²/g·S'_g(⌊N/g⌋).
- Quantitative fibres: 0 ≤ H(n) − log n − γ ≤ 1/n; |A_j(n) − log(1+1/j)| ≤ 4(j+1)/n for n ≥ 2(j+1); A_j(n) ≤ 3 always.
- Squarefree coprime fibre W_m(N,j) = Σ_{⌊N/g⌋=j}μ(g)²[(g,m)=1]/g = Σ_dΣ_{e|m}μ(d)μ(e)/[d²,e]·A_j(⌊N/[d²,e]⌋) via μ²(g)[(g,m)=1] = Σ_{d²|g}Σ_{e|(g,m)}μ(d)μ(e). Coprime-squarefree density D(m) = Σ_dΣ_{e|m}μ(d)μ(e)/[d²,e] for squarefree m (dominated convergence of counts/N); 0 ≤ D(m) ≤ 1.
- Equidistribution of squarefree coprime fibres: |W_m(N,j) − D(m)A_j(N)| ≤ Kτ(m)(j+1)(1+log N)/√N (squarefree m, N ≥ 2(j+1)); series tail |Σ_{d>N}v_m(d)| ≤ τ(m)ζ(3/2)/√N.
- ρw(a)w(b) = μ(a)μ(b)/(ab)·D(ab) on coprime a,b. Fibre identity: fibre ⌊N/g⌋ = j of C(N) − γ_N equals Σ_{(a,b)=1,a,b≤j}μ(a)μ(b)/(ab)(W_{ab}(N,j) − D(ab)A_j(N)); bound K j²(j+1)(1+log N)/√N.
- C(N) − γ_N splits at fibre cutoff J(N) = ⌊N^{1/16}⌋ (iterated isqrt): head (j ≤ J) ≤ 34K/J³; tail (j > J) ≤ 16(C₁E + ρC₂)/(1+log(J+1))³ via pair decays and Σμ²Π²/g ≤ (1+log N)E.
- RESULT: C(N) = Σ_{d,e≤N}μ(d)μ(e)/[d,e] → κ = lim_B P(B)/B. Quadratic energy density of literal Möbius source on linear horizons M = O(N) equals its complete-period variance (generic rows need windows > N² to reach period values). |C(N) − γ_N| ≤ 34K/J³ + 16(...)/(1+log(J+1))³, J = ⌊N^{1/16}⌋ (rate only (log N)^{−3}).
## CoprimeMertensSawtoothCancellation (start)
- |m_f(Y)| ≤ CΠ(f)(1+log Y)^{−4} (fourth power kept, 2²⁰ constant); Abel M_f(s) = s m_f(s) − Σ_{j<s}m_f(j); Σ_{j<s}(1+log j)^{−4} ≤ 131088 s(1+log s)^{−4} ⇒ coprime Mertens |M_f(s)| ≤ KΠ(f)s(1+log s)^{−4}.
- Abel bound: 0 ≤ w ≤ 1 decreasing on (u,v], all partial sums ≤ T ⇒ |Σ a w| ≤ T.
- Sawtooth {M/(cb)} = M/(cb) − n on piece ⌊t/b⌋ = n (t = ⌊M/c⌋), decreasing in b. Range b > t: sawtooth = M/(cb), sum = (M/c)(m_f(X) − m_f(t)) ≤ 4KΠ(f)t(1+log t)^{−3}. Integers with ⌊t/b⌋ > √t (b ≤ √t): ≤ √t. Piece n ≤ √t lies in [t^{1/4}, t/n] ⇒ |M_f(x)| ≤ 256KΠ(f)t/(n(1+log t)⁴).
- SAWTOOTH CANCELLATION: c ≥ 1, t = ⌊M/c⌋ ≥ 256, all X: |Σ_{b≤X,(b,f)=1}μ(b){M/(cb)}| ≤ KΠ(f)t(1+log t)^{−3} + √t (pieces n ≤ √t via Abel+harmonic sum; b ≤ √t trivially; b > t harmonic).
## TheMoebiusPrefixEnergyAtLargeBandRatio
- E_N(M) = Σ_{d,e≤N}c(d)c(e)⌊M/[d,e]⌋ (any row). For μ: E_N(M) = M·C(N) − Σμ(d)μ(e){M/[d,e]}; gcd coordinates: sawtooth form = Σ_gμ(g)²Σ_{(a,g)=1}μ(a)Σ_{b≤N/g}μ(b)[(b,ag)=1]{M/(gab)}; each cell t = ⌊M/(ga)⌋ ≥ B = ⌊M/N⌋.
- |sawtooth form| ≤ M(KE²(1+log N)²/(1+log B)³ + (1+log N)²/√B). RESULT: B ≥ 256, N ≤ B^16 ⇒ |E_N(M)/M − C(N)| ≤ 256KE²/(1+log B) + 256(1+log B)²/√B. Möbius prefix mean square = period value up to a function of band ratio alone, incl. quadratic range M ≍ N² (where generic rows need full window sandwich).
## TheMoebiusEnergyTransfersAtEverySuperlinearHorizon (start)
- ∀ε ∃B₀,N₀: N ≥ N₀, M ≥ B₀N ⇒ |E_N(M)/M − κ| ≤ ε; E_N(M)/M → κ along every horizon with M/N → ∞. Generic level-N rows need N^{2±o(1)}; Möbius row transfers at every superlinear horizon. Proof split B ≤ J = ⌊N^{1/16}⌋ (quotient-pair form, |E_N((B+1)N) − 1 − NP(B)| ≪ B⁵√N log N, monotone in M) vs B > J (large band ratio + C(N) → κ).
- {X/L} ≤ √X/d when d² ≤ L. Coprime squarefree counts: |#{n ≤ X sqfree,(n,m)=1} − D(m)X| ≤ τ(m)√X(2 + ζ(3/2) + log X).
- Dilation pairs: |Σ_{n≤X}μ(an)μ(bn) − X D(a,b)| ≤ ab√X(2 + ζ(3/2) + log X). Band identity with error |E_N((B+1)N) − 1 − NP(B)| ≤ bandError(B,N) ≪ B⁵ J√N for B ≤ J; (1 + bandError)/(BN) ≤ (143 + 4ζ(3/2))/J³.
- Monotone sandwich: |E_N(M)/M − κ| ≤ |P(B)/B − κ| + |P(B−1)/(B+1) − κ| + (1 + bandError)/(BN), B = ⌊M/N⌋. P(B−1)/(B+1) → κ.
- Case split B ≤ J (band sandwich) / B > J (large band ratio + C(N) → κ) ⇒ SUPERLINEAR TRANSFER: M(N)/N → ∞ ⇒ E_N(M(N))/M(N) → κ.
## MoebiusPrimitiveFibreMasses
- J₂(q)/q² = Σ_{d|q}μ(d)/d². Jordan density δ(m) = Σ_{(d,m)=1}μ(d)D(dm)/d³ (|δ| ≤ ζ(3), tail ≤ ζ(2)/(N+1)). Fibre mass U_m(N,j) = Σ_{⌊N/q⌋=j,(q,m)=1}μ(q)²J₂(q)/q² = Σ_d[(d,m)=1]μ(d)/d²·#{q' sqfree,(q',dm)=1, ⌊⌊N/d⌋/q'⌋ = j}.
- |U_m(N,j) − δ(m)N/(j(j+1))| ≤ 2ζ(3/2)τ(m)√N(2 + ζ(3/2) + log N) + 3ζ(2) (squarefree m).
## TheMoebiusPrimitiveEnergyGrowsLinearly (start)
- 12E_prim(N;μ) = Σ_{2≤q≤N}μ(q)²(J₂(q)/q²)m_q(⌊N/q⌋)² (Jordan spectrum); m_q(j)² = Σ_{a,b≤j}μ(a)μ(b)/(ab)[(q,[a,b])=1]; fibre ⌊N/q⌋ = j = Σ_{a,b≤j}μ(a)μ(b)/(ab)U_{[a,b]}(N,j). Fibre weight T(j) = Σ_{a,b≤j}μ(a)μ(b)δ([a,b])/(ab).
- RESULT (stated): 12E_prim(N;μ)/N → c = Σ_{j≥1}T(j)/(j(j+1)) ≈ 0.3311. Period discrepancy of Möbius row is DIFFUSIVE (linear growth, explicit diffusion constant); previously only N/2 ≤ 3456E_prim and 12E_prim ≤ 64N(1+log N). Tail j > J uses |m_q| ≤ q/φ(q), Σ_{q≤x}(q/φ(q))³ ≪ x.
- Fibre law: fibre ⌊N/q⌋ = j carries N T(j)/(j(j+1)) up to j²(2ζ(3/2)√N(2 + ζ(3/2) + log N) + 3ζ(2)). Tail modes ⌊N/q⌋ > J carry ≤ e^{19/2}⌊N/(J+1)⌋ (via |m_q| ≤ q/φ(q), Σ(q/φ(q))³ ≤ e^{19/2}x). |T(j)| ≤ ζ(3)(1+log j)². |12E/N − Σ_{j≤J}T(j)/(j(j+1))| ≤ C/J⁴ + e^{19/2}/(J+1).
- PROVED: 12E_prim(N;μ)/N → c = Σ_{j≥1}T(j)/(j(j+1)) (rate ~1/J = N^{−1/16}).
## ResidueModeCompleteness (start)
- Truncated Möbius floor sum Σ_{k≤K}μ(k)⌊m/k⌋ = [m ≥ 1] for m ≤ K, and |·| ≤ 2m always (uniform linear majorant; uses |Σμ(k)/k| ≤ 1). Normalized residue profile v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d = −((n+1) mod d)/(d(n+1)), |v_d(n)| ≤ 1/(n+1) ⇒ v_d ∈ C₀(ℕ). Claim: residue modes dense in c₀ (dual separation; inversion against every ℓ¹ row without cancellation hypothesis). NOT density in critical pronic receiver norm.
- Proof: ℓ¹ row a annihilating all v_d ⇒ Σa = 0 (dominated convergence of d·floor profile) ⇒ floor pairings vanish ⇒ truncated Möbius inversion (majorant 2m, no cancellation needed) ⇒ tails Σ_{n+1≥d}a_n/(n+1) = 0 ⇒ a = 0. Dual of c₀ = ℓ¹ ⇒ Hahn–Banach ⇒ span{v_d : d ≥ 2} DENSE in c₀ (uniform norm only).
## ArithmeticDampingEntranceTailBarrier
- Entrance tail T_η(N) = Σ_{k>N}e_η(k) ≥ ρ_η(N+1)^{−η} (size bias from exact reciprocal tail Σe_η(k)/k = ρ_η(N+1)^{−1−η}). For η ≤ 1/2: Σ_N T_η(N)² = ∞; row L¹ error ‖P_η(n,·) − e_η‖₁ ≥ T_η(n) (row supported below start) ⇒ total variation NOT square-summable for η ≤ 1/2.
- Reciprocal observable tail ≤ 1/(N+1) at every η > 0, square-summable (ρ_η ≤ 1). Obstruction concerns absolute row control, not signed source.
## PronicDualNormOfTheEntranceLaw (start)
- Centring P_η − e_η needs entrance functional pronic-bounded (pronic ℓ² weight 1/(n(n+1))). Bernoulli two-sided bounds: (1+η)t^{−1−η}/(t+1+η) ≤ t^{−1−η} − (t+1)^{−1−η} ≤ (1+η)t^{−1−η}/(t+1); e_η(k) ≤ ρ_η(1+η)k^{−η}/(k+1).
- e_η(k) ≥ ρ_η(1+η)k^{−η}/(k+1+η). PRONIC DUAL NORM Σe_η(k)²k(k+1) < ∞ ⇔ η > 1/2 (≍ Σk^{−2η}). Above 1/2: entrance functional bounded on pronic inner product (Cauchy–Schwarz). At/below 1/2: unbounded (truncated dual vectors); for η < 1/2 explicit witness b(k) = k^{(η+1/2)/2}: pronic-square-summable but divergent entrance pairing. Threshold 1/2 = receiver damping threshold, read from size bias alone. Obstruction sits in centring, not transition. Reciprocal observable e_η(k)/k has finite pronic dual norm at every η > 0.
## PowerDampedResidualHasLinearCusp (start)
- Literal residual R_ε(T) = Σ_{n≤T}(S_ε(n) − 1)²/(n(n+1)), S_ε centred divisor prefix. Bounded residual ⇒ head q_ε(u) = S_ε(⌊1/u⌋) − 1 ∈ L²(0,∞) with energy = Σ. q_ε = centred source + ρ_ε·nymanGen₁ − 1_{u≤1}; dyadic difference q(u) − 2q(2u) = Fermi source + ρ_ε fermiNyman − dyadic Haar.
- Mellin: M q_ε(s) = (ζ(s)/ζ(s+ε) − ρ_ε ζ(s) − 1)/s on 1/2 < Re s < 1 (step correction gives −ρζ(s)/s, not continuous pole). Paley–Wiener: (2Re s − 1)|M q_ε(s)|² ≤ C if R_ε(T) ≤ C ∀T. Critical zero ρ of multiplicity m: ζ(ρ+ε)/ζ(ρ+2ε) → (1/2)^m as ε → 0⁺.
- M q_ε(ρ+ε) → ((1/2)^m − 1)/ρ; 2|((1/2)^m − 1)/ρ|² > 1/(4|ρ|²). UNCONDITIONAL LINEAR CUSP: ∃κ > 0, δ > 0: ∀ε ∈ (0,δ) ∃T: R_ε(T) > κε (κ = 1/(4|ρ|²) for a critical zero ρ; existence of critical zero used, no RH/admission). Literal residual cannot be o(ε) uniformly in T.
## LogarithmicReciprocityDefectForNearbyModuli
- Vasyunin reciprocity defect = residue-difference energy = residue-gap pronic energy. For h ≤ p, K = ⌊p/h⌋: hH_K − 2h ≤ π(V(p+h,p) + V(p,p+h)) ≤ hH_K + 4h. Symmetric Vasyunin sum of nearby moduli ≍ h log(p/h); log p for consecutive/twin moduli; linear only when sizes differ.
## HardyLittlewoodSingularSeriesOfTheDampedSource
- Limiting lag-h covariance A_ε(h) = Σ_{e≥2}c_e(h)w_ε(e)², w_ε(e) = ρ_εμ(e)/D_ε(e), D_ε(e) = Π_{p|e}(p^{1+ε} − 1). D_ε → φ on squarefree, dominated by σ(h)μ²/φ². RESULT: (ρ_ε² + A_ε(h))/ρ_ε² → 𝔖(h) = Σ_qμ²(q)c_q(h)/φ(q)² (Hardy–Littlewood singular series); jointly in (ε,Q) for receiver rows Cov_{Q+1}(h;c_Q). 𝔖(h) = Π_p(1 + c_p(h)/(p−1)²), c_p(h) = p−1 if p|h else −1; 𝔖(h) = 0 for odd h, > 0 for even h.
- Relative to variance V(ε) ~ ε/2 source is white (A_ε/V → 0); relative to ρ_ε² ~ ε² lag correlations = Λ(n)Λ(n+h) prediction (τ_ε(n)/ε → Λ(n)). Order: period first, then damping. Says NOTHING about actual prime-pair correlations.
## ExactDampedSingularSeriesAndGallagherPrefixDiscrepancy (start)
- For each ε > 0: (ρ_ε² + A_ε(h))/ρ_ε² = 𝔖_ε(h) = Σ_qc_q(h)μ²(q)/D_ε(q)² = Π_p(1 + c_p(h)/(p^{1+ε} − 1)²); 𝔖_ε → 𝔖. Odd h: factor at 2 = 1 − 1/(2^{1+ε} − 1)² > 0, vanishes only in limit (odd gaps suppressed continuously).
- Lag sums → Ramanujan primitives: Σ_{h≤H}A_ε(h) = Σ_{e≥2}w_ε(e)²R_e(H) = prefix discrepancy at H of row with Selberg coordinates w_ε(e)². GALLAGHER: Σ_{h≤H}(𝔖(h) − 1) = Σ_{q≥2}(μ²(q)/φ(q)²)R_q(H) — Gallagher's singular-series sum (governs variance of primes in short intervals) is prefix discrepancy of row with Selberg coordinates μ²/φ².
## HardyLittlewoodTupleSeriesFromRadicalClosedRows
- Radical-closed damped row c(d) = μ(d)d^{−ε} on divisors of P = Π_{p∈S}p: response s(n) = Π_{p∈S}g_p(n), g_p(n) = 1 − p^{−ε} if p|n else 1 (each prime acts on own residue). CRT: every translated moment factors exactly: (1/P!)Σ_{n<P!}Π_is(n+h_i) = Π_{p∈S}m_p(ε,H), m_p = (1/p)Σ_{r<p}Π_ig_p(r+h_i). k = 1: 1 − p^{−1−ε}. ε = 0: m_p = 1 − ν_p(H)/p (ν_p = occupied residues of −H).
- Normalized moments → Π_{p∈S}(1 − ν_p(H)/p)/(1 − 1/p)^k as ε → 0; factor within k²/p² of 1 once p > spread (1 − k²x² ≤ (1−kx)/(1−x)^k ≤ 1). Product over all primes converges to 𝔖(H) (prime k-tuple singular series); 0 for inadmissible, > 0 for admissible. Pair case: Euler form = Ramanujan form Σμ²c_q(h)/φ².
## SecondOrderSmallDampingLawsFromTheSingularSeries (start)
- V(ε) = ε/2 − ε² + o(ε²); Haar dissipation R(ε) = ε/2 + o(ε²). E[τ_ε²] = C(ε)ζ(1+2ε)/ζ(1+ε)², C(ε) = Π_p(1 − ((t−t²)/(p−t))²), t = p^{−ε}, prime deficit ≤ ε²(log p/(p−1))² ⇒ C = 1 − O(ε²); Euler constant cancels. Bézout limit Σμ(e)w_ε(e)² = ρ_ε²𝔖_ε(1) (c_e(1) = μ(e)) ⇒ R(ε) = V(ε) + ρ_ε²(1 − 𝔖_ε(1)), 𝔖_ε(1) → 𝔖(1) = 0 (one of two consecutive integers even): extra ρ_ε² ~ ε² cancels second-order term.
- 1/ρ_δ − 1/δ → γ (ζ(1+δ) = 1/δ + γ + o(1)). PROVED: (V(ε) − ε/2)/ε² → −1; (R(ε) − ε/2)/ε² → 0.
## BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo
- Energy-centred prime primitive F_p(n) = log p − (n mod p). For n < 2p (one jump): packet V(n) = Σa_pF_p(n) = L − nA + C(n), C(n) = Σ_{p≤n}a_p p (cumulative jump sum), A mass, L log moment.
- S ⊆ (P,2P], A = L = 0: pronic energy of window n < 2P+2 = Σa_pa_q(min(p,q) − pq/(2P+2)) (BROWNIAN-BRIDGE kernel) ≤ energy-centred Gram form Σa_pa_q𝒢^{ec}(p,q). At block primes: Σ_pC(p)²/(2P(2P+1)) ≤ Gram.
- Ramp: Σ_{v<k}(x + (v+1)c)² ≥ c²k(k²−1)/12. CODIMENSION NO-GO: S ⊆ (P,2P] with ≥ (J+3)k primes, any J linear side conditions ⇒ ∃ nonzero packet with A = L = 0, satisfying conditions, Gram ≥ (k²−1)/(24(2P+1))·Σp a_p² (block-constant jumps on J+3 blocks). Cauchy–Schwarz upper bound |S|Σa_p²𝒢^{ec}(p,p), 𝒢^{ec}(p,p) ≍ p. With k ≈ |S|/(J+3): no Type-II estimate with finitely many side conditions beats Cauchy–Schwarz by more than (J+3)²log P on a prime block; diagonal quality needs J ≳ |S|/√P conditions. Necessary replacement hypothesis: square-root size of cumulative jump sum C on block (summatory function of coefficients). (TRAP + positive survivor.)
## CoherentPrimeBlocksAndTheTypeIIWindowNoGo
- Every prime packet V(n) = L − Σa_p(n mod p). Block B of k primes in [p₀, p₀+ℓ], unit jumps a_p p = 1: between clusters j(p₀+ℓ) ≤ n < (j+1)p₀ all ⌊n/p⌋ = j and V(n) = L + kj − ns, s = Σ1/p ≥ k/(2p₀) (exactly affine). Affine run of r values ≥ s²r(r²−1)/12.
- Window W = [J₀p₀, 2J₀p₀), 4J₀ℓ ≤ p₀: pronic energy on W ≥ (k/2304)·kΣ_W1/(n(n+1)) (window diagonal bound) — energy exceeds diagonal by factor k/2304 = #primes in interval of length ℓ ≈ p₀²/(4X).
- Pigeonhole: every S ⊆ (P,2P] contains block with k ≥ |S|/⌈P/(ℓ+1)⌉ ≈ |S|P/(4X). At X = P^{2/θ}: loss P^{2−2/θ}/log P, a power of P for every θ > 1. LARGE-SIEVE LOSS P²/X ATTAINED below quadratic horizon; NO TYPE-II INPUT (arbitrary coefficients, ℓ² norms) reaches any θ > 1 on pronic prime Gram. Obstruction = jump measure Σ_{p∈I}a_p p on intervals of length P²/X; replacement hypothesis = its square-root cancellation at that scale. (TRAP)
## SummatoryFunctionBoundForTheDyadicPronicGram
- Row c on dyadic block (N₀,2N₀] with |Σ_{n≤m}c(n)| ≤ B ∀m. V(M) = R₀ − Σc(n)(M mod n)/n (R₀ von Mangoldt constant). Hyperbola: Σc(n)⌊M/n⌋ = Σ_{j≤M}S(⌊M/j⌋). Abel vs 1/n: |Σc/n| ≤ B/(N₀+1); only ⌊M/(N₀+1)⌋ layers contribute ⇒ |Σc(n)(M mod n)/n| ≤ 2BM/(N₀+1); trivial ≤ ‖c‖₁.
- Gram ≤ 3R₀² + 8B² + 2‖c‖₁²/(N₀+1)²; |R₀| ≤ B (Abel vs log n/n); ‖c‖₁²/(N₀+1)² ≤ 2D(c) ⇒ RESULT: energy-centred pronic Gram ≤ 11B² + 4D(c), D(c) = Σc(n)²/n.
- For row classes with dyadic summatory function O(√D) (alternating signs, fixed character twist, bounded partial sums): Gram within constant of diagonal = dispersion at receiver exponent θ = 2 at ONE modulus, no character/modulus average. Cauchy–Schwarz loses N₀. Coherent blocks show summatory function is NECESSARY (first-window energy = its mean square). (POSITIVE SURVIVOR of Type-II no-go.)
## CrossScaleFactorizationOfThePrimePronicGram
- Packet values V_a(n) = m(a) + Ṽ_a(n), m(a) = L_a − Σa_p(p−1)/2, Ṽ_a = −Σa_p((n mod p) − (p−1)/2) (centred residues: interval sums ≤ p²/2 ⇒ fast factor, K_a = Σ|a_p|p²/2). V_b(n) = L_b − nA_b + Σ_qb_q q⌊n/q⌋ (slow factor = superposition of steps 1[jq ≤ n]); Abel vs pronic weight beyond jq costs K_a/(jq(jq+1)).
- CROSS-SCALE: |Σa_pb_q𝒢^{ec}(p,q) + m(a)L_b| ≤ K_a(|A_b|/2 + 2Σ|b_q|/q). On A_b = L_b = 0: |Σa_pb_q𝒢^{ec}| ≤ Σ|a_p|p²·Σ|b_q|/q for ARBITRARY coefficients. a on (P,2P], b on [Q,2Q]: ‖a‖₁‖b‖₁P²/Q vs Cauchy–Schwarz ‖a‖₁‖b‖₁√(PQ): power saving (P/Q)^{3/2} without character/modulus average (loss = period P² of fast factor vs step length Q).
## ExactTypeIILossOfTheReceiverGram (start)
- Receiver form Q(c) = ΣV_c(M)²/(M(M+1)), V_c(M) = R(c) − Σc(n)(M mod n)/n. First window (row on (N₀,2N₀], M ≤ 2N₀): V_c(M) = R − MH + S(M), H = Σc/n, S summatory. Codimension no-go (log-free): (J+3)k ≤ N₀, any J side conditions ⇒ row with R = H = 0, Q(c) ≥ (k²−1)/(24(2N₀+1))·D(c); k = ⌊N₀/(J+3)⌋ ⇒ ≈ N₀/(48(J+3)²)·diagonal: CAUCHY–SCHWARZ SHARP up to 48(J+3)².
- Every window below quadratic horizon: unit integer row on [n₀, n₀+ℓ] is affine between clusters; window energy ≥ (k/2304)·window diagonal, k = ℓ+1 ≈ n₀²/(4X); log-free large sieve gives matching 1 + 2(2n₀)²/X. EXACT TYPE-II LOSS of receiver Gram = Θ(N²/X) at every X ≤ N², Θ(N/J²) at receiver window. No Type-II input reaches θ > 1; replacement hypothesis = square-root size of row's summatory function on intervals of length N²/X.
## ExactRankTwoCrossScaleLawOfTheReceiverGram (start)
- B(c,c') = ΣV_cV_{c'}/(M(M+1)). Row mean m(c) = R(c) − Σc(n)(n−1)/(2n); fluctuation F_c(M) = −Σ(c(n)/n)((M mod n) − (n−1)/2), interval sums ≤ K_c = Σ|c(n)|n/2. Slow: V_{c'}(M) = R(c') − MH(c') + Σc'(n)⌊M/n⌋. Dirichlet constant β(c) = Σ_{M≥1}F_c(M)/(M+1) converges (conditionally).
- EXACT RANK-TWO LAW: |B(c,c') + m(c)R(c') + β(c)H(c')| ≤ 2K_cΣ|c'(n)|/n². c on (P,2P], c' on (Q,2Q]: remainder ‖c‖₁‖c'‖₁P/Q² vs rank-two size ‖c‖₁‖c'‖₁(log Q)/Q.
- Single moduli e ≤ q: |eqB(δ_e,δ_q) − (D_e log q − (e+1)/2(H_e − 1) + (e−1))| ≤ e/2 + e²/q, D_e = (e−1)/2 − log e; |eβ(δ_e) − ((e+1)/2(H_e−1) − (e−1))| ≤ e/2. D_e < 0 ⇔ e ∈ {2,3} (e ≥ 2). SIGN LAW: for large q, sign B(δ_e,δ_q) = sign D_e: moduli 2, 3 couple negatively to every large modulus (≈ −log q), every e ≥ 4 positively.
- Prime unit rows: pqB(δ_p,δ_q) = 𝒢^{ec}(p,q) (receiver unit rows at primes = Vasyunin prime kernel). FAR-SCALE LAW: |𝒢^{ec}(p,q) − (D_p log q − (p+1)/2(H_p − 1) + (p−1))| ≤ p/2 + p²/q; 𝒢^{ec}(p,q) = (p/2)log(q/p) + O(p) for q ≥ p².
## LargeSieveDispersionOfTheCrossScaleRemainder (start)
- For c on primes: F_c(M) = Σ_p(c(p)/p)Σ_{ζ prim p}ζ/(ζ−1)ζ^M (exponential sum over primitive p-th roots). Summation by parts: ‖Σ_{A≤M<H}w(M)ζ^M − w(A)ζ^A/(1−ζ)‖ ≤ (w(H−1) + 2(w(A)−w(A+1))/|ζ−1|)/|ζ−1|.
- Farey separation: |ζ−1| ≥ 4/p for primitive p-th ζ; Σ_ζ|ζ−1|^{−2} ≤ p²/4; Σ|ζ−1|^{−(k+2)} ≤ (p/4)^k p²/4 (Σ|1−ζ|^{−4} ≤ p⁴/64). Dilated frequencies ζ^j have ≤ j preimages ⇒ large sieve cost factor j. Σ_j√j/j² ≤ 4; Σ_j(w(jn) − w(jn+1)) ≤ 4/n³.
- RESULT (stated): c on primes ≤ Q₀, c' on window of length L: |B + mR' + βH'| ≤ ½√(Σc(p)²p²)√(L + 2Q₀² − 1)√(Σc'(n)²/n⁴) + ½Σ|c(p)|p²·Σ|c'(n)|/n³. For c on (P,2P], c' on (Q,2Q], P ≤ Q ≤ P²: ratio to √(D(c)D(c')) is P^{5/2}/Q^{3/2} ⇒ cross-scale Gram rank two at diagonal quality once Q ≥ P^{5/3} (improves elementary Q ≥ P²). Input: additive large sieve over small primes acting on residues of large moduli.
- Proof: main term = Σ_jΣ_ζα(ζ)Σ_nc'(n)w(jn)(ζ^j)^n with α(ζ) = (c(p)/p)ζ/((ζ−1)(1−ζ)), Cauchy–Schwarz + dilated large sieve (factor j), Σ_j√j/j² ≤ 4; boundary error δ(H) → 0. PROVED.
## LargeSieveDispersionInSelbergCoordinates
- Every row's fluctuation = canonical primitive F_c(M) = W_{N,c}(M) = Σ_{ζ≠1}Y_c(ord ζ)ζ/(ζ−1)ζ^M. Abstract: for F_c = Σ_{ζ∈T}κ(ζ)ζ^M, T nontrivial roots of order ≤ Q₀: |B + mR' + βH'| ≤ 4√(Σ|κ|²/|ζ−1|²)√(L+2Q₀²−1)√(Σc'²/n⁴) + 8(Σ|κ|/|ζ−1|²)Σ|c'|/n³.
- SELBERG FORM: every row c on [1,Q₀]: |B + mR' + βH'| ≤ ½√(Σ_eY_c(e)²e⁴)√(L+2Q₀²−1)√(Σc'(n)²/n⁴) + ½Σ_e|Y_c(e)|e³·Σ|c'(n)|/n³ (Farey: Σ|ζ−1|^{−3} ≤ e³/16). Cross-scale dispersion holds for receiver's own rows on all moduli, Jordan-type weight e⁴ on Selberg coordinates; primes Y(p) = c(p)/p recover prime theorem.
## SecondOrderCrossScaleLawAndTheBernoulliKernel (start)
- Residue potential Φ_d(M) = (d²−1)/12 − ρ(d−ρ)/2 = (d²/2)B₂(ρ/d) − 1/12 (ρ = M mod d), mean-zero second primitive: Φ_d(M+1) − Φ_d(M) = r_d(M); |Φ_d| ≤ d²/8, interval sums ≤ d³/8.
- Bernoulli kernel 𝔅(d,n) = Σ_{j≥1}Φ_d(jn)/j² (depends on n mod d). Stated: |B + mR' + βH' − Σ_{n,d}c'(n)c(d)𝔅(d,n)/(dn²)| ≤ ¾(Σ|c(d)|d²)(Σ|c'(n)|/n³). Two primes p < q: 𝒢^{ec}(p,q) = −pq(mR + βH) + 𝔅(p,q)/q + O(p³/q²) — fine cross-scale structure is a function of q mod p of size p²/q. 𝔅(d,n) = (d²/2)Σ_jB₂({jn/d})/j² − π²/72; Σ_jB₂({jx})/j² = Estermann cosine series π^{−2}Σ_hd(h)cos(2πhx)/h².
- Two summations by parts: |Σ_{A≤M<H}r_d(M)w(M) + 1[A<H]Φ_d(A)/A²| ≤ 1[A<H](d²/8)w(H−1) + (d³/8)(w(A)−w(A+1)) + (d²/8)/A³. |𝔅(d,n)| ≤ (d²/8)(π²/6). PROVED SECOND-ORDER LAW (¾ constant). Two primes: |𝒢^{ec}(p,q) − D_p log q + pβ_p − 𝔅(p,q)/q| ≤ ¾p³/q²; kernel term is function of q mod p of size ≤ (π²/48)p²/q.
## CoherentNearMultipleObstructionToCrossScaleDispersion (start)
- Φ_d ≥ −(d²+2)/24; Φ_d(M) ≥ (d²−1)/12 − (M mod d)d/2. BERNOULLI POSITIVITY: 32(n mod d) ≤ d ⇒ 𝔅(d,n) ≥ d²/25 − 1/4 (π < 3.15).
- Coherent windows: 64(n₀ mod d) ≤ d and 64H ≤ d ⇒ 32((n₀+t) mod d) ≤ d for t < H. In any T consecutive integers ≥ (T−d)/64 lie in [0,d/64] mod d. COHERENT SHIFT: S ⊆ [1,D], any Q ⇒ ∃n₀ ∈ [Q,Q+2D) with |S| ≤ 128|{d ∈ S: 64(n₀ mod d) ≤ d}| (double counting).
- Stated: nonneg rows c on coherent moduli, c' on window, n₀ ≥ 75D ⇒ B + mR' + βH' ≥ (1/100)(Σc(d)d)(Σc'(n)/n²) = 1/100 of trivial rank-two remainder bound — attained by coherent configurations for every set of small moduli (primes included), every placement. Large-sieve vs coherent differ by ≍ √(|S|/D) ⇒ threshold Q ≥ P^{5/3} SHARP up to √(log P) for prime packets. Below it no Type-II input escapes rank-two law with diagonal remainder. Replacement hypothesis: equidistribution of large-scale coefficients across near-multiple windows {n mod p ≤ p/32} (cancellation of Σ_{n∈I}c'(n) on intervals of length ≍ P against coherent residues). (TRAP)
- PROVED coherent lower bound (n₀ ≥ 75D, 64H ≤ d ≤ D, 64(n₀ mod d) ≤ d): E = B + mR' + βH' ≥ (1/100)(Σc(d)d)(Σc'(n)/n²) — trivial rank-two remainder 2K_cΣ|c'|/n² attained up to 100. Every S ⊆ [64H, D] has coherent configuration (n₀ ∈ [Q,Q+2D), S' ⊆ S, |S| ≤ 128|S'|). Against diagonal: indicator rows on S' ⊆ (D/2,D]: E ≥ D|S'|H/(200(n₀+H)²), E² ≥ (1/80000)D³|S'|Hn₀/(n₀+H)⁴·D(a)D(b); primes S' ≍ D/log D, H ≍ D, n₀ ≍ Q: remainder exceeds diagonal by ≍ D^{5/2}/(Q^{3/2}√log D).
## FourierFormOfTheBernoulliKernelAndTheExactCrossScaleLoss (start)
- Nontrivial roots T_d: Σ_{η∈T_d}η^k = d[d|k] − 1; inversion pairing 1/(η−1) + 1/(η^{−1}−1) = −1 ⇒ Σ1/(η−1) = −(d−1)/2. Spectral forms: r_d(M) = −Σ_{η∈T_d}η^{M+1}/(η−1); Φ_d(M) = Σ_{η∈T_d}η^M/|η−1|² (POSITIVE-DEFINITE on ℤ/d, coefficients 1/(4sin²(πk/d)) > 0 sum to Φ_d(0) = (d²−1)/12).
- S(z) = Σ(c'(n)/n²)z^n, S₀ = Σ|c'|/n². Σ_n(c'(n)/n²)Φ_d(jn) = Σ_η|η−1|^{−2}S(η^j). Prime p, |S(ζ)| ≤ σ_p on nontrivial p-th roots ⇒ |Σc'(n)𝔅(p,n)/n²| ≤ ((p²−1)/12)(π²σ_p/6 + 2S₀/p²).
- EXACT CROSS-SCALE LOSS (c on primes): |B + mR' + βH'| ≤ (π²/72)Σ|c(p)|pσ_p + (S₀/6)Σ|c(p)|/p + ¾Σ|c(p)|p²Σ|c'|/n³. Rank-two remainder improves exactly by normalized Fourier mass σ_p/S₀ of large-scale coefficients at rationals k/p; coherent windows σ_p ≍ S₀. Type-II input at one modulus = size of Σc'(n)e(kn/p)/n².
## BlockEquidistributionSufficesForCrossScaleDispersion
- Block discrepancy Δ_H(c') = Σ_m|Σ_{block m}c'(n)/n²| (K blocks of length H). |ζ^t − 1| ≤ t|ζ−1| ⇒ |Σ(c'(n)/n²)ζ^n| ≤ Δ_H + H|ζ−1|S₀. Σ_{η∈T_d}|η−1|^{−1} ≤ (d/2)h_d (circle row sum). One modulus (truncate j at J, trivial |Φ_d| ≤ d²/8 beyond): |Σc'(n)𝔅(d,n)/n²| ≤ (π²/72)(d²−1)Δ_H + HS₀(d/2)h_dh_J + S₀d²/(8J).
- EVERY ROW (no support hypothesis): |B + mR' + βH'| ≤ (π²/72)Δ_HΣ|c(d)|d + (Hh_N²/2 + 1/8)S₀Σ|c(d)| + ¾Σ|c(d)|d²Σ|c'|/n³. Gain vs rank-two remainder S₀Σ|c|d: Δ_H/S₀ + H log²N/P + P/Q (c on [P,2P], c' above Q). Equidistribution of c'/n² in blocks of length H = o(P/log²P) ⇒ cross-scale remainder negligible; nonneg c' on one window of length P/64 keeps it rank-two size. REPLACEMENT HYPOTHESIS OF TYPE-II NO-GO = EXACTLY block equidistribution at scale of small moduli.
## ReciprocityFormOfTheBernoulliKernel (start)
- Σ_{j≥1}cos(2πjx)/j² = π²B₂(x), x ∈ [0,1]. Nontrivial roots = ω^k, |ω^k−1|² = 4sin²(πk/d). Cosine form Φ_d(M) = Σ_{k=1}^{d−1}cos(2πkM/d)/(4sin²(πk/d)). FINITE FORM 𝔅(d,n) = (π²/4)Σ_{k=1}^{d−1}B₂({kn/d})/sin²(πk/d). RECIPROCITY (nn̄ ≡ 1 mod d): 𝔅(d,n) = (π²/4)Σ_kB₂(k/d)/sin²(πkn̄/d) — {N/pq} ↔ p̄/q + q̄/p at second order. Primes p < q: 𝒢^{ec}(p,q) = D_p log q − pβ_p + (π²/(4q))Σ_kB₂(k/p)csc²(πkq̄/p) + O(¾p³/q²): fine structure = Dedekind-type cosecant–Bernoulli sum in q̄/p; beyond rank two, bilinear form in Kloosterman fractions kq̄/p.
- PROVED reciprocity form for two distinct primes (inverse exists): |𝒢^{ec}(p,q) − D_p log q + pβ_p − (π²/(4q))Σ_{k<p}B₂(k/p)csc²(πkq̄/p)| ≤ ¾p³/q².
## KuzminLandauGainForFlatSmallScaleRows
- Flat row c(d) = d on [D₁,D₂) (a_d = 1): column Col(n) = Σ_d𝔅(d,n); 𝔅 + π²/72 = (d²/2)Σ_jB₂({jn/d})/j²; via B₂ Fourier → reciprocal-phase sums T(x) = Σ_dd²cos(2πx/d), x = hjn. Phase increments x/(d(d+1)) monotone in [x/D₂², 1/2] while x ≤ X₀ = D₁(D₁+1)/2 ⇒ Kuzmin–Landau: |Σ_{D₁≤d<D'}e(x/d)| ≤ 3D₂²/(2x) + 1; Abel against increasing d²: |T(x)| ≤ 3D₂⁴/x + 2D₂².
- Flat column: |Σ_d𝔅(d,n) + (π²/72)(D₂−D₁)| ≤ (12D₂⁴/n + 8D₂² + 2W₂h_Jn/X₀)/(2π²) + W₂/(5J), W₂ = Σd². For c' above Q, [P,2P): rank-two remainder ≍ S₀P³ improves to ≍ S₀(P⁴/Q + PQ log P), gain P/Q + (Q/P²)log P ⇒ FLAT small-scale rows, ARBITRARY large-scale coefficients: diagonal quality for Q ≥ P^{3/2}log P (θ up to 4/3), BEYOND Type-II barrier Q ≥ P^{5/3}.
## DiscreteGallagherInequalityAndTheWindowSpectrum
- All row frequencies on μ_M (M = N!). Dirichlet kernel D(j) = Σ_{y<L}ω^{−yj}: Re D(j) ≥ L/2 when 4jL ≤ M. DISCRETE GALLAGHER: T ⊆ μ_M, 1 ≤ L, 4KL ≤ M: Σ_{j<K}|Σ_{ζ∈T}a(ζ)ζ^{A+j}|² ≤ (4M/L²)Σ_{ξ∈μ_M}|Σ_{y<L}1_T(ξω^y)a(ξω^y)(ξω^y)^A|² (arc sums; Parseval on μ_M) — Riemann sum of Gallagher's (πK)²∫|cluster|².
- Window energy: Σ_{X≤M<X+K}F_c(M)²/(M(M+1)) ≤ (4N!/(L²X²))Σ_ξ|arc cluster of κ(ζ)ζ^X|², κ(ζ) = Y_c(ord ζ)ζ/(ζ−1), resolution L/N! ≍ 1/K. Window energy below quadratic horizon governed by clustering of row's Farey spectrum at scale 1/X; coherent blocks of Type-II no-go = exactly such clusters.
## NumeratorSplitOfTheWindowEnergy
- Prime packet: F_c(M) = Σ_pΣ_{1≤a<p}u(p,a)ω_p^{aM}, u(p,a) = (c(p)/p)ω_p^a/(ω_p^a − 1). Split at a₀: small numerators a ≤ a₀ and p−a ≤ a₀ ⇒ one-numerator sums Ψ_{±a}(M) = Σ_pu(p,±a)ω_p^{±aM}; large numerators: |ω_p^a − 1| = 2sin(πa/p) ≥ 4min(a,p−a)/p ⇒ Σ_large|u|² ≤ Σc(p)²/(8a₀).
- RESULT: Σ_{X≤M<X+K}F_c²/(M(M+1)) ≤ (2/X²)(2h_{a₀}Σ_{a≤a₀}aΣ_M(|Ψ_a|² + |Ψ_{−a}|²) + (K + 2N² − 1)Σc(p)²/(8a₀)) (log-free large sieve on large part, Cauchy–Schwarz weights 1/a on small). Large numerators cost ≍ (K + N²)/(a₀X) relative to window diagonal ≍ Σc²/X. Below quadratic horizon only a ≲ P²/X matter; at θ just above 1, bounded number of numerators carries all energy.
## OneNumeratorClustersAreShortIntervalSums
- Fractions a/p = ω^{a(M/p)}, M = N!. Arc at ω^x collects primes with x ≤ a(M/p) < x+L; no wrap when 4PL ≤ aM; each nonempty arc has x ≥ aM/(4P), its primes form interval (aM/(x+L), aM/x] of length ≤ 16P²L/(aM). RESULT: if every twisted interval sum |Σ_{t₁<p≤t₂}u(p,a)ω_p^{aX}| ≤ B (length ≤ 16P²L/(aM)), then Σ_{X≤m<X+K}|Ψ_a(m)|² ≤ (4M/L²)(a(M/(2P)) + L)B². Ψ_{−a} = conj Ψ_a.
## TwistedShortIntervalCancellationGivesWindowDispersion
- Combined: window energy ≤ (2/X²)(2h_{a₀}Σ_{a≤a₀}a·2(4M/L²)(a(M/(2P)) + L)B_a² + (K + 2N² − 1)Σc²/(8a₀)). L = M/(4K): intervals length 4P²/(aK), factor 64K²a/P + 32K. |u(p,a)| ≤ |c(p)|/(4a); twisted square-root cancellation B_a ≤ η√(4P²/(aK))|c|_∞/(4a) for a ≤ a₀ = P²/(εX) ⇒ window energy on [X,2X) within ≍ (η²log² + ε)log P of diagonal at EVERY window P ≤ X ≤ P² (every θ ∈ [1,2]). Coherent blocks have B_a ≍ |I_a| ⇒ REPLACEMENT HYPOTHESIS IDENTIFIED EXACTLY: twisted square-root cancellation of packet over intervals of length P²/(aX) for first P²/X numerators.
## SharpConstantOfTheRankTwoRemainder
- Φ_d(M) ≤ Φ_d(0) = (d²−1)/12; |Φ_d| ≤ (d²−1)/12 for d ≥ 2. 𝔅(d,0) = π²(d²−1)/72; SHARP |𝔅(d,n)| ≤ π²(d²−1)/72 (equality at n ≡ 0 mod d). Sharp rank-two law (c(1) = 0): |B + mR' + βH'| ≤ (π²/72)Σ|c(d)|(d²−1)/d·Σ|c'|/n² + ¾Σ|c|d²Σ|c'|/n³. ATTAINED: n₀ divisible by every small modulus of nonneg c ⇒ ≥ (π²/72)Σc(d)(d²−1)/(dn₀²) − ¾Σc(d)d²/n₀³. Coherence at residue zero is extremal.
## LargeSieveDispersionForBoundedRows (start)
- Σ_{k≤m}1/k ≤ 2√m. |c| ≤ 1 on [1,Q₀] ⇒ |Y_c(e)| ≤ 2√(Q₀/e)/e.
- Bounded rows |c| ≤ 1 on [1,Q₀]: ΣY(e)²e⁴ ≤ 2Q₀²(Q₀+1), Σ|Y(e)|e³ ≤ Q₀²(Q₀+1) ⇒ |B + mR' + βH'| ≤ ½√(2Q₀²(Q₀+1))√(L+2Q₀²−1)√(Σc'²/n⁴) + ½Q₀²(Q₀+1)Σ|c'|/n³ (Möbius, Liouville, characters; no arithmetic input). Gain ≍ √(Q₀/L) vs rank-two remainder on Q₀ ≤ L ≤ Q₀².
## TwoSidedSignLawOfTheSecondOrderKernel
- Near residue d/2 (|n mod d/d − 1/2| ≤ 1/64): 𝔅(d,n) ≤ −d²/100 (first 16 terms: odd k give B₂ = (kσ)² − 1/12, even ≤ (kσ)² + 1/6; Σ ≤ −73/2000; tail ≤ d²/(12·16)). With 𝔅 ≥ d²/25 − 1/4 near 0: second-order term changes sign at full size ≍ d². Two primes: 𝒢^{ec}(p,q) − [D_p log q − pβ_p] ≤ −p²/(100q) + ¾p³/q² near half; ≥ (p²/25 − 1/4)/q − ¾p³/q² near zero. Pronic Gram of two primes oscillates in sign with q mod p at amplitude ≍ p²/q; no one-sided estimate improves rank-two remainder by more than a constant.
## FlatLargeScaleRowsAndTheTypeIGain
- Flat large row c'(n) = n on [A+1,A+L]: |S(ζ)| ≤ 2/((A+1)|ζ−1|) (Abel vs geometric partial sums ≤ 2/|ζ−1|); σ_p ≤ p/(2(A+1)) ⇒ |B + mR' + βH'| ≤ (π²/144)Σ|c(p)|p²/(A+1) + (Σ_I1/n)/6·Σ|c(p)|/p + ¾Σ|c|d²Σ_I1/n². Gain ≍ P/L + P/A; arbitrary small coefficients on primes ~ P, flat large on [Q,2Q]: diagonal quality for Q ≥ P^{3/2} (θ up to 4/3). TYPE-I row at EITHER scale passes Type-II barrier P^{5/3}.
## CrossScaleParityBlindnessOfThePronicGram
- 𝔅(d,n) = 𝔅(d, n mod d) ⇒ large-scale row enters second-order law only via weighted residue masses ρ_{c'}(d,r) = Σ_{n≡r(d)}c'(n)/n² and readouts R, H. PROVED: same residue masses modulo every small modulus of c ⇒ |ΔB + mΔR + βΔH| ≤ ¾Σ|c|d²(Σ|c'₁|/n³ + Σ|c'₂|/n³). CROSS-SCALE PARITY BLINDNESS: cannot distinguish primes vs products of two large primes with matched residue statistics, Liouville vs constant on rough integers. Parity must come from large-scale rows' own Gram or near-diagonal interaction. (TRAP)
## SharpConstantAttainedByPrimesInTheUnitClass
- Φ_d(0) − Φ_d(j) = ρ(d−ρ)/2 ≤ min(jd/2, d²/8) ⇒ π²(d²−1)/72 − (d/2)(h_d + 1/4) ≤ 𝔅(d,1) ≤ π²(d²−1)/72. Dirichlet (q ≡ 1 mod p, arbitrarily large): 𝒢^{ec}(p,q) − [D_p log q − pβ_p] ≥ (π²(p²−1)/72 − (p/2)(h_p + 1/4))/q − ¾p³/q², vs universal upper π²(p²−1)/(72q) + ¾p³/q². Extremal second-order coupling π²p²/(72q) realised within primes by Bézout seeds q ≡ 1 (mod p).
## TypeIIBarrierSurvivesTheRankTwoSideConditions
- Anti-coherence: 255d ≤ 512(n mod d) ≤ 257d (≥ d/512 residues for d ≥ 512); anti-coherent window [n₀,n₀+H), 512H ≤ d ⇒ near half ⇒ 𝔅(d,n) ≤ −d²/100; coherent window 64H ≤ d ⇒ 𝔅 ≥ d²/100. Anti-coherent shift: S ⊆ [512,D] ⇒ n₀ ∈ [Q,Q+2D) with |S| ≤ 1024|anti-coherent subset|.
- Three windows W₂ < W₁ < W₃ (W₁ coherent, W₂,W₃ anti-coherent, common modulus set relative size 2^{−27}); c' = c₁ − a₂c₂ − a₃c₃ (nonneg pieces, a ≥ 0): every piece pushes kernel term up; n₂ ≥ 150D ⇒ B + mR' + βH' ≥ (1/200)(Σc(d)d)(Σ|c'|/n²).
- Readout ratio ℓ = R/H = average of log n over support (log a·H ≤ R ≤ log b·H) ⇒ ℓ₂ < ℓ₁ < ℓ₃; a₂ = H₁(ℓ₃−ℓ₁)/(H₂(ℓ₃−ℓ₂)), a₃ = H₁(ℓ₁−ℓ₂)/(H₃(ℓ₃−ℓ₂)) ≥ 0 kill both readouts. PROVED: with R(c') = H(c') = 0, B(c,c') ≥ (1/200)(Σc(d)d)(Σ|c'|/n²). Two rank-two side conditions cannot bring Type-II below rank-two remainder size; barrier Q ≍ P^{5/3} INTRINSIC to bilinear form. Replacement: equidistribution across near-multiple and near-half windows. (TRAP)
## ResidueDiscrepancyIsTheExactCrossScaleLoss (start)
- Residue average of potential: Σ_{r<d}Φ_d(jr) = d(gcd(j,d)² − 1)/12 (roots with η^j = 1 are nontrivial gcd-th roots). Prime p: Σ_{r<p}𝔅(p,r) = π²(p²−1)/(72p) (average π²(p²−1)/(72p²), p² smaller than max).
- ℓ¹ residue discrepancy Δ_p(c') = Σ_{r<p}|ρ(p,r) − S'/p|, S' = Σc'/n². One prime: |Σc'𝔅(p,n)/n² − (π²(p²−1)/(72p²))S'| ≤ (π²(p²−1)/72)Δ_p(c'). DISCREPANCY LAW (c on primes): |B + mR' + βH' − (π²/72)S'Σc(p)(p²−1)/p³| ≤ (π²/72)Σ|c(p)|((p²−1)/p)Δ_p(c') + ¾Σ|c|p²Σ|c'|/n³. Cross-scale remainder at one modulus = residue discrepancy of large-scale weighted row modulo small primes at rate π²/72; equidistributed part costs only (π²/72)|S'|Σ|c|/p (gain p²). Rate attained (one class: Δ_p = 2S'(1−1/p); coherent windows; Bézout seeds). TYPE-II DISPERSION BEYOND θ = 1 AT ONE MODULUS ⇔ Σ_p|a_p|pΔ_p(c') = o(Σ_p|a_p|pS'): weighted ℓ¹ equidistribution of large-scale coefficients in residue classes to small prime moduli.
## ThirdOrderCrossScaleLawAndTheCubicBernoulliKernel
- Cubic potential Ψ_d(M) = (4ρ³ − 6(d−1)ρ² + 2d(d−3)ρ + d² − 1)/24 = (d³/6)B₃(ρ/d) + Φ_d/2: Ψ_d(M+1) − Ψ_d(M) = Φ_d(M+1), zero period sums, |Ψ_d| ≤ d³/6, interval sums ≤ d⁴/6; 2Ψ_d − Φ_d = (d³/3)B₃(ρ/d).
- Third summation by parts (Δw = 2/(M(M+1)(M+2)), Δ²w = 6/(M…(M+3))): Σ_{M≥A}r_d(M)w(M) = −Φ_d(A)/A² − (2Ψ_d(A) − Φ_d(A))/A³ + O(d⁴/A⁴) (error ≤ 3d⁴/A⁴).
- Cubic Bernoulli kernel 𝔅₃(d,n) = Σ_j(2Ψ_d(jn) − Φ_d(jn))/j³ = (d³/3)Σ_jB₃({jn/d})/j³ (depends on n mod d), |𝔅₃| ≤ d³. THIRD-ORDER LAW: |B + mR' + βH' − Σc'(n)(c(d)/d)(𝔅(d,n)/n² + 𝔅₃(d,n)/n³)| ≤ 6(Σ|c|d³)(Σ|c'|/n⁴). Second-order error ¾Σ|c|d²Σ|c'|/n³ IS the cubic term; new error smaller by d/n. Cross-scale form up to O(d³/n⁴) = function of residue classes of large moduli mod small ones at weights n^{−2}, n^{−3}.
## SmoothLargeScaleRowsAndTheCancellationOfBothKernels
- Cubic kernel odd: f_d(ρ) = ρ³/3 − dρ²/2 + d²ρ/6 = (d³/3)B₃(ρ/d), f_d(d−ρ) = −f_d(ρ) ⇒ Σ_{r<d}(2Ψ_d − Φ_d)(jr) = 0 ⇒ Σ_{r<d}𝔅₃(d,r) = 0. Periodic zero-sum g, |g| ≤ B ⇒ interval sums ≤ dB. Smooth weights y(0) = y(b) = 0: |Σy𝔅₃(d,n)| ≤ d⁴Σ|Δy|. Prime p: 𝔅(p,·) − m_p zero period sums, |·| ≤ p²/4; two summations by parts (weights vanishing at 0,1,b,b+1): |Σx(𝔅(p,n) − m_p)| ≤ (p⁴/2)Σ|Δ²x|.
- SMOOTH-ROW LAW (c on primes, c' in [2,N], x = c'/n², y = c'/n³): |B + mR' + βH' − (π²/72)S'Σc(p)(p²−1)/p³| ≤ Σ|c(p)|p³(½Σ|Δ²x| + Σ|Δy|) + 6Σ|c(p)|p³Σ|c'|/n⁴. Smooth at scale A (Σ|Δ²x|, Σ|Δy| ≲ S₀/A²) ⇒ errors ≍ S₀Σ|c|p³/A² ⇒ diagonal quality for A ≥ P^{4/3}: θ up to 3/2 for ARBITRARY small-scale coefficients. Sharp cutoffs stop at 4/3 (boundary terms of 𝔅); one order more smoothness moves barrier 4/3 → 3/2.
## DualNormOfTheCrossScaleFunctional
- Kernel statistic Λ_p(c') = Σ(c'(n)/n²)(𝔅(p,n) − m_p) + Σ(c'(n)/n³)𝔅₃(p,n). Cross-scale form = (π²/72)S'Σc(p)(p²−1)/p³ + Σ(c(p)/p)Λ_p(c') + O(6Σ|c|p³Σ|c'|/n⁴). DUAL NORM ATTAINED (c = sign Λ_p on S): sup_{|c|≤1 on S}|B + mR' + βH' − main| = Σ_{p∈S}|Λ_p(c')|/p up to fourth order. Type-II for arbitrary bounded small coefficients ⇔ bound on single-modulus linear statistics Σ_p|Λ_p(c')|/p (no bilinear structure left); for arithmetic rows = low-frequency exponential sums Σ_aW_p(a)Σ_n(c'(n)/n²)e(an/p).
## KernelMeanAtCompositeModuliAndTheAllRowsLaws (start)
- Residue mean m_d = (1/d)Σ_{r<d}𝔅(d,r) = Σ_{j≥1}(gcd(j,d)² − 1)/(12j²) ≥ 0; Σ_{e|j}1/j² = π²/(6e²); 0 ≤ m_d ≤ (π²/72)(τ(d) − 1) (equality structure m_p = π²(p²−1)/(72p²)); ≍ τ(d)/d² below max. All-rows laws (stated): |𝔅(d,·) − m_d| ≤ d²/3; smooth-row law and dual-norm reduction hold for every modulus (Möbius-type small rows on integers); equidistributed part O(|S'|Σ|c(d)|τ(d)/d).
- PROVED all-rows laws: periodic zero-sum D, |D| ≤ B, weights vanishing at 0,1,b,b+1: |ΣxD| ≤ 2d²BΣ|Δ²x|; |𝔅(d,·) − m_d| ≤ d²/3; m_d ≤ max. All-rows smooth law: |B + mR' + βH' − S'Σ(c(d)/d)m_d| ≤ Σ|c|d³((2/3)Σ|Δ²x| + Σ|Δy|) + 6Σ|c|d³Σ|c'|/n⁴. All-rows dual norm Σ_{d∈S}|Λ_d(c')|/d (attained; Λ_d uses m_d). Smooth-row exponent θ up to 3/2 and reduction of Type II to single-modulus statistics hold for Möbius-type small rows on integers.
## SharpCutoffTypeIStopsAtFourThirds (start)
- Density pigeonhole: periodic condition with ≥ d/K residues ⇒ some n₀ ∈ [Q,Q+2D) satisfies it for ≥ 1/(2K) share of S. Windows: near zero [0,d/8192] (density 1/8192), coherent end [d/64,d/32] (≥ d/128 residues for d ≥ 256).
- Centred kernel primitive G_p(n) = Σ_{k<n}(𝔅(p,k) − m_p): p-periodic, |G_p| ≤ p³/4, |G_p(b)| ≤ bp²/4, G_p(a) ≥ ap²/50 for 32a ≤ p (p ≥ 64). Flat row boundary term: Λ_p ≥ (G_p((A+L+1) mod p) − G_p((A+1) mod p))/(A+L) − (3/2)p³L/(A+1)².
- PROVED (sharp cutoff): left endpoint near zero (8192(A+1 mod p) ≤ p), right endpoint after coherent stretch ((A+L+1) mod p ∈ [p/64,p/32]) ⇒ G_p(a) − G_p(b) ≥ p³/3600; L ≤ (A+1)/50000 ⇒ Λ_p ≥ p³/(14400A). Two nested pigeonholes: S ⊆ primes in [256,D] ⇒ interval I, |S| ≤ 2²²|S'|; attained dual norm ⇒ |c| ≤ 1 on S' with B + mR' + βH' − main ≥ Σ_{S'}p²/(14400A) − 6Σp³Σ|c'|/n⁴. Primes S' ≍ P/log P, L ≍ A: ≍ P³/(A log P) vs diagonal ≍ A/√log P ⇒ exceeds diagonal for A ≤ cP^{3/2}. SHARP-CUTOFF TYPE-I ROWS REACH EXACTLY θ = 4/3; replacement = one order of smoothness (θ = 3/2). (TRAP)
## IteratedDifferencesAndRisingFactorialPronicWeights
- Rising product R(x,m); higher pronic weights u_k(M) = (k+1)!/R(M,k+2), u_0 = pronic weight; u_k(M) − u_k(M+1) = u_{k+1}(M); positive, antitone, u_k(M) ≤ (k+1)!/M^{k+2}, u_k(A+m) ≤ (k+1)!/(m+1)².
- Backward difference Δf(n) = f(n) − f(n+1). Leibniz bound: |Δ^r g| ≤ μ_r antitone ⇒ |Δ^s(fg)(n)| ≤ 2^sΣ_{t≤s}|Δ^tf(n)|μ_{s−t}(n). Step j: |Δ^r[m ↦ u_i(j(m+1)+t)]| ≤ j^r u_{i+r}(j(m+1)+t).
- Centred periodic primitive Y(n) = Σ_{k<n}X(k) − mean: periodic, zero period sum, |Y| ≤ 2p max|X|. Iterated summation by parts: x vanishing below s+1 and from b: |Σ_{n<b}xD| ≤ (2p)^{s+1}BΣ|Δ^{s+1}x| (D p-periodic zero-sum, |D| ≤ B).
## CrossScaleLawOfEveryOrder (start)
- Tail t_d(A) = Σ_{M≥A}r_d(M)w(M): exact B + mR' + βH' = −Σ_{n,d}c'(n)(c(d)/d)Σ_{j≥1}t_d(jn). Potential chain X₀ = r_d, Y_i = centred primitive of X_i, X_{i+1}(n) = Y_i(n+1): d-periodic, zero sums, |X_i| ≤ (2d)^i(d/2), |Y_i| ≤ (2d)^{i+1}d/2. Tail expansion t_d(A) = −Σ_{i<L}Y_i(A)u_i(A) + T_L(A), |T_L| ≤ (2d)^L(d²/2)u_L(A).
- LAW OF ORDER L+1 (stated): |B + mR' + βH' − Σc'(n)(c(d)/d)Σ_{i<L}Σ_jY_{d,i}(jn)u_i(jn)| ≤ 2^L(L+1)!Σ|c|d^{L+1}Σ|c'|/n^{L+2}. Each potential term depends on large modulus only via jn mod d.
- PROVED: |t_d(A)| ≤ (d²/2)w(A); tail expansion to any order with remainder |Σ_{M≥A}X_L u_L| ≤ (2d)^L(d²/2)u_L(A); Σ_j u_k(jn) ≤ 2(k+1)!/n^{k+2}; exact tail identity B + mR' + βH' = −Σc'(n)(c(d)/d)τ_d(n), τ_d(n) = Σ_jt_d(jn); law of order L+1 with constant 2^L(L+1)!.
## SmoothLargeScaleRowsOfEveryOrder (start)
- Smoothness norm 𝒮_L(c') = Σ_{t≤L}Σ_n|Δ^tc'(n)|/n^{L+2−t}. Stated: c on primes, c' on [L+1,N]: |B + mR' + βH'| ≤ C_LΣ|c(p)|(p^{L+1}𝒮_L(c') + p^{−1}Σ|c'|/n²), C_L = 2(L+1)4^L(L+1)!.
- Mechanism: p ∤ j ⇒ n ↦ Y_{p,i}(jn) is p-periodic zero-sum (unit multiplication permutes residues) ⇒ L−i periodic summations by parts; Leibniz + step-j bounds give 2^{L−i}(L+1)!j^{−(i+2)}𝒮_L, summable in j; p | j ⇒ constant kernel Y(0), contributes O(Σ|c'|/n²) (equidistributed baseline; Σ_{p|j}j^{−(q+2)} ≤ 2/p^{q+2}).
- EXPONENT LADDER: c'(n) = n²x(n), x smooth at scale A on [A,2A]: 𝒮_L ≍ A^{1−L}; c = 1 on primes in (P,2P] ⇒ diagonal quality for A ≥ P^{(L+2)/(L+1)}, θ up to 2K/(K+1) = 4/3, 3/2, 8/5, … → 2 (K = L+1 order). Sharp cutoffs not smooth beyond K = 2 ⇒ stop at 4/3.
- PROVED smooth-row law of every order (constant 2(L+1)4^L(L+1)!).
## LargeSieveWithTheMontgomeryVaughanConstant (start)
- Window sum of e(nθ) telescopes: 2i sin(πθ)Σ_{A<n≤A+K}e(nθ) = e((A+K+½)θ) − e((A+½)θ). With Montgomery–Vaughan cosecant inequality: δ-separated frequencies, any window of K integers: |Σ|Σb_re(nα_r)|² − KΣ|b_r|²| ≤ δ^{−1}Σ|b_r|² (two-sided); dual large sieve ≤ (K + δ^{−1})Σ|b|²; duality ⇒ primal Σ_r|Σx_ne(nα_r)|² ≤ (K + δ^{−1})Σ|x|².
- Distinct Farey fractions of order Q ≥ 2 are 1/(Q(Q−1))-separated (1/(qq') distinct denominators; 1/q equal) ≤ Q² − 1 ⇒ Farey large sieve constant N + Q² − 1 (Montgomery–Vaughan, removes factor 2 from window-sandwich N + 2Q² − 1); double form Σ_{q≤Q}Σ_{(a,q)=1}; multiplicative large sieve Σ_{q≤R}(q/φ(q))Σ_{ψ prim}|Σc_nψ̄(n)|² ≤ (N + R² − 1)Σ|c|²; Montgomery's sieve (in progress).
- Montgomery sieve with N + Q² − 1: |A|Σ_{p∈P}(p − ω_p)/ω_p ≤ N + Q² − 1; sieve bound |A| ≤ (N + Q² − 1)/L. Roots of unity of order ≤ Q: 1/(Q(Q−1))-separated (m·x ∈ ℤ, x ∉ ℤ ⇒ ‖x‖ ≥ 1/m) ⇒ large sieve over roots of unity with K + Q² − 1; two-sided window bound |Σ_k|Σa(ζ)ζ^k|² − KΣ|a|²| ≤ Q(Q−1)Σ|a|².
## ArithmeticLargeSieveWithTheMontgomeryVaughanConstant
- |A|Σ_{q≤Q sqfree}Π_{p|q}(p − c_p)/c_p ≤ N + Q² − 1 (Montgomery at each squarefree modulus + root-of-unity large sieve MV constant).
## ExactOrderOfTheVasyuninReciprocityDefect
- E(p,q) = Σ_{M≥1}(M mod p − M mod q)²/(M(M+1)) = π(V(q,p) + V(p,q)) + (q−p)log(q/p). New lower bound E(p,q) ≥ (q−p)/8 (on [p,q) residues differ by ≥ M/2). EXACT ORDER: h(1 + log⁺(p/h))/18 ≤ E(p,p+h) ≤ 12h(1 + log⁺(p/h)). Defect o(p+q) ⇔ h = o(p), then h log(p/h) + O(h); different sizes ⇒ order p+q.
## WindowSandwichWithTheMontgomeryVaughanConstant
- |Σ_{A<k≤A+K}s(k)² − KQ_Sel| ≤ N(N−1)Q_Sel at every phase (half of trapezoid 2N²−1). Optimal window sandwich constant ∈ [Φ(N) − 2, N(N−1)], Φ(N) = Σ_{q≤N}φ(q) ~ 3N²/π².
## FourierFormOfTheCubicKernelAndFourthOrderLargeSieve (start)
- Ψ_d(M) = Σ_{η∈T_d}(η/(|η−1|²(η−1)))η^M; 2Ψ_d − Φ_d = Σ w₃(η)η^M, w₃(η) = (η+1)/(|η−1|²(η−1)) = −η(η+1)/(η−1)³, |w₃| ≤ 2/|η−1|³, Σ_{T_d}w₃ = 0. {η^j = 1} = T_{gcd(j,d)}: quadratic zero modes sum (gcd²−1)/12, cubic zero modes sum 0 ⇒ for every d only η^j ≠ 1 survive in both layers of Λ_d. Stated: Farey Σ|ζ−1|^{−6} ≤ p⁶/1024 + dilated large sieve disperses third-order remainder into ℓ² term smaller by P/Q, deterministic remainder O(P⁴/Q³); bounds strong ℓ¹ dual norm uniformly over sign patterns.
- PROVED Fourier bounds at every modulus: σ₂(d) = max_{T_d}|S₂|, σ₃(d) = max|S₃| (S₃ = Σc'(n)/n³z^n): |Σ(c'/n²)(𝔅(d,n) − m_d)| ≤ (π²(d²−1)/72)σ₂(d) (subtracting m_d kills S₀ diagonal leak at every modulus); |Σ(c'/n³)𝔅₃| ≤ (π²/3)Σ_{T_d}|η−1|^{−3}σ₃(d); prime: |Λ_p| ≤ (π²(p²−1)/72)σ₂ + (π²p³/48)σ₃. All-moduli fourth-order Fourier cross-scale law: |B + mR' + βH' − S'Σc(d)m_d/d| ≤ (π²/72)Σ|c(d)|dσ₂(d) + (π²/3)Σ(|c(d)|/d)W₃(d)σ₃(d) + 6Σ|c|d³Σ|c'|/n⁴. m_p = primeKernelMean; T_p = primitive p-th roots.
- Dilated MV large sieve: Σ_{ζ∈T}|Σy_k(ζ^j)^k|² ≤ j(L + Q₀² − 1)Σ|y|². Σ_j√j/j³ ≤ 2. Large-sieve dispersion of centred quadratic statistics: Σ_p(|c(p)|/p)|Σ(c'/n²)(𝔅(p,n) − m_p)| ≤ ½√(Σc(p)²p²)√(L + Q₀² − 1)√(Σc'²/n⁴) (uniform over sign patterns of c); cubic statistics ≤ (1/8)√(Σc²p⁴)√(L+Q₀²−1)√(Σc'²/n⁶).
- Fourth-order large-sieve dispersion of the weighted dual norm Σ_p(|c(p)|/p)|Λ_p(c')| ≤ ½√(Σc²p²)√X√(Σc'²/n⁴) + (1/8)√(Σc²p⁴)√X√(Σc'²/n⁶), X = L + Q₀² − 1; cross-scale functional |B + mR' + βH' − equidistributedMain| ≤ same + 6Σ|c|p³Σ|c'|/n⁴. Hypothesis-free over all primes ≤ N (Q₀ = max(N,2), window [1,N]).
## SelbergCoordinateFourthOrderLargeSieveAndAllModuliDualNorm (start)
- Σ_{r<d}𝔅(d,r) = d·m_d. Quadratic residue-discrepancy bound at every modulus: |Σ(c'/n²)(𝔅(d,n) − m_d)| ≤ (π²(d²−1)/72)Δ_d(c'); cubic residue mass/discrepancy Δ_{d,3}: |Σ(c'/n³)𝔅₃(d,n)| ≤ d³Δ_{d,3}(c') (Σ_r𝔅₃ = 0). Unconditional all-moduli third-order law (primality removed): |B + mR' + βH' − S'Σc m_d/d| ≤ (π²/72)Σ|c(d)|((d²−1)/d)Δ_d + (3/4)Σ|c|d²Σ|c'|/n³; fourth-order version with cubic discrepancy + 6Σ|c|d³Σ|c'|/n⁴.
- Cyclotomic–Selberg bridge: η ∈ T_d ⇔ η ∈ primitiveRoots'(N) and ord η | d; Σ_{d≤N}(c(d)/d)Σ_{T_d}F = Σ_{2≤e≤N}Y_{N,c}(e)Σ_{prim e}F, Y_{N,c}(e) = Σ_{e|d}c(d)/d (divisor-overlapping moduli collapse to disjoint primitive families). Exact Selberg-coordinate spectral identities for both layers (filtered η^j ≠ 1); cutoff to primitiveRoots'(Q₀) if supp c ⊆ [1,Q₀].
- Fourth/sixth-order Farey moments in Selberg coordinates: Σ_{prim'(Q₀)}Y(ord η)²|η−1|^{−4} ≤ (1/64)ΣY(e)²e⁴; with |w₃|²: ≤ (1/256)ΣY(e)²e⁶. Selberg-coordinate large sieve: quadratic layer ≤ ½√(ΣY²e⁴)√X√(Σc'²/n⁴); cubic ≤ (1/8)√(ΣY²e⁶)√X√(Σc'²/n⁶). Fourth-order Selberg law (upgrade from third order, L + 2Q₀² − 1 → L + Q₀² − 1) + 6Σ|c|d³Σ|c'|/n⁴; all-inputs version (Q₀ = L = N). 𝔅₃(1,·) = 0, Λ₁ = 0.
- Bounded rows |c| ≤ 1 on [1,Q₀]: ΣY(e)²e⁶ ≤ 2Q₀⁴(Q₀+1) (|Y(e)| ≤ 2√(Q₀/e)/e); ΣY²e⁴ ≤ 2Q₀²(Q₀+1). ALL-MODULI DUAL-NORM LARGE SIEVE: for any S ⊆ [1,Q₀] (composite allowed), Σ_{d∈S}|Λ_d^{all}(c')|/d ≤ ½√(2Q₀²(Q₀+1))√X√(Σc'²/n⁴) + (1/8)√(2Q₀⁴(Q₀+1))√X√(Σc'²/n⁶) — sign witness c = ±1 linearizes ℓ¹ norm; bridge resolves divisor overlap. Bounded-row fourth-order law with 6Σ_{S}d³Σ|c'|/n⁴; all-inputs version.
## ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
- Damped Möbius c_ε = μ(d)d^{−ε}, mean m_ε = 1/ζ(1+ε), centred prefix A_ε(n), receiver E_T(ε) = Σ_{n≤T}A_ε(n)²/(n(n+1)). Bounded for ε ≥ 1/2; horizon-uniform bound at fixed ε < 1/2 = zero-free half-plane.
- Abel inequality with linear partial sums: |S(x)| ≤ Lx for x ≥ D, w ≥ 0 decreasing ⇒ |Σ_{D<d≤X}s(d)w(d)| ≤ L(2Dw(D+1) + Σw(d)). Blocks |Σ_{D<d≤X}s d^{−α}| ≤ 5LX^{1−α} (0<α≤½); tails |Σ_{d>D}s d^{−1−ε}| ≤ (2 + 1/ε)LD^{−ε}.
- RATE HYPERBOLA BOUND: |s| ≤ 1, |S(x)| ≤ Lx (x ≥ D), 1/4 ≤ ε ≤ 1/2: |A(n)| ≤ 3D^{1−ε} + 31LnD^{−ε} (short moduli ≤ Σd^{−ε}; long moduli via cofactor blocks; tail of mean).
- Vinogradov–Korobov ⇒ |M(x)| ≤ Bx e^{−√(log x)/12}. Split D = n e^{−√(log n)/20} ⇒ |A_ε(n)| ≤ K n^{1−ε}e^{−√(log n)/40} uniformly ε ∈ [1/4,1/2]. Trivial |A_ε(n)| ≤ 3 + 31n.
- PROVED: E_T(ε) bounded uniformly in T on the band ε ≥ 1/2 − 1/(80√(log T)) (absorbs n^{1−2ε} ≤ e^{√(log n)/40}; Σe^{−√(log n)/40}/n < ∞). Receiver-control damping moves from 1/2 to 1/2 − c/√(log T), paid by the zero-free region; fixed-width band = zero-free strip (not reached).
- Bézout interior energy on the same band: E^int_T(ε) ≤ 2E_T(ε) + 1/2.
## ReceiverBoundedInTheVinogradovKorobovBand
- σ(x) = (log x)^{3/5}(log log x)^{−5/3} (nondecreasing from exp(exp(25/9)); σ/log decreasing from exp(e); (4/9)σ(x) ≤ σ(z) when (4/9)log x ≤ log z ≤ log x). Full VK rate |M(x)| ≤ Bx e^{−κσ/24} ⇒ |A_ε(n)| ≤ K n^{1−ε}e^{−κσ(n)/240} on ε ∈ [1/4,1/2] (split D = n e^{−g/5}).
- PROVED: receiver (and interior energy) bounded uniformly on band 1/2 − κσ(T)/(480 log T) ≤ ε ≤ 1/2; width ≍ (log T)^{−2/5}(log log T)^{−5/3} > dlVP width (log T)^{−1/2} (max a Beurling system can guarantee). Extra width = Vinogradov mean value theorem = additive structure of ℕ. No fixed ε < 1/2.
## LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa
- Θ = sup Re ρ ∈ [½,1]. Littlewood |M(x)| ≤ Cx^{Θ+δ} (unconditional) + rate hyperbola with L = 2CD^{β−1}, D ≈ n^{1/(2−β)} ⇒ |A_ε(n)| ≤ (3 + 124C)n^{(1−ε)/(2−β)}, exponent < 1/2 ⇔ β < 2ε.
- PROVED: every Θ/2 < ε ≤ ½ admissible receiver damping; sandwich Θ − ½ ≤ receiverDampingRate ≤ Θ/2; receiverDampingRate < ½ ⇔ Θ < 1 (zero-free strip). Under RH (conditional corollary) rate ≤ ¼. Elementary pointwise transfer loses on sawtooth head Σμ(d)d^{−ε}{n/d}; sharp rate = Θ − ½ would be a mean-square (Mellin–Plancherel) statement.
## ParityPairSeparatedOnTheVinogradovKorobovBand
- Damped Möbius c_ε and parity twin c'_ε (≥ 0, squarefree support) have |W_{c'}(e)| = |W_c(e)| (equal Ramanujan coefficient moduli) ⇒ every sign-blind datum coincides.
- ρ_ε = Π(1 − p^{−1−ε}) increasing in ε; twin local factors 1/(p^{1+ε} − 2) decreasing; twin drift constant K⋆ = ρ_{1/4}/U_{1/4} > 0 uniform on ε ≥ 1/4. log(T+1) − log a ≤ Σ_{a≤n≤T}1/n.
- PROVED: on VK band, E_T(c_ε) ≤ E while E_T(c'_ε) ≥ ((K⋆/16)²/4)(log(T+1) − log 100), uniformly. Bound on band reads the signs of μ ⇒ paid by zero-free region of 1/ζ.
## ReceiverGrowthBelowHalfDampingAgainstThePeriodEnergy
- Fixed ε ∈ [1/4,1/2): period energy E_prim(N) ≥ N^{1−2ε}/10368 (top octave of moduli = N^{1−2ε} independent unit steps on period torus); receiver E_T(ε) ≤ C_εT^{1−2ε}e^{−κσ(T)/270} (split at √T; σ(n) ≥ (4/9)σ(T) for n ≥ √T; σ/log → 0).
- PROVED: E_N(ε)/E_prim(N) ≤ Ce^{−κσ(N)/270} → 0: pronic weighting below the first period carries a cancellation the period torus lacks; unconditional size exactly the VK factor. Growth exponent < 1 − 2ε at fixed ε < 1/2 would be a zero-free strip (not given).
## MultiplicativeWeightsAreDecidedAtThePrimesOnTheBand
- f multiplicative |f| ≤ 1. f(p) = −1 ∀p: f = g ⋆ μ, g = f ⋆ 1 vanishes at primes ⇒ g d^{−ε} in critical Wiener algebra, mass G_ε = Σ|g(q)|q^{−1/2−ε} ≤ G_{1/4}; convolution law ‖A_{g⋆c}‖ ≤ G‖A_c‖ + (√2+1)G|m_c| ⇒ PROVED E_T(f d^{−ε}) ≤ E_f uniformly on VK band. ρ_ε ≤ 1.
- f(p) = +1, f ≥ 0 ⇒ f ≥ μ² (f = 1 on squarefree); squarefree drift n Σ_{n<d≤2n}f d^{−1−ε} ≥ n(2n)^{−ε}/16 ⇒ E_T ≥ (log(T+1) − log 100)/1024 for all 0 < ε ≤ 1/2.
- Receiver of multiplicative weight decided by sign at primes (dilations k ↦ pk); higher prime powers invisible.
## OmittedResidueClassLawOfThePrimeRow
- Prime row c'_Q = Λ·1_{(Q,2Q]}; Λ_p(c'_Q) depends on n only via n mod p. Dirichlet (WeakPNT_AP) with linear rate: coprime class r carries W(Q)/(p−1) + o(1/Q), W(Q) = Σ_{Q<n≤2Q}n^{−2}, QW(Q) → 1/2 (telescoping). Class 0 omitted: at most one prime power in (Q,2Q] divisible by p ⇒ QM_0(Q) ≤ log(2Q)/Q → 0. Cubic part o(1/Q).
- PROVED OMITTED-CLASS LAW: Q·Λ_p(c'_Q) → −(𝔅(p,0) − m_p)/(2(p−1)) = −π²(p²−1)²/(144p²(p−1)), with 𝔅(p,0) − m_p = π²(p²−1)²/(72p²). Single-modulus statistic of the actual prime row is NOT small: sieve term of the omitted class, relative size ≍ 1/p vs trivial; a row equidistributed in every class incl. 0 has o(1/Q). Fixed moduli only.
## CrossScaleCouplingOfPrimePacketsWithThePrimeBlock (start)
- PNT on dyadic window via classes mod 2: QΣ_{Q<n≤2Q}Λ(n)/n² → 1/2. Fixed prime packet c on S: Q(B + mR' + βH') → −(π²/144)Σ_{p∈S}c(p)(1 − 1/p²): coupling = equidistributed main term × (−p) at each prime (omitted class 0 reverses the sign); positive packet couples negatively, weight 1 − p^{−2} independent of p's size. Fixed small scale only.
## MoebiusEquidistributionInTheResidueClassesOfAPrime
- Twisted hyperbola swap Σ_{n≤N}w(n)(f⋆g)(n) = Σ_d f(d)Σ_{m≤N/d}w(dm)g(m); μ log = −μ⋆Λ ⇒ Σ_{n≡a}μ(n)log n = −Σ_{p∤d}μ(d)Σ_{m≤x/d, m≡ad̄}Λ(m) (dm ≡ a ⇒ p ∤ d, one coprime class). Uniform Dirichlet over coprime classes: |Σ_{m≤y}(1_{m≡r}Λ − 1/(p−1))| ≤ εy + K. Coprime Möbius floor sum |Σ_{p∤d}μ(d)⌊x/d⌋| ≤ 3x (coprime harmonic Möbius ≤ p/φ(p)).
- PROVED: Σ_{n≤x, n≡a mod p}μ(n)log n = o(x log x), 0 < a < p (from L(1,χ) ≠ 0 mod p via WeakPNT_AP). Qualitative: no rate, no uniformity in p.
## SingleModulusCancellationOfTheMoebiusBlock (start)
- Möbius block μ_Q = μ·1_{(Q,2Q]}: coprime class masses Σ_{n≡r}μ(n)/n² = o(1/Q) (Abel against 1/(n² log n)); block mass o(1/Q) by M(x) = o(x) ⇒ class 0 also cancels. Möbius omits no residue class.
- ⇒ QΛ_p(μ_Q) → 0 and Q(B + mR' + βH') → 0 for fixed prime packets. PAIR: prime block QΛ_p → −π²(p²−1)²/(144p²(p−1)) ≠ 0, Möbius block o(1/Q). Sign cancellation within each residue class removes the sieve term. Fixed modulus, no rate, no uniformity.
## ShortWindowMeanSquareCarriesTheCrossScaleLoss (start)
- x(n) = c'(n)/n², X(z) = Σx(n)z^n; window average x̄ = x ⋆ 1_{[0,H)}/H has X̄ = B_H X, B_H(z) = (1/H)Σ_{i<H}z^i, B_H(1) = 1, |B_H| ≤ 1, |1 − B_H(ζ)| ≤ H|ζ−1| on circle. x̄ keeps mass.
- Σ_n y(n)Φ_d(kn) = Σ_{T_d}|η−1|^{−2}Y(η^k) for every row y; η ↦ η^k permutes T_p for p ∤ k; layers p | k read only mass ((p²−1)/12)Σy. Full layer ≤ (p²/8)‖Y‖_p; smoothed-away defect (1−B_H)X layer ≤ √(Hkp³/8)‖X‖_p (min(2,Hk|η−1|)² ≤ 2Hk|η−1|).
- ONE MODULUS: |Σx(n)𝔅(p,n)| ≤ (π²/48)p²‖X̄‖_p + |Σx|/6 + √(2Hp³)‖X‖_p, ‖X‖_p² = Σ_{T_p}|X(ζ)|².
- Cross-scale: |B + mR' + βH'| ≤ (π²/48)√(Σc²p²)√(L + H + 2Q₀²)‖x̄‖₂ + √(2H)√(Σc²p)√(L + 2Q₀²)‖x‖₂ + |Σx|Σ|c(p)|/(6p) + (3/4)Σ|c|p²Σ|c'|/n³. Loss splits into normalized short-window mean square ‖x̄‖₂/‖x‖₂ and √(H/P) (c on (P,2P]). A large-scale row cancelling in almost all windows of length H = o(P) beats the Type-II barrier at every cross-scale exponent (replacement hypothesis).
## MoebiusCancelsInAlmostAllLinearShortWindows
- Fibre mean square (RHTower.Sieve) = mean square over multiplicative windows [x/a,(x+h√x)/a], a ∈ [√x,2√x]. With √x = 2(Y−1), h = 2H_j every start t ∈ [Y,Y+D) is a fibre start of a unique outer factor; fibre (t,t+ℓ], H_j − 1 ≤ ℓ ≤ H_j + H_j(D+1)/(Y−1) + 1. Linear windows = fibres up to 2 + 2(H+1)/m points.
- Σ_{Q≤t<2Q}(Σ_{t<n≤t+H}f)² ≤ 32ε'm(H+1)²Q + 2Q(2 + 2(H+1)/m)² + mH² given fibre mean squares ≤ ε'h²√x at m scales.
- PROVED (Matomäki–Radziwiłł in linear windows): for H(Q) → ∞ monotone, ≤ Q, growing ≤ 1 per doubling: Σ_{Q≤t<2Q}(Σ_{t<n≤t+H}μ(n))² = o(H²Q).
## MoebiusBlockBeatsTheTypeTwoBarrier (start)
- Möbius block x(n) = μ(n)1_{(Q,2Q]}/n², window H = log₂Q ((log₂Q)² ≤ 4Q): Σx̄² ≤ (2/(H²Q⁴))Σ_t(Σμ)² + 32H²/Q⁵ + 2H/Q⁴ = o(Q^{−3}).
- PROVED: ∀ε > 0, large Q, rows c on primes p ≤ Q₀ with 8 log₂Q ≤ ε²p: |B + mR' + βH'| ≤ ε√(Σc²p²)√(Q + 2Q₀²)Q^{−3/2} + |Σμ/n²|Σ|c|/(6p) + (3/4)Σ|c|p²Σ|c'|/n³. First term ε × large-sieve size (attained by coherent rows = Type-II barrier) ⇒ Möbius block is NOT Type-II extremal; block-mass term o(1/Q) by PNT. Saving is MR strength o(1); power saving needs power cancellation of μ in almost all windows of length ≍ P.
- Window sum of μ1_{(Q,2Q]}/m² on interior window = (Σμ)/(t+1)² + O(4H²/Q³); |x(m)| ≤ 1/Q²; at most 2H boundary windows. MR for averaged block at H = log₂Q: Σx̄² ≤ ηQ^{−3} eventually.
## ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis (start)
- E_α(Q) = Σ_{Q≤t<2Q}(Σ_{t<n≤t+⌈Q^α⌉}μ(n))² vs trivial Q^{1+2α}. MoebiusPowerWindowSaving := ∃α ∈ (0,1), δ > 0, C: E_α(Q) ≤ CQ^{1+2α−δ}.
- PROVED EQUIVALENCE: MoebiusPowerWindowSaving ⇔ Θ < 1. (⇐) Littlewood M(N) ≪ N^{Θ+ε}, α = (1+Θ)/2, ε = (1−Θ)/4, δ = (1−Θ)/2. (⇒) windows telescope Σ_t(M(t+H) − M(t)) = Σ_{i<H}(M(2Q+i) − M(Q+i)) ⇒ |M(2Q) − M(Q)| ≤ √Q√E/H + 2H ≪ Q^γ, γ = max(1 − δ/2, α) < 1; halving induction M(N) ≪ N^γ; absolute-moment exponent law ⇒ Θ ≤ γ.
- TRAP: power gain past large sieve for Möbius row via short windows = zero-free strip (same wall as receiver below half damping).
- PROVED moebiusPowerWindowSaving_iff (MoebiusPowerWindowSaving ↔ Θ < 1).
## CentredPrimeBlockBeatsTheLargeSieve
- Window averages from window bounds: |x| ≤ B, interior windows sum ≤ G ⇒ Σx̄² ≤ Q(G/H)² + 2HB². Centred prime block c' = (Λ − 1)1_{(Q,2Q]}, |c'| ≤ log 2Q + 1. Huxley PNT in all windows H = ⌈(2Q)^α⌉, 7/12 < α < 1 ⇒ G = 2εH/Q² ⇒ Σx̄² ≤ ε²/Q³.
- PROVED: rows c on primes p ≤ Q₀ with 8H(log 2Q + 1)² ≤ ε²p: |B + mR' + βH'| ≤ ε√(Σc²p²)√(Q + 2Q₀²)Q^{−3/2} + |Σ(Λ−1)/n²|Σ|c|/(6p) + (3/4)Σ|c|d²Σ|c'|/n³. Threshold p ≥ Q^{α+o(1)}; α < 3/5 covers whole balanced regime P ≤ Q < P^{5/3}. Gain vs rank-two bound: (P/Q)^{1/2}·ε; vs large-sieve size √(log Q)Q^{−3/2}: ε/√(log Q). Omitted residue class (size P/Q in dual norm) is o of large-sieve size P^{5/2}Q^{−3/2} once P ≥ Q^{1/3+δ}.
## ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis (start)
- R(N) = ψ(N) − N; F_α(Q) = Σ_{Q≤t<2Q}(Σ_{t<n≤t+H}Λ − H)², H = ⌈Q^α⌉. PrimePowerWindowSaving ⇔ Θ < 1. (⇐) R(N) ≪ N^{Θ+ε}. (⇒) telescope + |R(a+i) − R(a)| ≤ i(log(a+i) + 1) ⇒ |R(2Q) − R(Q)| ≤ √Q√F/H + 2H(log 3Q + 1) ≪ Q^γ, γ = max(1 − δ/2, (1+α)/2); halving ⇒ R(N) ≪ N^γ; square-sample exponent law Θ = 1/2 + inf{c: Σ_{s<N}R(s²)/N² = O(N^{2c})} ⇒ Θ ≤ max(γ,1/2).
- Centred prime row gains over large sieve by o(1) unconditionally (Huxley), by a power exactly when ζ has a zero-free strip.
- PROVED primePowerWindowSaving_iff (PrimePowerWindowSaving ↔ Θ < 1); log(4Q) + 1 ≤ (4/η + 1)Q^η.
## DualNormOfTheActualRowsBeatsTheLargeSieve
- Cross-scale problem for bounded small-scale coefficients = single-modulus dual norm Σ_{p∈S}|Λ_p(c')|/p (sign pattern c = sign Λ_p attains it up to main + 4th-order error). |main(c)| ≤ (π²/72)|S'|Σ1/p for |c| ≤ 1 on primes.
- PROVED: Möbius block (8 log₂Q ≤ ε²p) and centred prime block (8⌈(2Q)^α⌉(log 2Q + 1)² ≤ ε²p): Σ_{p∈S}|Λ_p(c')|/p ≤ ε√(Σp²)√(Q + 2Q₀²)Q^{−3/2} + (1/6 + π²/72)|S'|Σ1/p + (3/4)(Σp²)Σ|c'|/n³ + 6(Σp³)Σ|c'|/n⁴. Single-modulus statistics of actual rows at moduli growing with window, from short-window cancellation (MR, Huxley), no character/modulus average. Power-saving form = QRH.
## CentredPrimeRowPassesTheCoherentBlockObstruction (start)
- Actual centred prime row Λ − 1 on [A, A+KH) ⊆ [Q,2Q] satisfies block-equidistribution replacement hypothesis unconditionally via Huxley, regime P^{1+δ} ≤ Q ≤ P^{12/7−δ} (7/6 < θ < 2).
- Huxley uniform in window length: 7/12 < α < 1: |ψ(x+h) − ψ(x) − h| ≤ εh ∀ x^α ≤ h ≤ x/2, large x (zero sums monotone in parameter; cx²/(h·h/M) ≤ cMx^{2(1−α)}; 12/5 zero-density below exponent 5/12).
- Block [a,a+H): |Σ(Λ−1)/n²| ≤ (H/a²)(ε + 6H/a). |Λ(n) − 1| ≥ 1/12 ∀n ⇒ mass S₀ ≥ KH/(48Q²), block discrepancy Δ_H ≤ 96εS₀.
- Rows c on (P,2P], blocks (2Q)^α ≤ H ≤ 4Q^α, Hh_N²/2 + 1/8 ≤ εP, 3P ≤ 2εQ: |B + mR' + βH'| ≤ 16εS₀Σ|c(d)|d = 16ε × rank-two bound. Below quadratic horizon coherent blocks obstruct only sign-blind classes; remaining: balanced regime Q ≍ P where cubic tail is rank-two size.
- Rows c on (P,2P]: PΣ|c| ≤ Σ|c|d, Σ|c|d² ≤ 2PΣ|c|d; c' above Q: QΣ|c'|/n³ ≤ Σ|c'|/n². PROVED exists_abs_rowBilinear_centredPrimeRow_le (16ε × rank-two).
## CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation (start)
- Every complete-period quadratic form is diagonal in Selberg coordinates Y_{N,c}(q): centred forms (variance, successor covariance/reserve, phase loss, primitive energy, above-parity variance, all lag covariances, tuple variances) depend only on (Y(2)²,…,Y(N)²); uncentred (Selberg totient form, Bézout coprime form, Franel gcd form, translated moments) on (Y(1)²,…,Y(N)²).
- PROVED: (1) invariance under every sign character ε(q) = ±1 (scaledSelbergRow); (2) ORBIT CLASSIFICATION: same mean + same lag covariances on 1..N ⇔ same (ℤ/2)^{N−1} sign orbit (lag-spectrum Möbius inversion); (3) pointwise response, prefix discrepancy, von Mangoldt readout LINEAR in signed Y: flipping q₀ shifts sieveSeq by −2Y(q₀)c_{q₀}(k), prefix discrepancy by −2Re(R_{q₀}(M))Y(q₀), readout by −2Λ(q₀)Y(q₀).
- (4) Explicit pair Y = δ₂ ± δ₃ (N ≥ 3): identical mean 0, variance 3, Bézout form −2, successor cov −2, reserve 5, phase loss 3/2, primitive energy 11/12, periodCov(1) = −2, (2) = 0, all tuple variances; pointwise responses differ by 2c₃(k) ≠ 0 at EVERY k (incl. trans-horizon k = N+1); prefix discrepancies differ by −2 at M = 1 and M = 3N+1; readouts log2 ± log3; renormalized prefix defects −4 vs 0. TRAP: complete-period quadratic data is sign-blind; trans-horizon/linear data separates.
- Faithfulness: sieveSeq of c^ε = sieveSeq of c at all integers ⇔ ε(q) = 1 at every active mode Y(q) ≠ 0 (mean of s² = Selberg totient diagonal form). c₃(k) ∈ {2, −1}, never 0. Prefix discrepancy of δ₂+δ₃ pair: −(M mod 2) ∓ (M mod 3); difference −2(M mod 3).
