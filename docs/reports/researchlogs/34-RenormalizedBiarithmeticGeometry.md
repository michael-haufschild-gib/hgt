# 34 RenormalizedBiarithmeticGeometry — mathematical facts log

## TheRenormalizationSurvivalLaw (imports only Mathlib)
- Regularized family Q_r with Q_r − s_rB → A entrywise; counterterm B; survivalCone B = {x : B(x,x) = 0}.
- Survival (quad_nonneg_of_regularized): Q_r ⪰ 0 eventually ⇒ A ≥ 0 on survival cone (any divergence s_r). counterterm_nonneg: s_r → +∞ ⇒ B ⪰ 0.
- Invariance: two renormalizations Q − sB, Q − tC (s → ∞, C ≠ 0) ⇒ t/s → c, B = cC (counterterm_eq_smul); survival cone scheme independent (survivalCone_eq_of_regularized).
- Finsler–Debreu (exists_quad_add_smul_pos): B ⪰ 0, A > 0 on nonzero null vectors of B ⇒ A + sB PD for large s (compact sphere). quad_nonneg_on_survivalCone_iff: A ≥ 0 on cone ⇔ ∀ε eventually A + sB + εI ⪰ 0.
- Scalar counterterm: survivalCone 1 = {0}; every A is the renormalized limit of PD forms A + sI (regularized_one_realizes): scalar divergence carries no positivity. Rank-one vvᵀ: cone = hyperplane ⟨v,x⟩ = 0. Rank-k divergence leaves codimension k.

## TheArchimedeanGermSurvivesOnItsPolarHyperplane
- latticeGerm G_r(z) = Σ_k r^k/(k + z) (Abel self-energy of z + ℕ). Hankel forms Σc_ic_jG_r(x_i + x_j) ≥ 0 (each level a Cauchy kernel 1/(k + x_i + x_j)).
- G_r(z) + log(1−r) → latticeGermLimit(z) = Σ_k(1/(k+z) − 1/(k+1)) = −ψ(z) − γ (Tannery/dominated Abel means + (1−r)log(1−r) → 0). latticeGermLimit 2 = −1 (ψ(2) = 1 − γ).
- Counterterm 𝟙𝟙ᵀ (divergence −log(1−r) independent of z). Survival: Σc_i = 0 ⇒ Σc_ic_j(−ψ(x_i + x_j)) ≥ 0 (neg_digamma_hankel_nonneg). Off the hyperplane nothing survives: one node x = 1 gives −1 < 0.

## TheCountertermRankDichotomy
- torsionGerm S r = gcd-twisted Abel torsion energy (AET twistedEnergy), PSD for r < 1; counterterm identity with divergence −log|1−r|; limit torsionLimit = −P(m,n) off diagonal, −I(n,n)/φ(n) on diagonal.
- Every renormalization of torsion germ has survival cone {0} (scheme independence). Limit indefinite on {1,q} for each prime power q: x = (1,t), form −2tΛ(q)/√q − t²c(q) < 0 for small t > 0 (orbit 1 has zero self-intersection, coupling Λ(q)/√q > 0).
- Every renormalization of lattice germ has survival cone {Σc = 0}, limit positive there, not positive off it. counterterm_rank_dichotomy: prime place positivity carried entirely by divergence; archimedean keeps it on a hyperplane. Positivity on prime side needs a twist lowering counterterm rank.

## ThePoleNodeCompletesTheArchimedeanGerm
- harmonicFn H(x) = ψ(1+x) + γ (harmonic numbers). Adjoining pole node (x = ½ shifted, i.e. order-one orbit/arithmetic point with self-energy −log(1−r)) with coefficient −Σc spends the hyperplane constraint: kernel H(x_i) + H(x_j) − H(x_i + x_j) PSD on x ≥ 0 (harmonicKernel_nonneg) = ∫_0^1(1−t^x)(1−t^y)/(1−t)dt. Matched cancellation: arithmetic point self-energy cancels archimedean polar divergence ⇒ positivity on whole space.

## TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations
- Periodic Abel germ Q_r(α,β) = Σ_k r^k a_α(k)a_β(k)/(k + 1 + x_α + x_β) (modes a_α q-periodic, nodes x_α ≥ 0): PSD (each level Cauchy form in C_αa_α(k)).
- Periodic p with mean μ: Σr^kp(k)/(k+w) + μ log(1−r) converges (mean part = lattice germ; mean-zero part Dirichlet test + Abel). Counterterm = Cesàro Gram M(α,β) = mean(a_αa_β); CᵀMC = mean square of Σ C_αa_α ⇒ survival cone = linear relations Σ C_αa_α ≡ 0 (scheme independent when M ≠ 0).
- Archimedean (all modes 1): relations = polar hyperplane. Torsion: modes = Ramanujan sums Re c_n; same order at several nodes ⇒ per-order zero sums are relations ⇒ positivity survives on them (ramanujanTwin_survival).

## TheRamanujanTwinsSurviveExactlyOnPerOrderRelations
- Ramanujan sums real; orthogonality over common period q: Σ_{k<q}c_m(k)c_n(k) = qφ(n)δ_{mn}. Relations among modes c_{ord α} ⇔ coefficients sum to 0 over each order (ramanujanRelations_iff).
- Twin law: every renormalization of the Ramanujan twin germ has survival cone {per-order zero sums} exactly. One node per order ⇒ cone {0} (prime-place no-go caused by orthogonality of Ramanujan modes). Matched cancellation for orbit of order n ≥ 2 only against a twin carrying the same mode c_n.

## TheRamanujanTwinsCarryThePrimes
- shiftedMode c_n(k+1). Pole-node block (x = 0) = AET torsion energy: T_r(m,n) = r·Σ_k r^k c_m(k+1)c_n(k+1)/(k+1). For m ≠ n entry → −I(m,n); Cesàro entry 0 by orthogonality.
- ramanujanTwin_carries_primes: renormalized limit A ≥ 0 on per-order relations, entries at two pole nodes of orders m ≠ n equal −I(m,n); orders m, mt: −φ(m)Λ(t) (von Mangoldt enters survival inequality through pole-node block).

## TheTwistedEntriesAreDigammaSums
- Closed form: periodic p (period q, mean μ, b = p − μ): lim(Σr^kp(k)/(k+w) + μ log(1−r)) = μG(w) + (1/q)Σ_{j<q}b(j)G((j+w)/q), G(z) = −ψ(z) − γ (group mean-zero part over full periods; Dirichlet test + Abel).
- Every entry of every periodic germ family (incl. Ramanujan twins) = finite combination of digamma at rational shifts of nodes (periodicGerm_limit_eq).
- Orbit intersections are digamma sums: m ≠ n, m,n | q: I(m,n) = −(1/q)Σ_{j<q}c_m(j+1)c_n(j+1)G((j+1)/q); φ(m)Λ(t) = same with n = mt, q = m·mt (von Mangoldt via ψ at rationals).

## TheDyadicAmplificationOfTheHeckeDefect (uses ConjugateDiagonalGeometry)
- Collided mass D(f) = Σ_ρ w_ρ (w_ρ = m_ρ|f̂|²); symmetric Hecke defect E(L) = Σ_ρ w_ρ(2cosh(2δ_ρL) − 2) (δ_ρ = depth = Re ρ − ½). Strip bound E(L) ≤ D(2cosh L − 2).
- Two-scale rigidity E(L)² ≤ D(E(2L) − 4E(L)) ⇒ E(2L) ≥ a_D(E(L)), amplify a_D(e) = 4e + e²/D; a_D(D(2coshθ − 2)) = D(2cosh 2θ − 2) (angle doubling).
- heckeDefect_dyadic_ge: E(L) ≥ D(2coshθ − 2) ⇒ E(2^kL) ≥ D(2cosh(2^kθ) − 2) ∀k (loss D fixed, non-scaling: stand-in for genus in Weil tensor-power argument). Sandwich with strip bound. Lossless downward transfer heckeDefect_le_of_dyadic_le.
- Growth decides blindness: E(2^kL) = O(exp(ε2^k)) ∀ε ⇒ E(L) = 0. riemannHypothesis_iff_dyadic_subexp: RH ⇔ ∀ compact C² test, ∀ε: E(2^k) ≤ C exp(ε2^k). Only one large dyadic scale needs a source-side bound.

## TheHeckeMomentProblem
- Depth levels k_ρ = 2cosh(2δ_ρL) − 2 ≥ 0; moments m_j(L) = Σ w_ρk_ρ^j: m_0 = D, m_1 = E(L), m_2 = E(2L) − 4E(L) (Stieltjes moment sequence of positive measure on [0,∞)).
- Hankel forms Σc_ic_jm_{i+j+s} = Σ_ρ w_ρk_ρ^s(Σc_ik_ρ^i)² ≥ 0. Null vector ⇔ polynomial Σc_iX^i annihilates every seen level. Shell rigidity: nonzero null vector of size n ⇒ < n seen depth levels (n = 2: CDG unit-shell rigidity). Log-convexity m_j² ≤ m_{j−1}m_{j+1} (j = 1: two-scale rigidity). Hecke defects at L, 2L, 3L,... are linear combinations of moments; finite theta prefixes compute all moments (CDG).

## IntegerThetaPrefixesReadTheDefectWithoutLoss (uses CDG FiniteThetaMetric)
- reading R_n(f,L,j) = finite integer theta prefix (integers ≤ n) reading of moment m_j(L): |R_n − m_j(L)| < ε uniformly for j|L| ≤ 2log(n+1), n ≥ N(ε) (CDG finiteThetaSource_uniform_moving_moments). Readings compute mass (j = 0), Hecke defect (j = 1), Hankel forms with error ε(Σ|c|)².
- heckeDefect_le_of_readings: one pair of readings at one dyadic scale 2^kL ≤ 2log(n+1): R_n(2^kL,1) + ε ≤ (R_n(0,0) − ε)(2cosh(2^kφ) − 2) ⇒ E_f(L) ≤ D(2coshφ − 2) (seen depth ≤ φ/(2L)). Conversely an effective angle θ forces readings > D(2cosh(2^kθ) − 2) − ε at all admissible dyadic scales. Prefix length enters only through 2^k|L| ≤ 2log(n+1).

## TheTerminalCeilingAndTheOneScaleBoundAreZeroFreeStrips (uses ACP terminals)
- Every zero of depth > a ascends (ACP) to a right terminal of depth > a ⇒ zeroFreeStrip_iff_terminal_ceiling: all depths ≤ a ⇔ all right terminals depth ≤ a. riemannHypothesis_iff_no_right_terminal.
- not_forall_kernel_le: w(2cosh(2dL) − 2) ≤ D(2cosh(2ϑL) − 2) ∀L fails if d > ϑ, w > 0 (at L = log M/(2(d−ϑ))). zeroFreeStrip_iff_heckeDefect_bound: |depth| ≤ ϑ ∀ρ ⇔ E_f(L) ≤ D(f)(2cosh(2ϑL) − 2) ∀f,L. No input weaker than a zero-free strip reaches either target (graded RH).

## TheGaugeChargeOfACoupling (uses BiarithmeticGaugeGeometry)
- IsSquare N ⇔ all v_p(N) even. flipGauge p (−1 at p): character (−1)^{v_p(N)}.
- Classification realSignBlind_iff_isSquare: coupling (n; a,b) satisfies σ(n) = σ(a)σ(b) ∀ real sign gauge ⇔ nab is a square. sourceKernel_twist_iff: source twist acts on kernel by conjugation σ(a)σ(b) for all real gauges ⇔ every coupling in support is square class.
- Square-class criteria cannot select the Euler point: twist = mode sign change x ↦ σx, so positivity criterion holds for Λ iff for λΛ (sourceForm_nonneg_twist_iff).
- Diagonal (1;a,a), ratio (n;a,an), product (ab;a,b) couplings blind (structural reason for gauge blindness of multiplicative lattice forms). Successor coupling a·(a+1) never square ⇒ charged: some real sign gauge flips a → a+1.

## LogCellsFixTheGauge
- Lattice dilation D_m (δ_a ↦ δ_{ma}) vs cell dilation M_m (I_a + log m = ⊔_{r<m}I_{am+r}, (M_mq)(n) = q(⌊n/m⌋)). Both satisfy Baumslag–Solitar M_mS = S^mM_m with successor shift S; M_m = Σ_{r<m}S^rD_m.
- Lattice dilation covariant at every gauge: U_ωD_m = χ_ω(m)D_mU_ω (blind). Dyadic cell dilation covariant up to scalar ⇔ ω = Euler gauge (cellDilate_two_covariant_iff: χ(2a) = χ(2a+1) = cχ(a) ⇒ c = 1 via 9 = 3², then χ ≡ 1 by halving induction).
- Finite horizon [1,X], X ≥ 4: covariance ⇔ ω(p) = 1 ∀ primes p ≤ 2X+1 (twice the reach of successor flatness N+1, BGG). Cells carry successor holonomy that pins the arithmetic point.

## TheCellHolonomyDefectCountsChargedCells
- Hilbert–Schmidt covariance defect of dyadic cell dilation on [1,X]: Def_X(ω,c) = Σ_{a≤X}(|χ(2a) − cχ(a)|² + |χ(2a+1) − cχ(a)|²). Real sign gauge: per cell (σ(2) − c)² + (σ(a)σ(2a+1) − c)².
- Charged cell: σ(a)σ(2a+1) ≠ σ(2). Def ≥ 2·#charged for every c; some c gives 0 ⇔ no charged cell.
- Liouville: charged ⇔ λ(a) = λ(2a+1); min defect ∈ [2N₊, 4N₊] (exactly 4N₊ at c = −1), N₊ ≥ 1 for X ≥ 2 (λ(2)λ(5) = 1). Quantitative cell holonomy = binary correlation of λ along a ↦ 2a+1.

## TheLiouvilleCellDefectGrowsPolynomially
- Charged ⇔ λ(2a) ≠ λ(2a+1). Sign change λ(u) ≠ λ(u+1) ⇒ a = 2u(u+1) charged (2a+1 = (2u+1)²). λ(k²) = 1, λ(2j²) = −1 ⇒ sign change in [⌊√(2j²)⌋², 2j²), disjoint windows.
- ≥ J charged cells below 8J⁴ ⇒ Def ≥ 2J on [1,8J⁴] for every c (fourth-root growth). Linear growth ⇔ positive lower density of sign changes λ(2a) ≠ λ(2a+1) (two-point correlation along (+1,×2)) — not proved.

## CriticalDiscsAndTheTerminalLens (uses ACP)
- Pair {ρ, 1−ρ̄}, ρ = ½ + b + iγ, at s = ½ + x + iy: contribution to 2Re ξ'/ξ = 2x(x² + (y−γ)² − b²)/(|s−ρ|²|s−(1−ρ̄)|²): negative exactly inside critical disc (radius |b| about ½ + iγ) for x > 0.
- Carathéodory region: right of line, off zeros, outside all critical discs ⇒ Re ξ'/ξ ≥ 0. RH empties every disc. IsTerminal p (ACP quadratic cone: depth_r² ≤ depth_p² + (height diff)²) ⇔ p lies in no critical disc.
- Terminal lens (p = ½ + a + iγ_p terminal, T = √(¼ − a²)): {x > 0, |y−γ_p| ≤ T, x² − a² + (y−γ_p)² ≥ 2T|y−γ_p|} (right of two radius-½ circles through p) lies outside every disc; zero-free except p for |y−γ_p| < T; Re ξ'/ξ ≥ 0 on it. Extends ACP outward ray to a sector of half-angle arctan(a/T).

## HarnackOnTheCaratheodoryRegion
- Strictly outside all closed critical discs ⇒ ξ ≠ 0 and u = Re ξ'/ξ is nonnegative harmonic. harnack_re_logDeriv_xi: disc B(c,R) right of line, strictly outside discs ⇒ (R−r)/(R+r)·u(c) ≤ u(s) ≤ (R+r)/(R−r)·u(c), r = |s−c|.
- Ray discs: terminal p = ½ + a + iγ_p, 0 < h < ½ − a: disc of radius ρh about p + h (ρ = a/(2(a+T)), T = √(¼−a²)) strictly outside every critical disc.
- exists_terminal_floor_spreads: ACP floor u(p+h) ≥ m/h + m/(2a+h) + c·a·log(|γ_p|+4) (m = multiplicity) holds up to factor 1/3 on disc radius ρh/2 about p + h.

## PositivityIsIrreversible (uses BGG Landau–Wronskian)
- PositiveDeformation Λ₀ → Λ: on a ray σ > σ₁, Λ₀'/Λ₀ − Λ'/Λ = Laplace transform of measure ν on (0,∞) with finite Laplace mass. Compose (measures add); mutual positive deformations ⇒ log derivatives agree on a ray (two nonnegative transforms summing to zero vanish). not_positiveDeformation_of_ne: a deformation changing the log derivative arbitrarily far right cannot be undone positively. Positive deformations = monoid without nontrivial units (chirality: outward splitting positive, inverse not).

## CollectivePacketsDiluteOverIndependentOrdinates (uses HTGeometry Kronecker, MPG Fejér)
- Positive packet P(t) = a_0 + Σ a_j cos(ω_jt) ≥ 0 (a_0 = pole share; a_j purchases). Kronecker dilution: ω ℚ-independent ⇒ Σ|a_j| ≤ a_0 (sharp, converse trivially nonneg). Peak at 0 ≤ 2a_0.
- Harmonic concentration: on γ, 2γ, …, Mγ the Fejér packet has pole share M+1, buys M(M+1) = M × pole share.
- Height law: harmonic progressions g_i,…,Mg_i along ℚ-independent generators ⇒ total purchase ≤ M·a_0 regardless of number of generators (packet nonneg on torus diagonal by Kronecker; quadrature over M+1 equally spaced diagonal nodes kills harmonics ≤ M). Generated clouds: ordinates Σ_i n_{ji}g_i with heights 1 ≤ Σn_{ji} ≤ M ⇒ purchase ≤ M·a_0.
- Collective amortization only through arithmetic relations; size = maximal height over independent basis; independent clouds worse than single ordinate (MPG multiFrequency_purchase_le_two).

## EveryLatticeCloudHasAFinitePurchaseBound
- Lattice cloud ω_j = Σ_i n_{ji}g_i (n ∈ ℤ, mixed signs allowed). Weighted heights h_j = Σ n_{ji}m_i (integer weights m). Weighted height law: 1 ≤ |h_j| ≤ M ⇒ packet buys ≤ M·a_0 (Kronecker to weighted diagonal + (M+1)-node quadrature).
- Admissible weights m_i = t^i exist (heights nonzero polynomials in t; finitely many bad t). exists_purchase_bound: every finite cloud of nonzero lattice ordinates has finite M.
- Difference packets: |Σe^{ix_it}|² = N + Σ_{i≠j}cos((x_i − x_j)t) ≥ 0 buys (N−1)× pole share. Purchase constant ∈ [largest difference set − 1, minimal max weighted height]; equal (= length) for harmonic progressions. Positive packets never amortize without bound.

## TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry
- Soft: two-scale rigidity and dyadic amplification hold for every finite nonnegative configuration (w_i, δ_i) (weighted Cauchy–Schwarz; ζ, golden datum, any fake): content for ζ is only transfer of a source-side bound.
- Selective: cells reject Liouville (not covariant; defect ≥ 2 for X ≥ 2), Euler passes. Square-class criteria accept Liouville twin (squareClass_liouville_iff).

## TheLawsOfRenormalizedBiarithmeticGeometry (capstone renormalized_biarithmetic_geometry_laws)
- 23 conjuncts: periodic germ survival on relations; torsion survival cone {0} + indefinite limit; digamma Hankel on hyperplane; harmonic kernel PSD; dyadic amplification; RH ⇔ dyadic subexp; square-class blindness; successor charged; cells fix gauge; terminal lens zero-free; irreversibility; Kronecker dilution; height law; Liouville cell sandwich; Ramanujan orthogonality; floor spreads; terminal ceiling ⇔ strip; one-scale bound ⇔ strip; φ(m)Λ(t) digamma sum; fourth-root Liouville defect; finite purchase; difference packets nonneg.
