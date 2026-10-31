# SelectiveMultiscaleArithmeticPositivity — facts log

## PositivityAtEveryRootSelectsTheVonMangoldtWeight (uses SSHA TheGaugeAtEveryRoot, RHTower WeilConeUniquenessUnconditional)
- AtomicPositiveAt λ φ κ: eventually in N, Q_λ ≥ 0 on all atomic tests of the dilated profile κ_Nφ(κ_N·) (width 1/κ_N) at points log n, n ≤ N.
- Full Weil positivity ⇔ positivity on real C² compactly supported tests.
- atomicPositiveAt_iff: for bounded |λ| ≤ Λ, smooth φ supported in [0,1] with ∫φ = 1, overlap growth of finite order: AtomicPositiveAt ⇔ RH ∧ λ = Λ on n ≥ 2 (Weil cone = {Λ} under RH, empty otherwise).
- Consequences: one weight at one root ⇒ RH; any family containing a weight ≠ Λ at some n ≥ 2 is not uniformly atomic-positive; Liouville-twisted Λ is never atomic-positive (λ(2) = −log 2).

## ThePoleHyperplaneIsTheHarmonicHyperplane (uses ALG ThePoleDefectPaysThePole, SSHA, AE)
- Translation: ∫g(u−c)e^{au} = e^{ac}∫g e^{au}. Atomic test f_x = Σ_{n≤N} x_n g(·−log n): A(f_x) = A(g)Σ x_n/√n, B(f_x) = B(g)Σ x_n√n (A, B = moments against e^{∓u/2}).
- W(f) = M(f) + 2A(f)B(f) (M = Markov form = archForm − prime sum); same pole term for every twin ωΛ.
- On the harmonic hyperplane Σ x_n/√n = 0: W(f_x) = M(f_x).
- Below the spacing, for multiplicative sign twins ω: W_ω(f_x) − W(f_x) = (∫g²)(P_N(x) − P_N^ω(x)). Archimedean diagonal and both pole moments cancel; the ζ/twin difference is purely prime.

## ThePoleHyperplaneSeparatesTheFullWeilForms (uses RAPT ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin, ALG HyperbolicityIsBlindTheSignIsNot)
- markovFinitePart φ₀ = 2·gammaHardyPhaseRate 0 + log(1/(wN)) + profileRobin φ + γ − ε − (e^{1/2}/2)w − markovCrossConstant·wN; defectFractionRetained c₀ = 1 − ε − 32e²·wN.
- exists_weilQuad_atomicTest_ge_of_harmonic: ∃G > 0, eventually in N, all widths w ≤ δ_N/2 with wN ≤ overlap bound and c₀ ≥ 0, every atomic test on the hyperplane: W(f) ≥ (φ₀ + c₀G)‖f‖² (pole term vanishes; poleDefect ≥ GΣx² on hyperplane).
- Gap-paid positivity where φ₀ + c₀G ≥ 0.
- Liouville twin's atomic prime form = ζ's at Liouville-signed coordinates.
- exists_liouville_weilQuad_add_le_of_harmonic: ∃G > 0 ∀ε, eventually ∃ nonzero hyperplane x with W_λ(f_x) + (G − 2ε)‖f_x‖² ≤ W(f_x) for every narrow profile g.
- Separation: one G does both. exists_liouville_weilQuad_lt_of_harmonic: on the hyperplane the Liouville twin is strictly below ζ (reverse of the positive cone, where ζ is the minimum of its gauge orbit).

## TheSelectiveGardingInequality
- harmonicSum ℓ(x) = Σx_n/√n; harmonicMass H_N = Σ1/n; poleProj removes (ℓ/H_N)u, u_n = n^{−1/2}; lands on hyperplane; mass |x|² − ℓ²/H_N.
- poleDefect D_N(x) = Σ_{mt≤N} Λ(t)(x_{mt} − x_m/√t)² is invariant under x ↦ x − c u.
- Selective Poincaré: ∃G > 0, ∀N ≥ 1, ∀x: D_N(x) ≥ G(|x|² − ℓ(x)²/H_N).
- Selective Gårding: eventually, every narrow atomic test: W(f_x) ≥ (φ₀ + c₀G)‖f_x‖² − c₀G‖g‖²ℓ(x)²/H_N + 2A(f_x)B(f_x). Gap acts on everything except the pole component, which the pole term reads.

## TheConductorTwoIsTheFirstExcitation (uses RAPT TheFullPrimeMatrixHasRamanujanSpectralPoints)
- Ramanujan profile of conductor m: quasimode of the full prime matrix P_N at energy log N − E_m, E_m = γ + log m + τ(m), τ(m) = Σ_{p|m} log p/(p − 1) (tame different). E_1 = γ (pole), E_2 = γ + 2 log 2.
- Prime 2 is the bottleneck: log m + τ(m) > 2 log 2 for m ≥ 3 (cases: m even ⇒ m ≥ 4; minFac 3: 27 > 16; minFac ≥ 5: log 5 > log 4). E_m − E_1 ≥ 2 log 2 with equality iff m = 2.
- atomicWeilForm N (horizonExtend x) = xᵀ P_N x. Eigenvectors orthonormal; on span{e_i, e_j}: Q = a²λ_i + b²λ_j, mass a² + b².
- eventually_exists_harmonic_atomicWeilForm_ge: ∀ε, eventually some nonzero x on the hyperplane with P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|² (plane of the eigenvectors near log N − E_1 and log N − E_2 meets the hyperplane).

## TheHyperplaneGapIsTheSelectiveMargin
- HasHyperplaneGap ω g: ∀ε, eventually, on Σx_n/√n = 0: P_N(ωx) ≤ (log N − γ − g + ε)|x|².
- ζ has a positive gap (RAPT exists_atomicWeilForm_le_of_pole_orthogonal); every ζ gap ≤ 2 log 2; Liouville sign has no positive gap (prime form reaches ceiling log N − γ on the hyperplane).

## TheSelectiveMarginIsTwoLogTwo (uses RAPT TheSpectralGapOfThePrimeFormIsTwoLogTwo)
- ζ has gap exactly 2 log 2 (IsGreatest); every sign gauge ω² = 1 has gap 0 (Robin–Euler ceiling P_N(y) + (1−ε)D_N(y) ≤ (log N − γ + ε)|y|², |ωx| = |x|); Liouville gap exactly 0; sSup difference = 2 log 2.
- Sharp selective Poincaré: ∀η eventually D_N(x) ≥ (2 log 2 − η)(|x|² − ℓ²/H_N) for all x.
- Sharp Gårding: reserve c₀(2 log 2 − η).
- Top plane meets every hyperplane Σx_n c_n = 0 at level ≥ log N − γ − 2 log 2 − ε ⇒ every sign gauge has gap ≤ 2 log 2 (x = ωy maps hyperplanes); ζ maximal among sign gauges (IsGreatest = 2 log 2).
- Zero weight has every gap: damping is not selectivity; extremal problem posed among sign gauges.

## AMarginNeedsHarmonicCorrelation
- P_N(x) and P_N(ωx) (ω² = 1) are unitarily equivalent; tops along pole b_n = n^{−1/2} and along ω_n b_n. gaugeHarmonicSum S_N(ω) = Σω(n)/n; H_N = S_N(1) ≥ log N.
- gaugeWitness x_n = (ω_n − S_N/H_N)b_n: on the hyperplane, mass H_N − S_N²/H_N; ωx = b − (S/H)ωb.
- atomicWeilForm_gaugeWitness_ge: P_N(ωx) ≥ P_N(b) − (S/H)²(log N + log4 + 4)H − 2|S/H|((log N + γ)|S| + B H), B = log4 + 4 + log2 + γ (rows of the prime form within B of log N − γ; bottom of prime form ≥ −(log N + C₀)|v|²).
- If S_N²/log N → 0: ∀ε eventually a nonzero hyperplane x with P_N(ωx) ≥ (log N − γ − ε)|x|² (ceiling); hence no positive gap. Bounded harmonic sums suffice; Liouville recovered via |Σλ(n)/n| ≤ 2.
- Contrapositive: positive gap ⇒ S_N(ω)² ≥ c log N infinitely often.

## FullCorrelationKeepsTheMargin
- Pole polarization: P_N(αb + z) = α²P_N(b) + P_N(z) + 2αΣR_n b_n z_n, R_n = mertensSum(N/n) + log n, |R_n − (log N − γ)| ≤ B.
- poleCoord α = ⟨y,b⟩/H_N, poleResidual z = y − αb on hyperplane, |z|² = |y|² − α²H.
- Row cost (z ⟂ b leaves only deviations): 2αΣR_n b_n z_n ≤ α²H/t + tB²|z|².
- Misalignment: y ⟂ ωb ⇒ ⟨y,b⟩² ≤ |y|²·2(H_N − S_N) (Cauchy–Schwarz with (1−ω)b; |(1−ω)b|² = 2(H − S)).
- S_N/H_N → 1 ⇒ gap 2 log 2 (ceiling pays αb, sharp gap pays z, α²H ≤ δ|y|²). Finite flips (ω = 1 eventually) keep gap 2 log 2 (H − S bounded, H → ∞).
- Margin decided at both ends by S_N/H_N: 2 log 2 if → 1; 0 if S_N² = o(log N).

## TheHaarFloorIsTwinBlind (uses ACS HaarCellEffectivity)
- roughWeilTw ω f = 2θ'(0)∫f² + Γ(f) − twistedPrimeSum ω f + (2cosh² − 2sinh² half-moments).
- Twisted prime sum of a balanced Haar section = quadratic form of Σ_m ω(m) e_m(a,b) (entries of ζ's Haar prime matrix, m ≤ 2X+1).
- |ω| ≤ 1 ⇒ |twisted entry| ≤ nonnegative ζ entry K_ab ⇒ prime charge ≤ Σ_a (16 + log(2a+1)/√2) h_a c_a² (row + column bounds; sign never used).
- Floor for every |ω| ≤ 1: W_ω(f_c) ≥ Σ_a ((1 − 1/√2) log a + 2θ'(0) − 20) h_a c_a²; one lower index A (A > exp((21 − 2θ'(0))/(1 − 1/√2))) gives W_ω ≥ Σ h_a c_a² on sections supported at a ≥ A, all twists at once, all horizons. Liouville twin included.
- Consequence: the high-detail floor carries no selective information; selective input is needed for coarse/low-index part.

## ALevelIsPaidByItsReserve (pure Mathlib)
- |b| ≤ βst, e ≥ δt² ⇒ 2b + e ≥ (1−θ)δt² − (β²/(θδ))s² for θ ∈ (0,1].
- RG step: margin μ on coarse ⇒ min(μ − β²/(θδ), (1−θ)δ) on refined.
- rgMargin recursion: after L levels ≥ min(μ₀, D) − Σ_{l<L} c_l; summable costs below min(μ₀, D) keep a uniform positive margin.
- Schur: D ≻ 0 ⇒ [[A,B],[Bᴴ,D]] ⪰ 0 ⇔ A − BD⁻¹Bᴴ ⪰ 0; correction only lowers the coarse form.
- Block dominance (Gershgorin for forms): Σ_i(δ_i − Σ_{j≠i} b_ij)x_i² ≤ total.

## TheCompleteSourceIsADyadicMultiresolution (uses SSHA TheGaugeBecomesVisibleAtTheCriticalExponent)
- logCell C_a = 1_{[log a, log(a+1))}; C_{2a} + C_{2a+1} = T_{log 2}C_a.
- RG step on cells 1..2X+1: c₁C₁ + T_{log 2}(Σ pair-averages·C_a) + Σ half-differences·(C_{2a} − C_{2a+1}).
- Multiresolution on 1..2^L − 1: Σ_{j<L} T_{j log 2}(c^{(j)}_1 C₁ + Σ_a d^{(j)}_a detail_a).
- Level-Toeplitz: translation-invariant functionals (every twisted Weil form Q_λ) have polarized level-j/level-k pairing depending only on k − j; diagonal blocks repeat at every level.

## ThePoleHyperplaneIsRenormalizationInvariant
- dyadicShift (Sx)_{2m} = x_m, odd entries 0: f_{Sx} at horizon 2N = T_{log 2}f_x; Weil form and mass unchanged.
- ℓ_{2N}(Sx) = ℓ_N(x)/√2: hyperplane invariant; ℓ additive; two-level combinations T_{log2}f_x + f_y of hyperplane tests are hyperplane tests at horizon 2N, pole term vanishes, gap-paid bound applies without any inter-level coupling estimate.

## ThePoleCouplesTheLevelsHyperbolically
- poleMomentA A(f) = ∫f e^{−u/2}, poleMomentB B(f) = ∫f e^{u/2}; shift by t multiplies by e^{∓t/2}. polePairing(f,g) = A(f)B(g) + A(g)B(f).
- Cosh law: pole pairing of f(·−s), f(·−t) = 2A(f)B(f)cosh((t−s)/2); ≥ |AB|e^{|t−s|/2} (dyadic: 2^{|k−j|/2}); vanishes for all pairs iff A(f)B(f) = 0. Pole couplings are never summable level costs unless zero.
- Level orbit F = Σc_j f(·−s_j): A(F) = A(f)Σc_j e^{−s_j/2}, B(F) = B(f)Σc_j e^{s_j/2}; W(F) = M(F) + 2A(f)B(f)(Σc_j e^{−s_j/2})(Σc_j e^{s_j/2}) — rank-two pole form.
- Any two coefficient vectors have a nontrivial combination with A(F) = 0 (≤ one negative pole direction). For s ≠ t: (e^{−s/2} − e^{−t/2})(e^{s/2} − e^{t/2}) < 0, so with AB ≠ 0 the two-level pole plane is hyperbolic.
- A(f) ≠ 0: orbit on pole hyperplane ⇔ Σc_j e^{−s_j/2} = 0; dyadic s_j = j log 2: Σc_j 2^{−j/2} = 0 (harmonic hyperplane of atoms at 2^j).

## SeparatedLevelsCoupleThroughTheChebyshevError (uses AID TheOrderedWeilSourceIsACenteredChebyshevDefect)
- ACS poleB = A, poleA = B.
- Gamma tail of an ordered pair with gap 2δ around cut b: |T(f,g)| ≤ πe^{−4δ}(‖f‖² + ‖g‖²) (boundary-mass damping).
- Separated: |W(f,g) + ∫_0^∞(ψ_err(h) − c)q'(h)dh| ≤ πe^{−4δ}(‖f‖² + ‖g‖²) for every centring c; also W(f,g) = A(f)B(g) − P(f,g) up to the same error; if A(f) = 0 then W(f,g) = −P(f,g) up to it.
- Copies of tests on [0,ℓ] at s, t ≥ s + ℓ: error πe^{−2(t−s−ℓ)}; dyadic levels j < k: π·4^{−(k−j−1)} (summable).

## TouchingLevelsCoupleUniformly (uses AID TouchingCellsPayTheFullMixedSource, ACS TheLambdaRingOfTheScalingSurface)
- Pairing of copies depends on t − s only; continuous tests on [0,ℓ] vanish at endpoints.
- ∀ℓ > 0 ∃C: |W(φ(·−s), ψ(·−s−ℓ))| ≤ C(‖φ‖² + ‖ψ‖²) for all s (AID ordered window mass bound, transported). Dyadic adjacent levels: one constant for all j.
- Every orbit coupling cost bounded; only the Chebyshev part at level distance ≥ 2 can fail summability.

## TheDyadicSignIsRigid (uses ACS TheFrobeniusSpanIsTheTowerOfTheScalingSurface, ArithmeticHodgeIndexSignatureLaw; ACP OnNonnegativeTestsZetaIsTheWorstTwin; RHTower XiMassShellPrimeMass, ThetaPrimeScheduleSpectralObservation)
- TowerPositive λ g ℓ: every finite window K ⊂ ℤ of T_{kℓ}g has Weil Gram with hermNegIndex 0; DyadicPositive = ℓ = log 2 (Hecke tower at ℓ = log p).
- Tower Grams are Toeplitz: entry (i,j) = lagW λ g ((i−j)ℓ) = W_λ(T_{(i−j)ℓ}(g⋆g̃)).
- 2×2 window: ‖H_ij + conj H_ji‖ ≤ Re H_ii + Re H_jj; tower positivity ⇒ ‖W(T_{−D}k) + conj W(T_D k)‖ ≤ 2 Re W(k).
- Two weights: lag correlations differ by the prime pairing of u = λ' − λ only (archimedean and pole shared). primeMass(u,g,s).
- Rigidity: both tower positive ⇒ primeMass(−D) + primeMass(D) ≤ 2(Re W_λ(k) + Re W_{λ'}(k)) at every lag.
- Nonnegative generator + one-signed u: mass nonnegative; unbounded mass along lags dℓ excludes both being tower positive (window {0,d}).
- Nonnegative nonzero C² generator: autocorrelation ≥ c > 0 on |x| ≤ r; mass ≥ c·Σ_{|log n − D| ≤ r} u_n/√n.
- λ and λ + εn^{−η} (0 < η < 1/2) never both tower positive at any ℓ (mass ≥ cε(1 − e^{−2r})e^{(1/2−η)dℓ} − cε), though interval sums differ by ≤ ε(b−a)a^{−η}: Brun–Titchmarsh/short-interval PNT (statements stable under relative o(1)) cannot decide the sign.
- Λ and Liouville twin (difference 2 log p on primes) never both tower positive at any ℓ > 0; mass ≥ c(e^{2r} − 1)e^{D/2 − 3r/2} via PNT for θ on the window (relative accuracy (e^{2r}−1)/(2(e^{2r}+1))).

## TheDyadicSignOfAPoleFreeGeneratorIsRH (uses ACS OnePrimeSeesTheWholeDefectOfZeta)
- Pole moments = transforms at ±i/2 (γ_1 = −i/2 for s = 1, γ_0 = i/2 for its reflection); 1 is not a nontrivial zero.
- exists_test_killing_deep_zeros_poleFree_small: for deep-sparse Z with 1 ∉ Z, finite F of right zeros, depth σ₀ > 1/2, ε > 0: C² test on [−ε,ε] with both pole moments zero, killing γ_τ, γ_{1−τ̄} for all deep right zeros τ ∉ F, and nonzero at those for τ ∈ F (adds τ = 1 to the killed set).
- Index law (deep-sparse, tempered, 1 ∉ Z): some window of the ℓ-tower of some pole-free generator supported in [−ε,ε] has ≥ n negative squares ⇔ n ≤ #outer eigenvalues. For ζ at ℓ = log p: outer eigenvalues p^{ρ−1/2}.
- RH ⇔ Λ tower positive along the p-tower of every pole-free C² generator supported in [−ε,ε] (one/every prime p, one/every ε). Dyadic case p = 2.
- Under RH: Λ tower positive for every C² compactly supported generator; Liouville twin and every n^{−η} perturbation (0 < η < 1/2) fail on every Hecke tower of every nonnegative nonzero generator (although Liouville dominates ζ on each nonnegative test).
- Support length vs log 2 irrelevant: no intermediate content at any overlap.
