# 53 SuccessorShellArithmetic — facts log

## TheNonRatioFormIsAFiniteSumOfShells (uses SpacingScaleHarmonicAnalysis TheRowsAtBoundedOverlap)
- Non-ratio prime form at width w: pairs (k, m, n), n ≠ km, |log(km/n)| ≤ w. shift h = n − km ∈ ℤ∖{0}; shellLag(k, h) = Σ x_m x_n β(log k − log(n/m)) over n = km + h; shellForm = 2Σ_k Λ(k)k^{−½} shellLag.
- Two orientations carry the same pairs: nonRatioLag = 2·upward. Shift bound |n − km| ≤ min(n, km)(e^w − 1).
- NR = Σ_{0<|h|≤H} Sh_h, H = ⌊N(e^w − 1)⌋. Shell count 2H; at w = c/N: ≤ 2c e^{c/N}, exactly 2⌊c⌋ eventually. Shells empty for k > Ne^w.
- Top band: shell h reads only partners n with |h| ≤ n(e^w − 1); at w = c/N, n ≥ |h|N/(c e^{c/N}). N(e^w − 1) < 1 ⇒ no shells, NR = 0.

## TheIntegralityOfTheShiftRepaysTheLogarithm (uses RAPT TheShellsRepayEveryConductor)
- Conductor-one energy subtracts shells 1 ≤ h < c with weights F_c(h) = ∫_{h/c}^1 G(u)/u du. Continuum shell sum ∫_0^c F_c(h)dh = c(∫φ)²/2 = pole charge.
- Continuum energy = self finite part log(1/(2πc)) + β/M → −∞ (negative for c > e^{β/M}/(2π)). Lattice gain = actual − continuum = log(2πc) − β/M + E(c) ≥ log(2πc) − β/M; gain − log(2πc) → −β/M (actual energy E(c) ≥ 0, → 0: marginal).
- Every conductor: period mean of Ramanujan c_m(h) = [m = 1]; continuum conductor-m energy = self finite part + log-type adjunction energy − γ → −∞; conductor lattice gain ≥ log(2πc) − β/M − adjunction(m) + γ, asymptotically equal. The unit gap |h| ≥ 1 alone repays the logarithm (cell 0 < h < 1 holds M log c of shell weight).

## FixedConductorPacketsArePositiveBelowTheNineteenthRoot (uses CAF WeilGrowingPackets; CACT CompleteConductorResidualsRetainTheirHorizonDecay)
- Improved residual: ‖(W − E_m)u_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²) (for 4(e+3)²c² ≤ N). Scaled by c⁷ (floor κc^{−7}): residual contributes c^{19/2}(log N)^{−1/2}, Gram error c⁹/log N; both → 0 iff 19α < 1.
- Every fixed finite family of distinct conductors is positive for all coefficients along c_N = (log N)^α, 0 < α < 1/19 (improves CAF's 1/40). Exponent 19 = 2·7 + 5 (twice the floor exponent + residual exponent).
- Diagonal argument: some unbounded, non-effective Q(N) → ∞ with span{u_1, …, u_{Q(N)}} positive along the same schedule.

## TheShellsAloneCostTheSquareOfTheOverlap (uses RAPT ThePrimeFormCollapsesOnThePoleProfile, TheDeficitOfThePrimeFormIsADirichletEnergy; ArithmeticLorentzianGeometry TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing)
- Top band T = {n ≤ N : Ne^w < 2n}: shell partners never bases. Pole row R(n) = Σ_{ℓ≠n} b_ℓ Λ_N(ℓ)β(log ℓ − log n). Λ_N(ℓ) = log ℓ for ℓ ≤ 2N+1 (only d = 1 can exceed N) ⇒ rows prime-free for e^w < 2.
- Base collapse: x = pole vector b on all bases (2m ≤ Ne^w) ⇒ NR(x) = 2Σ x_n R(n). Witness x_η = b + η b 1_T: NR(x_η) = NR(b) + 2ηΣ_T b_n R(n); NR(b) ≥ 0 for nonnegative bump; Σ_T b R ≥ (log(N/2)/N)·(top-band off-diagonal Gram).
- Top-band Gram: atoms in a window of log-length log 2 ⇒ Cauchy–Schwarz Σ_{n,ℓ∈T} β ≥ (|T|∫g)²/log 2. Witness defect: D(x_η) = η²D(b1_T) ≤ η² log N Σ_T 1/n (top-band bases have only trivial edge t = 1); Σ_T 1/n ≤ 2; N(1 − e^w/2) ≤ |T| ≤ N/2 + 1; mass Σ x_η² = H_N + (2η + η²)Σ_T 1/n.
- Floor: if eventually NR(x) ≤ G(εD(x) + C S(x)) for all x at width c/N (nonnegative profile), then C ≥ A⁺²/(2ε), A = cq/(4 log 2) − ½, q = (∫φ)²/∫φ² (|T|/N → ½, H_N/log N → 1, optimize η = A⁺/(2ε)). At ε = a c^{−7}: C ≥ A⁺²c⁷/(2a) ~ c⁹. Separate shell payment costs order c²/ε; the c¹⁶ confinement exponent is intrinsic to paying shells apart from the pole.

## TheTwinDefectIsASuccessorDisagreementShell
- Completely multiplicative sign gauge ω (±1): gauge factor ω(k) − ω(m)ω(n) = ω(k)(1 − ω(km)ω(n)); with n = km + h this is ω(k)(1 − σ_h(km)), σ_h(ℓ) = ω(ℓ)ω(ℓ+h) (successor sign; 1 − σ ∈ {0, 2}).
- Twin prime form − ζ prime form of the gauged vector = Σ_{0<|h|≤N(e^w−1)} twinShellForm(h): shells carried by pairs (m, km + h) whose product and partner disagree in sign. Shifts with agreement are invisible. Below the spacing (no shifts) twins coincide. A selective inequality separating ζ from twins must read shells through successor signs.

## TheShellsAndThePoleCancelOnTheTopBand (uses RAPT TheCompletedShellEnergyIsAPositiveFourierIntegral; RHTower LogWindowPrimeNumberTheorem)
- Cell comparison: |F'| ≤ K on [a, a+m] ⇒ |Σ_{k<m}F(a+k) − ∫F| ≤ mK. Atom autocorrelation β_w(s) = w·A(s/w), derivative A'(s/w) bounded; β_w(t) = 0 for |t| ≥ w.
- Laplace factorization at ½: ∫e^{u/2}β = a₋a₊ (a∓ = ∫g e^{∓u/2}). Pole moments of an atomic test: (∫f e^{−u/2})(∫f e^{u/2}) = a₋a₊(Σx_n n^{−½})(Σx_n √n); on the witness = a₋a₊(H_N + ηS_T)(N + η|T|).
- Row integrand (log t/√t)β(log t − log n): derivative O((1 + log 2n)(G + A₁)/n^{3/2}) on [n/2, 2n]; substitution t = n e^u: ∫ = √n(log n·∫e^{u/2}β + ∫u e^{u/2}β).
- Pole row as lattice sum: for n in top band (w ≤ ¼, N ≥ 8), b_n R(n) = log n·∫e^{u/2}β + ∫u e^{u/2}β − G log n/n + O(b_n(n(e^w − e^{−w}) + 2)K_n), K_n = ((n/2)√(n/2))^{−1}(1 + log 2n)(G + A₁) (prime-free row, cells A..B around n e^{±w}).
- Joint block 2·Pole − NR along x_η = const + 2η·jointWitnessCoefficient + 2η²a₋a₊S_T|T|; coefficient = a₋a₊(H_N|T| + N S_T) − Σ_T b_n R(n).
- Finite-horizon bound (N ≥ 8, 4c ≤ N): |coeff| ≤ 17cG + 2G log N + (18c + 24)(2 + log N)(G + A₁)/N (|∫e^{u/2}β| ≤ 4wG, |∫u e^{u/2}β| ≤ 4w²G). Fixed c: |coeff| ≤ K·G(1 + log N) while each term separately ≍ Gcq log N — shells and pole cancel at order c; joint payment removes the c²/ε obstruction.

## TopBand/UniformJointCancellation
- One profile constant K: |jointWitnessCoefficient| ≤ K·G·(c + 1 + log N) for all 1 ≤ c ≤ N/4, N ≥ 8 (cell remainder ∝ (G + A₁)/N retained). For 1 ≤ c ≤ log N: ≤ 2K·G(1 + log N), uniform in overlap.

## TopBand/PeriodicShellWindows (uses RAPT PeriodicPairSumsOfADecreasingKernelAreLinear)
- Abel: partial sums of ψ bounded by P, |F| ≤ M, |F'| ≤ K on window of length L ⇒ |Σ F(a+i)ψ(i)| ≤ P(M + LK). Periodic mean-zero ψ (period q, |ψ| ≤ B): partial sums ≤ 2qB.
- shellPartnerKernel (√t)^{−1}β(log t − log ℓ): derivative bounded by ((ℓ/2)√(ℓ/2))^{−1}(G + A₁) on [ℓ/2, 2ℓ]. Weighted periodic window sum (width absorbs endpoint cost: L ≤ 3wℓ + 2, wℓ ≥ ½): |b_ℓ Σ kernel·ψ| ≤ (4 + 56(¼ + A₁/M))qU·G/ℓ.
- topBand = Icc(⌊Ne^w/2⌋ + 1, N). Periodic cancellation survives horizon and shell cutoffs: same bound for the top-band sum (ℓ ≥ 4, w ≤ ¼).

## TopBand/WeightedBaseCollapse
- horizonDivisorCoefficient ψ N ℓ = Σ_{d|ℓ, ℓ/d ≤ N} Λ(d)ψ(ℓ/d); product-fibre regrouping Σ_k Σ_m Λ(k)ψ(m)F(km) = Σ_ℓ coeff(ℓ)F(ℓ); |coeff| ≤ B log ℓ for |ψ| ≤ B.
- Base profile x = b·a on bases (2m ≤ Ne^w): NR(x) = 2Σ x_n shellCoefficientRow(a)(n) (top band never a nonzero base).
- Perturbed profile b·a + η·1_T b·ψ: NR = NR(b·a) + 2η·shellTopCoefficient (no quadratic shell term); pole moments = a₋a₊(Σa_n/n + ηΣ_Tψ/n)(Σa_n + ηΣ_Tψ). Joint block 2·Pole − NR = const + 2η·jointTopCoefficient + 2η²a₋a₊(Σ_Tψ/n)(Σ_Tψ).
- shellTopCoefficient = Σ_ℓ coeff(ℓ)·b_ℓ Σ_T kernel(ℓ, n)ψ(n) − G Σ_T ψ(n)coeff(n)/n (smooth partner sums + removed ratio diagonal).

## TopBand/NonpolarJointCancellation (uses RAPT TheWeilEnergiesOfTheArithmeticModes; HTGeometry FiniteShiftedHarmonicAbelBounds; SAHT OneArithmeticRemainderControlsEveryRamanujanResidual)
- Partner kernel vanishes for products 2ℓ ≤ N on the top band. Product sum (periodic cancellation in partner, divisor mass ≤ B log ℓ): ≤ 4K·BqUG(1 + log N). Ratio diagonal: ≤ 2BU log N. shellTopCoefficient ≤ (18 + 224(¼ + A₁/M))BqUG(1 + log N).
- Periodic interval sums ≤ 2qU (endpoint-independent); top-band moments: |Σ_Tψ| ≤ 2qU, |Σ_Tψ/n| ≤ 4qU/N. Bounded profile moments: |Σa/n| ≤ B(1 + log N), |Σa| ≤ BN. |a₋a₊| ≤ G (w ≤ ¼). Polar cross terms ≤ 6BqUG(1 + log N).
- One profile constant K: |jointTopCoefficient| ≤ K·BqUG(1 + log N) for every bounded base a, mean-zero periodic ψ, 1 ≤ c ≤ N/4, N ≥ 8. Ramanujan profile c_m(n)/√(φ(m)n) (m ≥ 2): ≤ K·mφ(m)G(1 + log N); this is exactly half the linear coefficient of the actual Ramanujan top-band witness.

## TopBand/RamanujanDivisorMoments (uses CACT TheNearGammaAndDownwardPrimeRowsCancel; RAPT TheWeilEnergiesOfTheArithmeticModes, EveryFiniteFlipSetHasAnExactResolutionThreshold; BVI DilationJumpValuationClock; RHTower PMPowerDampedMobiusRamanujanMoment)
- Logarithmic divisor jet J_m(n) = Σ_{d|m, d|n} μ(m/d)d log d: period m, period mean Λ(m). Centered normalized jet (J − Λ(m))/√φ(m) periodic, mean zero, bounded by (jetBound + Λ(m))/√φ(m).
- For ℓ ≤ 2N: horizon divisor coefficient of normalized Ramanujan mode = log ℓ·mode(ℓ) − J_m(ℓ)/√φ(m).
- Σ_{n≤N} mode_m(n)/n → −Λ(m)/√φ(m) (m ≥ 2) with remainder ≤ 2m√φ(m)/(N+1).

## TopBand/RamanujanDivisorSpectrum (uses RHTower DirichletLogDerivation, Deninger DeningerVonMangoldtMoebiusConvolution; RAPT TheAdjunctionEnergySeparatesValuations)
- J_m(n) = log m·c_m(n) + Σ_{d|m} Λ(d)c_{m/d}(n) (logarithmic differentiation of μ * divisibility source; nonnegative conductor coefficients). J_m − Λ(m) = log m·c_m + Σ_{d|m, d≠m} Λ(d)c_{m/d} (nonpolar conductors only).
- At conductor multiples m | n: J_m(n) = φ(m)(log m + tameDifferent(m)); |J − Λ(m)| ≤ φ(m)(log m + tameDiff) − Λ(m), attained at every multiple. |centered jet| ≤ 2√φ(m) log m.

## TopBand/RamanujanDivisorPlancherel (uses ArithmeticIntersectionTheory TheDifferentOfATorsionOrbit)
- Ramanujan orthogonality over common period q: Σ_n c_k c_l = [k = l]qφ(l); packet Plancherel Σ_n(Σ b_k c_k)² = qΣ b_k²φ(k).
- Conductor weights of J_m: [k = m]log m + Λ(m/k) ≥ 0. Σ_{n<m} J² = m(φ(m)log²m + Σ_{d|m}Λ(d)²φ(m/d)). Period mean of centered jet² = log²m + (Σ Λ(d)²φ(m/d) − Λ(m)²)/φ(m) ≤ 2 log²m (using Σ Λ(d)²φ(m/d) ≤ φ(m)log²m).
- Period absolute mass: Σ|centered jet| ≤ 2m log m; normalized mode has unit period mean square, Σ|mode| ≤ m (totient-free).

## TopBand/FullShellRows
- Shell window [⌊n e^{−w}⌋, ⌊n e^{w}⌋ + 1) ⊆ [n/2, 2n], length ≤ 3wn + 2 (n ≥ 4, w ≤ ¼); partner kernel vanishes off it; complete row = window sum.
- Log substitution: ∫ partner kernel = √n·∫e^{u/2}β (pole moment). Width pays variation and endpoints: b_n(G/√(n/2) + L·K) ≤ (2 + 28(¼ + A₁/M))G/n for wn ≥ ½.
- Full periodic mean-zero row: |b_n Σ kernel·ψ| ≤ (4 + 56(¼ + A₁/M))qU·G/n. Constant row: |b_n Σ kernel − ∫e^{u/2}β| ≤ (2 + 28(…))G/n (lattice quadrature Oφ(G/n)). With log weight (rowIntegrand): ≤ (4 + 56(…))qUG(1 + log 2n)/n.

## TopBand/PeriodMassShellRows
- Mean-zero periodic ψ: every interval sum ≤ period absolute mass Σ_{n<q}|ψ(n)|. Abel with interval bound P (no pointwise amplitude): full row |b_n Σ kernel·ψ| ≤ (2 + 28(¼ + A₁/M))P·G/n; log row ≤ same·(1 + log 2n).
- Ramanujan interval sums ≤ m (totient-free, from Plancherel); centered jet intervals ≤ 2m log m. Full Ramanujan row cost ∝ m·G/n; centered-jet row ∝ 2m log m·G/n.

## TopBand/MixedPolarCancellation
- fullShellReading (row incl. ratio diagonal). shellTopCoefficient = Σ_T ψ·fullShellReading(horizon coeff) − G Σ_T ψ·coeff/n (kernel symmetry b_ℓ k(ℓ,n) = b_n k(n,ℓ)).
- For ceil(Ne^w) ≤ 2N: reading of horizon Ramanujan coefficient = reading(log·mode) − reading(centered jet) − (Λ(m)/√φ(m))·reading(1). Joint coefficient (Ramanujan base, constant top partner) decomposes so the jet mean Λ(m)/√φ(m) exactly cancels the harmonic pole moment Σ mode/n → −Λ(m)/√φ(m).
- Centered polar terms ≤ 6m√φ(m)G. Bound: |jointTopCoefficient(Ramanujan m, 1)| ≤ K·m(√φ(m) + V_m)G(1 + log N), V_m = jet amplitude, uniformly 1 ≤ c ≤ N/4.

## TopBand/RamanujanPackets
- Horizon coefficient, shell row, shellTopCoefficient, jointTopCoefficient are bilinear (linear in base and in partner). Two-mode expansion: J(αa + βb, αa + βb) − α²J(a,a) = αβ(J(a,b) + J(b,a)) + β²J(b,b) (both mixed orientations retained).
- On span{1, mode_m} (m ≥ 2): |J(α + β mode, α + β mode) − α²J(1,1)| ≤ K·m(|αβ|(2√φ(m) + V_m) + β²φ(m))G(1 + log N), uniformly 1 ≤ c ≤ N/4 (polar–polar entry removed; remainder logarithmic).

## Conductor/DivisorJetGroundState
- Divisor chains: Σ_{m|M}Σ_{k|m} f(k)Λ(m/k) = Σ_{k|M} f(k) log(M/k) (Λ * ζ = log). Incoming charge Σ_{k|m}Λ(m/k)φ(k) = φ(m)·tameDifferent(m).
- divisorJetEnergy(M, f) = Σ_{m|M}Σ_{k|m} Λ(m/k)φ(k)(f(m) − f(k))² ≥ 0 = Σ_m φ(m)(log(M/m) + tameDiff(m))f(m)² − 2Σ Λ(m/k)φ(k)f(m)f(k). Zero ⇔ f constant on divisors of M (prime-edge connectivity).
- Packet pairing over period M: Σ_n RamanujanPacket·JetPacket = M(Σ φ(m)log m f(m)² + Σ Λ(m/k)φ(k)f(m)f(k)). Hence energy = Σ φ(m)(log M + log m + tameDiff(m))f(m)² − (2/M)·(actual period pairing). Zero-energy packet = f(1)·M·[M | n] (integer divisibility comb).

## Conductor/RamanujanJetAdjunctionGap (uses ArithmeticPositiveDuality TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor)
- Power deformation R_m(n, s) = Σ_{d|m, d|n} μ(m/d)d^s: = μ(m/g)g^s ∏_{p|g}(p ∤ q ? 1 − p^{−s} : 1), g = gcd(m,n), q = m/g (Möbius reindexing; no squarefree restriction). At n = 0: m^s∏_{p|m}(1 − p^{−s}) (Jordan totient). Quotient identity R_m(n,s)·R_q(0,s) = μ(q)R_m(0,s) (holds even at zeros).
- R_m(n, 1) = c_m(n); ∂_s at 1 = J_m(n). Hence J_m(n) = c_m(n)·[(log m + tameDiff m) − (log q + tameDiff q)]: every divisor jet is its Ramanujan coefficient times an adjunction-energy gap.

## Conductor/DivisorJetReciprocity
- Complementary lags have equal reduced modulus: d/gcd(d, M/k) = k/gcd(k, M/d). Reciprocity φ(k)c_d(M/k) = φ(d)c_k(M/d); antisymmetric jet pairing φ(k)J_d(M/k) − φ(d)J_k(M/d) = (adj(d) − adj(k))φ(k)c_d(M/k), adj = log + tameDiff.
- Period gcd classes weighted by φ(M/d); c_d constant on gcd classes. Divisor-lattice orthogonality Σ_r φ(r)c_d(M/r)c_k(M/r) = [d = k]Mφ(k). Reciprocal transform squares to M: Σ_r c_d(M/r)c_r(M/k) = [d = k]M. Every divisor profile has exact finite reciprocal Ramanujan expansion.

## Conductor/DivisorJetSpectrum (uses RHTower CausallyAnchoredFutureAliasRegrouping)
- Graph generator (both edge directions): reciprocal Ramanujan mode a ↦ c_d(M/a) is an exact eigenvector with eigenvalue φ(k)(log d + tameDiff d) at vertex k. Energy = Σ_k f(k)·generator(f)(k).
- Adjunction spectrum: divisorJetEnergy(M, f) = (1/M)Σ_{d|M} φ(d)(log d + tameDiff d)·Packet(f)(M/d)², all valuation boundaries retained. Integer-period form: = (1/M)Σ_{n<M}(log(M/gcd) + tameDiff(M/gcd))·Packet(f)(n)² (reduced-lag adjunction symbol).

## Conductor/RamanujanAutocorrelationWeights
- Ramanujan lag Gram Σ_{i,j} a_i a_j c_k(|i−j|) = Σ_{primitive k-th roots z}|Σ a_i z^i|² ≥ 0 (signed sources). ramanujanAutocorrelationWeight = that / φ(k) ≥ 0.
- Shifted orthogonality Σ_{n<M} c_k(n+i)c_l(n+j) = [k = l]M c_k(|i−j|). Weight = (1/(kφ(k)))Σ_{n<k}(Σ a_i c_k(n+i))² (period square mass of smoothed mode). Smoothed Ramanujan Gram stays diagonal: Σ_n smooth(c_k)smooth(c_l) = [k = l]Mφ(l)·weight(l).

## Conductor/SmoothedDivisorJet
- weightedDivisorJetEnergy(M, b, f) = Σ_{m|M}Σ_{k|m} Λ(m/k)φ(k)b(k)(f(m) − f(k))² (weight on lower conductor). Packet projection Σ_{n<M} Packet(f)(n)c_k(n) = Mφ(k)f(k).
- Bilinear pairing keeps edge orientation: Σ_n Packet(g)·JetPacket(f) = M(Σ φ(m)log m g(m)f(m) + Σ Λ(m/k)φ(k)f(m)g(k)).
- Weighted square completion: energy = Σ_m(φ(m)b(m)log(M/m) + Σ_{k|m}Λ(m/k)φ(k)b(k))f(m)² − 2Σ Λφ b f f = Σ_m(φ(m)b(m)(log M + log m) + incoming)f(m)² − (2/M)Σ_n Packet(b·f)·JetPacket(f).
- Source smoothing of both packets = weighting packet by autocorrelation weights: Σ_n smooth(Packet f)·smooth(JetPacket f) = Σ_n Packet(w·f)·JetPacket(f). With b = autocorrelation weight, energy ≥ 0 and equals diagonal − (2/M)·(literal smoothed packet–jet pairing).
- Incoming smoothing charge Σ_{k|m}Λ(m/k)φ(k)w(k) = Σ_{i,j}a_i a_j c_m(|i−j|)(tameDiff m − (log q_{ij} + tameDiff q_{ij})), q_{ij} = m/gcd(m,|i−j|). Hence the reduced-lag adjunction deficit kernel is PSD on every finite signed source.

## Conductor/ProfiledAdjunctionLagKernel (uses BiScaleUncertainty MultiplicativeChainBesselAndOriginLeverage)
- Profile weight (continuous compactly supported φ, arbitrary real shifts θ): ramanujanProfileWeight = Σ x_i x_j c_k(|i−j|)autocorr φ(θ_j − θ_i)/φ(k) = ∫ autocorrelation weight of translated source ≥ 0.
- Incoming charge = profile Gram of adjunction lag kernel; PSD with actual profile autocorrelation; includes exact logarithmic mesh θ_i = log i / w (no uniform-lattice approximation). Weighted divisor energy with profile weights ≥ 0.
